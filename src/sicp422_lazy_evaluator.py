'''
lazy evaluation interpreter can delay evaluating expression to when needed
this results in normal-order, or non-strict evaluation

inspired by exercide 4.31, we use explicity lazy evaluation
but our syntax is (lazy expr), where "lazy" is put at list front
our lazy is just another list syntax like quote
it can be anywhere in code, not restricted to proceudre parameter
out lazy also automatically memoize the value once evaluated

since the default evaluation is still eager, not lazy, we can reuse previous evaluator
we will use the resolved evaluator, and the resolution rules are almost unchanged
we will not analyze the expression tree to create evaluate function, since that's difficult to debug

our lazy value is implemented via ThunkVal
in following scenarios, ThunkVal will be forced:
body result, operator, if-predicate, primitive procedure operands, sequence (except last expression)

we will have to create an environment for lazy, this is a trick to avoid failure of current resolution
for example, without creating environment, the following code will throw "local symbol used before initialization"
(define (f)
  (define a (lazy (+ b 1)))
  (define b 1)
  a)
(f)
other solutions exist though, but are more complex, for example:
let proc add environment of distance 1, lazy add environment of distance 0
we will not do that
'''

from typing import List, Optional
from sicp414_evaluator import AndExpr, SequenceExpr, BooleanVal, CallExpr, Environment, EvalRecurFuncType, Expression, \
    IfExpr, NilVal, NotExpr, OrExpr, PrimVal, ProcPlainVal, SchemePanic, SchemeParserError, SchemeRuntimeError, SchemeVal, SequenceExpr, \
    Token, TokenList, TokenTag, UndefVal, env_extend, install_is_equal_rules, install_parse_expr_rules, install_primitives, install_stringify_expr_rules, \
    install_stringify_value_rules, is_truthy, make_global_env, parse_expr, parse_expr_recursive, parse_sub_symbol_token, parse_tokens, pure_check_proc_arity, pure_eval_call_invalid, \
    pure_eval_call_prim, pure_eval_call_proc_extend_env, scan_source, scheme_flush, stringify_expr, stringify_expr_rule_decorator, stringify_value, update_parse_expr_rules, update_stringify_expr_rules
from sicp416_resolver import ResBindingsType, ResRecurFuncType, ResStackType, install_resolved_eval_rules, install_resolver_rules, resolve_expr, \
    resolved_eval_rule_decorator, resolved_eval_rule_decorator, resolved_evaluate_expr, resolver_rule_decorator, \
    update_resolved_eval_rules, update_resolver_rules


class LazyExpr(Expression):
    def __init__(self, keyword: Token, content: Expression):
        self.keyword = keyword
        self.content = content


def parse_list_lazy(combo: TokenList):
    '''parse lazy from list expression'''
    if len(combo.contents) != 2:
        raise SchemeParserError(
            combo.anchor, 'lazy should have 2 expressions, now %d' % len(combo.contents))
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    content = parse_expr_recursive(combo.contents[1])
    return LazyExpr(keyword, content)


def install_parse_expr_lazy_rules():
    rules = {'lazy': parse_list_lazy}
    update_parse_expr_rules(rules)


@stringify_expr_rule_decorator
def stringify_expr_lazy(expr: LazyExpr):
    substrs = ['lazy', stringify_expr(expr.content)]
    return '(%s)' % (' '.join(substrs))


def install_stringify_expr_lazy_rules():
    rules = {LazyExpr: stringify_expr_lazy}
    update_stringify_expr_rules(rules)


class ThunkVal(SchemeVal):
    '''
    created dynamically by lazy
    will not be checked for equality or stringified, because both will trigger forcing
    therefore no need to modify ValueStringifier and EqualityChecker
    '''

    def __init__(self, expr: Expression, env: Environment):
        self.expr = expr
        self.env = env
        self.value: Optional[SchemeVal] = None  # for memoization


def force(sv: SchemeVal, evl: EvalRecurFuncType) -> SchemeVal:
    if isinstance(sv, ThunkVal):
        if sv.value is None:
            actual_value = evl(sv.expr, sv.env)
            sv.value = force(actual_value, evl)
        return sv.value
    else:
        return sv


@resolver_rule_decorator
def resolve_lazy(expr: LazyExpr, phase: bool, resolve: ResRecurFuncType, stack: ResStackType, bindings: ResBindingsType):
    '''extending resolver rule to support lazy, lazy creates its own environmnent'''
    stack.append(expr)
    if not phase:  # create local scope only in phase 1
        bindings[expr] = {}
    resolve(expr.content, phase)
    stack.pop()


def install_resolver_lazy_rules():
    rules = {LazyExpr: resolve_lazy}
    update_resolver_rules(rules)


'''extending resolver evaluator rules to support lazy'''


@resolved_eval_rule_decorator
def lazy_resolved_eval_lazy(expr: LazyExpr, env: Environment):
    new_env = env_extend(env, [], [])
    return ThunkVal(expr.content, new_env)


@resolved_eval_rule_decorator
def lazy_resolved_eval_sequence(expr: SequenceExpr, env: Environment, evl: EvalRecurFuncType):
    '''notice begin and root have different behavior, regarding to whether the last subexpr should be forced'''
    res: SchemeVal = NilVal()
    for i in range(len(expr.contents)):
        res = evl(expr.contents[i], env)
        # force it if not last, or is root
        if i != len(expr.contents) - 1 or expr.keyword.tag == TokenTag.ROOT:
            res = force(res, evl)
    return res


def pure_lazy_resolved_eval_call_proc_plain(paren: Token, operator: ProcPlainVal, operands: List[SchemeVal], evl: EvalRecurFuncType):
    pure_check_proc_arity(paren, operator, operands)
    new_env = pure_eval_call_proc_extend_env(operator, operands)
    # only change
    return evl(operator.body, new_env)


@resolved_eval_rule_decorator
def lazy_resolved_eval_call(expr: CallExpr, env: Environment, evl: EvalRecurFuncType):
    operator = evl(expr.operator, env)
    operands = [evl(subexpr, env) for subexpr in expr.operands]
    operator_forced = force(operator, evl)
    if isinstance(operator_forced, PrimVal):
        operands_forced = [force(op, evl) for op in operands]
        return pure_eval_call_prim(expr.paren, operator_forced, operands_forced)
    elif isinstance(operator_forced, ProcPlainVal):
        return pure_lazy_resolved_eval_call_proc_plain(expr.paren, operator_forced, operands, evl)
    else:
        return pure_eval_call_invalid(expr.paren, operator_forced)


@resolved_eval_rule_decorator
def lazy_resolved_eval_if(expr: IfExpr, env: Environment, evl: EvalRecurFuncType):
    pred = evl(expr.pred, env)
    pred_forced = force(pred, evl)  # only change
    if is_truthy(pred_forced):
        return evl(expr.then_branch, env)
    elif expr.else_branch is not None:
        return evl(expr.else_branch, env)
    else:
        return UndefVal()


@resolved_eval_rule_decorator
def lazy_resolved_eval_and(expr: AndExpr, env: Environment, evl: EvalRecurFuncType):
    for subexpr in expr.contents:
        res = evl(subexpr, env)
        res = force(res, evl)  # only change
        if not is_truthy(res):
            return res
    return res


@resolved_eval_rule_decorator
def lazy_resolved_eval_or(expr: OrExpr, env: Environment, evl: EvalRecurFuncType):
    for subexpr in expr.contents:
        res = evl(subexpr, env)
        res = force(res, evl)  # only change
        if is_truthy(res):
            return res
    return res


@resolved_eval_rule_decorator
def lazy_resolved_eval_not(expr: NotExpr, env: Environment, evl: EvalRecurFuncType):
    res = evl(expr.content, env)
    res = force(res, evl)  # only change
    return BooleanVal(False) if is_truthy(res) else BooleanVal(True)


def install_resolved_eval_lazy_rules():
    '''
    we assume install_resolved_eval_rules() is called beforehand
    so that we can overwrite those rules
    '''
    rules = {
        LazyExpr: lazy_resolved_eval_lazy,
        SequenceExpr: lazy_resolved_eval_sequence,
        CallExpr: lazy_resolved_eval_call,
        IfExpr: lazy_resolved_eval_if,
        AndExpr: lazy_resolved_eval_and,
        OrExpr: lazy_resolved_eval_or,
        NotExpr: lazy_resolved_eval_not
    }
    update_resolved_eval_rules(rules)


def install_rules():
    install_parse_expr_rules()
    install_stringify_expr_rules()
    install_stringify_value_rules()
    install_is_equal_rules()
    install_resolver_rules()
    install_resolved_eval_rules()
    install_primitives()
    # lazy rules
    install_parse_expr_lazy_rules()
    install_stringify_expr_lazy_rules()
    install_resolver_lazy_rules()
    install_resolved_eval_lazy_rules()


def test_one(source: str, **kargs: str):
    '''
    each test tries to execute the source code as much as possible
    capture the output, panic and result
    print them and compare to expected value
    '''

    # source
    source = source.strip()
    print('* source: %s' % source)
    try:
        # scan
        tokens = scan_source(source)

        # parse
        combos = parse_tokens(tokens)
        expr = parse_expr(combos)

        # resolve
        distances = resolve_expr(expr)

        # evaluate
        glbenv = make_global_env()
        result = resolved_evaluate_expr(expr, glbenv, distances)
        result_str = stringify_value(result)
        output_str = scheme_flush()
        if len(output_str):
            print('* output: %s' % output_str)
        if 'output' in kargs:
            assert output_str == kargs['output']
        print('* result: %s' % result_str)
        if 'result' in kargs:
            assert result_str == kargs['result']
    except SchemePanic as err:
        print('* panic: %s' % err.message)
        assert err.message == kargs['panic']

    print('----------')


def test_non_lazy():
    # if
    test_one(
        '''
        (define x (if #t 1 2))
        (if (= x 1) (display "a"))
        (if (= x 2) (display "b"))
        ''',
        output='a',
        result='#<undef>'
    )
    # single recursion
    test_one(
        '''
        (define (run)
          (define (factorial n)
            (if (= n 1)
              1
              (* n (factorial (- n 1)))))
          (factorial 5))
        (run)
        ''',
        resolve='(3:= 2) (3:n 0) (5:* 2) (5:n 0) (5:factorial 1) (5:- 2) (5:n 0) (6:factorial 0) (7:run 0)',
        result='120'
    )
    # mutual recursion
    test_one(
        '''
        (define (f)
          (define (even n) (if (= n 0) #t (odd (- n 1))))
          (define (odd n) (if (= n 0) #f (even (- n 1))))
          (even 5))
        (f)
        ''',
        result='#f'
    )


def test_lazy():
    # double lazy result
    test_one(
        '''
      (lazy (lazy (+ 1 2)))
      ''',
        result='3'
    )
    # skip lazy invalid
    test_one(
        '''
      (define (f pd th el)
        (if pd th el))
      (f #t 1 (lazy (/ 0 0)))
      ''',
        result='1'
    )
    # sequence will be forced, except last
    test_one(
        '''
      (lazy (display "a"))
      (lazy (display "b"))
      (lazy (display "c"))
      ''',
        output='abc',
        result='#<undef>'
    )
    # memoization
    test_one(
        '''
      (define (f x) (+ x x))
      (f (lazy (begin (display "a") 1)))
      ''',
        output='a',
        result='2'
    )
    # lazy creates its own environment
    test_one(
        '''
      (define (f)
        (define a (lazy (+ b 1)))
        (define b 1)
        a)
      (f)
      ''',
        result='2'
    )


def test():
    test_non_lazy()
    test_lazy()


if __name__ == '__main__':
    install_rules()
    test()

import sys
import inspect
from typing import Any, Callable, Dict, List, Optional, Type, Union
from sicp331_cycle_detect import LinkedListNode
from sicp414_evaluator import AndExpr, BooleanExpr, BooleanVal, CallExpr, DefineProcExpr, DefineVarExpr, \
    Environment, Expression, GenericExpr, IfExpr, LambdaExpr, NilExpr, NilVal, NotExpr, NumberExpr, OrExpr, \
    PairVal, PrimVal, ProcPlainVal, QuoteExpr, SchemePanic, SchemeParserError, SchemeRuntimeError, \
    SchemeVal, SequenceExpr, SetExpr, StringExpr, SymbolExpr, Token, TokenList, UndefVal, find_type, \
    install_is_equal_rules, install_parse_expr_rules, install_primitives, install_stringify_expr_rules, \
    install_stringify_value_rules, is_truthy, make_global_env, pair_from_list_val, parse_expr, parse_expr_recursive, parse_sub_symbol_token, parse_tokens, \
    pure_check_proc_arity, pure_eval_boolean, pure_eval_call_invalid, pure_eval_call_prim, pure_eval_call_proc_extend_env, pure_eval_define_proc_plain_value, \
    pure_eval_define_var, pure_eval_lambda_plain, pure_eval_nil, pure_eval_number, pure_eval_string, quote_token_combo, scan_source, scheme_flush, \
    scheme_panic, stringify_expr, stringify_expr_rule_decorator, stringify_value, update_parse_expr_rules, update_stringify_expr_rules
from sicp416_resolver import ResDistancesType, ResRecurFuncType, env_lookup_at, env_set_at, install_resolver_rules, pure_resolved_eval_set, \
    pure_resolved_eval_symbol, resolve_expr, resolver_rule_decorator, update_resolver_rules


class AmbExpr(Expression):
    def __init__(self, keyword: Token, contents: List[Expression]):
        self.keyword = keyword
        self.contents = contents


def parse_list_amb(combo: TokenList):
    '''parse amb from list expression'''
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    contents = [parse_expr_recursive(subexpr)
                for subexpr in combo.contents[1:]]
    return AmbExpr(keyword, contents)


def parse_list_require(combo: TokenList):
    '''
    parse require from list expression
    (require pred) is then desugared to (if not(pred) (amb))
    '''
    if len(combo.contents) != 2:
        raise SchemeParserError(
            combo.anchor, 'require should have 2 expressions, now %d' % len(combo.contents))
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    return IfExpr(keyword, NotExpr(keyword, parse_expr_recursive(combo.contents[1])), AmbExpr(keyword, []), None)


def install_parse_expr_amb_rules():
    rules = {
        'amb': parse_list_amb,
        'require': parse_list_require
    }
    update_parse_expr_rules(rules)


@stringify_expr_rule_decorator
def stringify_expr_amb(expr: AmbExpr):
    substrs = [stringify_expr(subexpr) for subexpr in expr.contents]
    substrs = ['amb', *substrs]
    return '(%s)' % (' '.join(substrs))


def install_stringify_expr_amb_rules():
    rules = {AmbExpr: stringify_expr_amb}
    update_stringify_expr_rules(rules)


@resolver_rule_decorator
def resolve_amb(expr: AmbExpr, phase: bool, resolve: ResRecurFuncType):
    '''extending resolver rule to support amb, just resolve its contents one by one'''
    for subexpr in expr.contents:
        resolve(subexpr, phase)


def install_resolver_amb_rules():
    rules = {AmbExpr: resolve_amb}
    update_resolver_rules(rules)


'''
amb evaluator
we build it from resolved evaluator, it does not support lazy evaluation

evaluated value is passed to succeed callback function, not directly returned
the succeed function nested later expressions inside early expressions, creating very deep call stack frames
this limits the total number of expressions, thus limiting the size of the problem
this is unfortunately, and is due to the fact that we use python call stack frame to implement amb expression chain
we may need to explicitly model the amb expression chain, such as using bytecode to avoid this problem, but I won't do it

also notice we use exception to replace the fail callback function
this is because exception help us avoid simply passing down fail function, and differentiating fail and fail_after
besides, it can jump back multiple steps on the call stack frames
therefore I feel exception based backtrace is more elegantly
'''

AmbEvalSuceedFuncType = Callable[[SchemeVal], None]
AmbEvalRecurFuncType = Callable[[Expression,
                                 Environment, AmbEvalSuceedFuncType], None]
AmbEvalFuncType = Callable[[Expression, Environment,
                            AmbEvalSuceedFuncType, AmbEvalRecurFuncType, ResDistancesType], None]

_amb_eval_rules: Dict[Type, AmbEvalFuncType] = {}


class AmbEvalFailure(Exception):
    '''this exception replaces failure callback'''
    pass


def update_amb_eval_rules(rules: Dict[Type, AmbEvalFuncType]):
    _amb_eval_rules.update(rules)


def clone_value(sv: SchemeVal):
    '''
    this is to ensure the result returned by amb evaluator won't be mutated by the next round of trial
    currently only PairVal has the potential to be mutated, so we only need to clone it
    although ThunkVal.value may also be mutated, we do not support lazy evaluation here, so we ignore it
    '''
    if isinstance(sv, PairVal):
        return PairVal(clone_value(sv.left), clone_value(sv.right))
    else:
        return sv


def amb_evaluate_expr(expr: SequenceExpr, env: Environment, distances: ResDistancesType, limit: int):
    '''
    instead of interactively try-again to get next values
    we specify limit, so that we get at most limit values at once

    _succeed_root is the root level succeed callback, it retries next until limit is reached
    it is specified at root level, but will be passed down to the deepest level
    we use AmbEvalFailure to replace failure callback
    '''
    def _amb_evaluate_recursive(expr: Expression, env: Environment, succeed: AmbEvalSuceedFuncType) -> None:
        t = find_type(type(expr), _amb_eval_rules)
        f = _amb_eval_rules[t]
        return f(expr, env, succeed, _amb_evaluate_recursive, distances)

    results: List[SchemeVal] = []

    def _succeed_root(result: SchemeVal):
        results.append(clone_value(result))

        nonlocal limit
        limit -= 1
        if limit > 0:
            '''
            fake a failure to let it retry
            although this failure is specified at root level
            it is executed at the deepest level

            exception does not bubble up environment chain
            instead it bubbles up call stack frames
            '''
            raise AmbEvalFailure()

    try:
        _amb_evaluate_recursive(expr, env, _succeed_root)
    except SchemeRuntimeError as err:
        scheme_panic(str(err))
    except AmbEvalFailure:
        pass  # result exhausted

    return pair_from_list_val(results, NilVal())


'''
amb evaluator rule definitions
'''

AmbEvalRuleType = Union[
    Callable[[], None],
    Callable[[GenericExpr], None],
    Callable[[GenericExpr, Environment], None],
    Callable[[GenericExpr, Environment, AmbEvalSuceedFuncType], None],
    Callable[[GenericExpr, Environment,
              AmbEvalSuceedFuncType, AmbEvalRecurFuncType], None],
    Callable[[GenericExpr, Environment, AmbEvalSuceedFuncType,
              AmbEvalRecurFuncType, ResDistancesType], None]
]


def amb_eval_rule_decorator(rule_func: AmbEvalRuleType):
    arity = len(inspect.getfullargspec(rule_func).args)

    def _amb_eval_rule_wrapped(expr: Expression, env: Environment, succeed: AmbEvalSuceedFuncType,
                               amb_eval: AmbEvalRecurFuncType, distances: ResDistancesType):
        args: List[Any] = [expr, env, succeed, amb_eval, distances]
        return rule_func(*args[0:arity])
    return _amb_eval_rule_wrapped


def pure_amb_eval_linked_list(expressions: Optional[LinkedListNode[Expression]], env: Environment,
                              succeed_linked_list: Callable[[Optional[LinkedListNode[SchemeVal]]], None],
                              amb_eval: AmbEvalRecurFuncType, stop: Optional[bool]):
    '''
    accept a linked list of expressions, ambeval them, then in the callback succeed_linked_list pass a linked list of result
    to ambeval all expressions, we first ambeval the first, then ambeval the rest recursively

    in phase one, we purely evaluate expressions in order:
    first expression, then second, ..., finally last expression
    the results are stored in call stack frames
    failure can only happen in this phase 

    in phase two, we build the result linked list in reverse order via succeed callback:
    first build a linked list only of the last result, then prepend the second-but-last, ..., finally prepend the first result
    the _succeed_linked_list_rest continuation function is called at the very end together, quickly collecting results from call stack frames
    linked list is much more efficient in this phase, that's why we use linked list instead of list
    '''
    if expressions is None:
        succeed_linked_list(None)
    else:
        def _pure_amb_eval_linked_list_rest(result: SchemeVal):
            def _succeed_linked_list_rest(results_rest: Optional[LinkedListNode[SchemeVal]]):
                succeed_linked_list(LinkedListNode(result, results_rest))

            if (stop is True and is_truthy(result)) or (stop is False and (not is_truthy(result))):
                # early stop, useful for AndExpr and OrExpr
                succeed_linked_list(LinkedListNode(result, None))
            else:  # finish all, useful for SequenceExpr and CallExpr.operands
                # typing should discover this, but unfortunately it doesn't
                assert expressions is not None
                pure_amb_eval_linked_list(
                    expressions.next, env, _succeed_linked_list_rest, amb_eval, stop)
        amb_eval(expressions.data, env, _pure_amb_eval_linked_list_rest)


def pure_amb_eval_list(expressions: List[Expression], env: Environment, succeed_list: Callable[[List[SchemeVal]], None],
                       amb_eval: AmbEvalRecurFuncType, stop: Optional[bool]):
    '''we provide an interface with pure list, since this is more convenient than linked list'''
    def _succeed_linked_list(results: Optional[LinkedListNode[SchemeVal]]):
        succeed_list(LinkedListNode.to_list(results))
    pure_amb_eval_linked_list(LinkedListNode.from_list(
        expressions), env, _succeed_linked_list, amb_eval, stop)


@amb_eval_rule_decorator
def amb_eval_sequence(expr: SequenceExpr, env: Environment, succeed: AmbEvalSuceedFuncType, amb_eval: AmbEvalRecurFuncType):
    def _succeed_list(results: List[SchemeVal]):
        '''we only need the last result'''
        result = results[-1] if len(results) else UndefVal()
        succeed(result)
    pure_amb_eval_list(expr.contents, env, _succeed_list, amb_eval, None)


@amb_eval_rule_decorator
def amb_eval_symbol(expr: SymbolExpr, env: Environment, succeed: AmbEvalSuceedFuncType,
                    amb_eval: AmbEvalRecurFuncType, distances: ResDistancesType):
    succeed(pure_resolved_eval_symbol(expr, env, distances))


@amb_eval_rule_decorator
def amb_eval_string(expr: StringExpr, env: Environment, succeed: AmbEvalSuceedFuncType):
    succeed(pure_eval_string(expr))


@amb_eval_rule_decorator
def amb_eval_number(expr: NumberExpr, env: Environment, succeed: AmbEvalSuceedFuncType):
    succeed(pure_eval_number(expr))


@amb_eval_rule_decorator
def amb_eval_boolean(expr: BooleanExpr, env: Environment, succeed: AmbEvalSuceedFuncType):
    succeed(pure_eval_boolean(expr))


@amb_eval_rule_decorator
def amb_eval_nil(expr: NilExpr, env: Environment, succeed: AmbEvalSuceedFuncType):
    succeed(pure_eval_nil())


@amb_eval_rule_decorator
def amb_eval_quote(expr: QuoteExpr, env: Environment, succeed: AmbEvalSuceedFuncType):
    succeed(quote_token_combo(expr.content))


@amb_eval_rule_decorator
def amb_eval_call(expr: CallExpr, env: Environment, succeed: AmbEvalSuceedFuncType, amb_eval: AmbEvalRecurFuncType):
    '''first calculate operator, then operands, finally body'''
    def _succeed_operator(operator: SchemeVal):
        def _succeed_operands(operands: List[SchemeVal]):
            if isinstance(operator, PrimVal):
                succeed(pure_eval_call_prim(expr.paren, operator, operands))
            elif isinstance(operator, ProcPlainVal):
                pure_check_proc_arity(expr.paren, operator, operands)
                new_env = pure_eval_call_proc_extend_env(operator, operands)
                amb_eval(operator.body, new_env, succeed)
            else:
                succeed(pure_eval_call_invalid(expr.paren, operator))
        pure_amb_eval_list(expr.operands, env,
                           _succeed_operands, amb_eval, None)
    amb_eval(expr.operator, env, _succeed_operator)


@amb_eval_rule_decorator
def amb_eval_set(expr: SetExpr, env: Environment, succeed: AmbEvalSuceedFuncType,
                 amb_eval: AmbEvalRecurFuncType, distances: ResDistancesType):
    def _succeed_initializer(initializer: SchemeVal):
        old_value = env_lookup_at(env, distances[expr], expr.name.literal)
        try:
            succeed(pure_resolved_eval_set(expr, initializer, env, distances))
        except AmbEvalFailure:
            '''
            undo sideeffect: revert to old_value
            then raise failure to upper level
            '''
            env_set_at(env, distances[expr], expr.name.literal, old_value)
            raise AmbEvalFailure()
    amb_eval(expr.initializer, env, _succeed_initializer)


@amb_eval_rule_decorator
def amb_eval_define_var(expr: DefineVarExpr, env: Environment, succeed: AmbEvalSuceedFuncType, amb_eval: AmbEvalRecurFuncType):
    def _succeed_initializer(initializer: SchemeVal):
        succeed(pure_eval_define_var(expr.name, initializer, env))
    amb_eval(expr.initializer, env, _succeed_initializer)


@amb_eval_rule_decorator
def amb_eval_define_proc(expr: DefineProcExpr, env: Environment, succeed: AmbEvalSuceedFuncType):
    proc_obj = pure_eval_define_proc_plain_value(expr.name.literal, expr.pos_paras, expr.rest_para, expr.body, env)
    succeed(pure_eval_define_var(expr.name, proc_obj, env))


@amb_eval_rule_decorator
def amb_eval_if(expr: IfExpr, env: Environment, succeed: AmbEvalSuceedFuncType, amb_eval: AmbEvalRecurFuncType):
    def _succeed_pred(pred_val: SchemeVal):
        if is_truthy(pred_val):
            amb_eval(expr.then_branch, env, succeed)
        elif expr.else_branch is not None:
            amb_eval(expr.else_branch, env, succeed)
        else:
            succeed(UndefVal())
    amb_eval(expr.pred, env, _succeed_pred)


@amb_eval_rule_decorator
def amb_eval_lambda(expr: LambdaExpr, env: Environment, succeed: AmbEvalSuceedFuncType):
    succeed(pure_eval_lambda_plain(expr, env))


@amb_eval_rule_decorator
def amb_eval_and(expr: AndExpr, env: Environment, succeed: AmbEvalSuceedFuncType, amb_eval: AmbEvalRecurFuncType):
    def _succeed_contents(contents: List[SchemeVal]):
        succeed(contents[-1])
    pure_amb_eval_list(expr.contents, env, _succeed_contents,
                       amb_eval, False)  # try each one until not truthy


@amb_eval_rule_decorator
def amb_eval_or(expr: OrExpr, env: Environment, succeed: AmbEvalSuceedFuncType, amb_eval: AmbEvalRecurFuncType):
    def _succeed_contents(contents: List[SchemeVal]):
        succeed(contents[-1])
    pure_amb_eval_list(expr.contents, env, _succeed_contents,
                       amb_eval, True)  # try each one until truthy


@amb_eval_rule_decorator
def amb_eval_not(expr: NotExpr, env: Environment, succeed: AmbEvalSuceedFuncType, amb_eval: AmbEvalRecurFuncType):
    def _succeed_content(content: SchemeVal):
        succeed(BooleanVal(not is_truthy(content)))
    amb_eval(expr.content, env, _succeed_content)


@amb_eval_rule_decorator
def amb_eval_amb(expr: AmbExpr, env: Environment, succeed: AmbEvalSuceedFuncType, amb_eval: AmbEvalRecurFuncType):
    n = len(expr.contents)

    def _try_next(i: int):
        if i == n:
            raise AmbEvalFailure()  # in case of candidate exhaustion
        else:
            def _succeed_at(result: SchemeVal):
                try:
                    succeed(result)
                except AmbEvalFailure:
                    _try_next(i+1)  # in case of failure afterwards
            amb_eval(expr.contents[i], env, _succeed_at)

    _try_next(0)


def install_amb_eval_rules():
    rules = {
        SequenceExpr: amb_eval_sequence,
        SymbolExpr: amb_eval_symbol,
        StringExpr: amb_eval_string,
        NumberExpr: amb_eval_number,
        BooleanExpr: amb_eval_boolean,
        NilExpr: amb_eval_nil,
        QuoteExpr: amb_eval_quote,
        CallExpr: amb_eval_call,
        SetExpr: amb_eval_set,
        DefineVarExpr: amb_eval_define_var,
        DefineProcExpr: amb_eval_define_proc,
        LambdaExpr: amb_eval_lambda,
        IfExpr: amb_eval_if,
        AndExpr: amb_eval_and,
        OrExpr: amb_eval_or,
        NotExpr: amb_eval_not,
        AmbExpr: amb_eval_amb
    }
    update_amb_eval_rules(rules)


def install_rules():
    install_parse_expr_rules()
    install_stringify_expr_rules()
    install_stringify_value_rules()
    install_is_equal_rules()
    install_resolver_rules()
    install_primitives()
    # amb rules
    install_parse_expr_amb_rules()
    install_stringify_expr_amb_rules()
    install_resolver_amb_rules()
    install_amb_eval_rules()


'''test begins'''


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
        result = amb_evaluate_expr(expr, glbenv, distances, 3)
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


def test_non_amb():
    # if
    test_one(
        '''
        (define x (if #t 1 2))
        (if (= x 1) (display "a"))
        (if (= x 2) (display "b"))
        ''',
        output='a',
        result='(#<undef>)'
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
        result='(120)'
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
        result='(#f)'
    )


def test_amb():
    # simple pair
    test_one(
        '''
        (define a (amb 1 2 ))
        (define b (amb 3 4))
        (list a b)
        ''',
        result='((1 3) (1 4) (2 3))'
    )
    # require
    test_one(
        '''
        (define a (amb 1 2 ))
        (define b (amb 3 4))
        (require (> (+ a b) 4))
        (list a b)
        ''',
        result='((1 4) (2 3) (2 4))'
    )


def test_logic_puzzle():
    test_one(
        '''
        (define (abs x)
          (if (< x 0) (- 0 x) x))
        (define (multiple-dwelling)
          (define baker (amb 1 2 3 4 5))
          (require (not (= baker 5)))

          (define cooper (amb 1 2 3 4 5))
          (require (not (= cooper 1)))
          (require (not (= cooper baker)))

          (define fletcher (amb 1 2 3 4 5))
          (require (not (= fletcher 1)))
          (require (not (= fletcher 5)))
          (require (not (= fletcher baker)))
          (require (not (= fletcher cooper)))
          (require (not (= (abs (- fletcher cooper)) 1)))

          (define miller (amb 1 2 3 4 5))
          (require (not (= miller baker)))
          (require (not (= miller cooper)))
          (require (not (= miller fletcher)))
          (require (> miller cooper))

          (define smith (amb 1 2 3 4 5))
          (require (not (= smith baker)))
          (require (not (= smith cooper)))
          (require (not (= smith fletcher)))
          (require (not (= smith miller)))
          (require (not (= (abs (- smith fletcher)) 1)))

          (list baker cooper fletcher miller smith))
        (multiple-dwelling)
        ''',
        result='((3 2 4 5 1))'
    )


def test_parsing_nlp():
    shared_lib = '''
      (define nouns '(n student professor cat class))
      (define verbs '(v studies lectures eats sleeps))
      (define articles '(a the a))
      (define prepositions '(p for to in by with))

      (define (memq x ls)
        (if (not (pair? ls)) #f
          (or (equal? x (car ls))
              (memq x (cdr ls)))))

      (define (parse-sentence words)
        (define cursor words)

        (define (parse-word dict)
          (require (pair? cursor))
          (require (memq (car cursor) (cdr dict)))
          (define found (car cursor))
          (set! cursor (cdr cursor))
          found)

        (define (parse-simple-noun-phrase)
          (list (parse-word articles) (parse-word nouns)))

        (define (parse-prepositional-phrase)
          (list (parse-word prepositions) (parse-noun-phrase)))

        (define (parse-noun-phrase)
          (define (maybe-extend noun-phrase)
            (amb noun-phrase
              (maybe-extend
                (list noun-phrase (parse-prepositional-phrase)))))
          (maybe-extend (parse-simple-noun-phrase)))

        (define (parse-verb-phrase)
          (define (maybe-extend verb-phrase)
            (amb verb-phrase
              (maybe-extend
                (list verb-phrase (parse-prepositional-phrase)))))
          (maybe-extend (parse-word verbs)))

        (define result
          (list (parse-noun-phrase) (parse-verb-phrase)))
        (require (null? cursor))
        result
      )
    '''
    test_one(
        shared_lib +
        '''
        (parse-sentence '(the professor lectures to the student with the cat))
        ''',
        result='(((the professor) ((lectures (to (the student))) (with (the cat)))) ((the professor) (lectures (to ((the student) (with (the cat)))))))'
    )
    test_one(
        shared_lib +
        '''
        (parse-sentence '(the professor lectures to the student with the))
        ''',
        result='()'
    )


def test():
    test_non_amb()
    test_amb()
    test_logic_puzzle()
    test_parsing_nlp()


if __name__ == '__main__':
    install_rules()
    '''have to increase recursion limit to avoid "maximum recursion depth exceeded" error'''
    sys.setrecursionlimit(5000)
    test()

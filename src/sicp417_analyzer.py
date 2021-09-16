'''
analyzer turns expression into a self-evaluating function
potentially save the effort to parse expression every time it executes
in fact, it might not be that useful, since we have already parsed list expression
but it's fun, so let's implement it

anyway, I feel deeply nested functions harder to debug than deeply nested expression
so I do not recommend this step
'''


import inspect
from typing import Any, Callable, Dict, List, Optional, Type, Union

from sicp414_evaluator import AndExpr, SequenceExpr, BooleanExpr, BooleanVal, CallExpr, DefineProcExpr, DefineVarExpr, \
    Environment, Expression, GenericExpr, IfExpr, LambdaExpr, NilExpr, NilVal, NotExpr, NumberExpr, NumberVal, OrExpr, \
    PrimVal, ProcVal, QuoteExpr, SchemePanic, SchemeRuntimeError, SchemeVal, SequenceExpr, SetExpr, SymbolVal, UndefVal, \
    StringExpr, StringVal, SymbolExpr, Token, env_define, find_type, install_is_equal_rules, install_parse_expr_rules, install_primitives, \
    install_stringify_expr_rules, install_stringify_value_rules, is_truthy, make_global_env, parse_expr, parse_tokens, pure_check_proc_arity, \
    pure_eval_call_invalid, pure_eval_call_prim, pure_eval_call_proc_extend_env, pure_eval_define_var, quote_token_combo, \
    scan_source, scheme_flush, scheme_panic, stringify_token_full, stringify_value
from sicp416_resolver import ResDistancesType, install_resolver_rules, pure_resolved_eval_set, pure_resolved_eval_symbol, resolve_expr


class SchemeAnalysisError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self):
        return 'analysis error at %s in line %d: %s' % (stringify_token_full(self.token), self.token.line+1, self.message)


EvaluableType = Callable[[Environment], SchemeVal]
AnalRecurFuncType = Callable[[Expression], EvaluableType]
AnalFuncType = Callable[[Expression, AnalRecurFuncType,
                         ResDistancesType], EvaluableType]

_analyzer_rules: Dict[Type, AnalFuncType] = {}


def update_analyzer_rules(rules: Dict[Type, AnalFuncType]):
    _analyzer_rules.update(rules)


def analyze_expr(expr: SequenceExpr, distances: ResDistancesType):
    def analyze_recursive(expr: Expression):
        t = find_type(type(expr), _analyzer_rules)
        f = _analyzer_rules[t]
        return f(expr, analyze_recursive, distances)

    try:
        eval = analyze_recursive(expr)

        def _evaluate(env: Environment):
            try:
                res = eval(env)
            except SchemeRuntimeError as err:
                scheme_panic(str(err))
            return res
    except SchemeAnalysisError as err:
        scheme_panic(str(err))
    return _evaluate


'''analysis list rule definitions'''

AnalRuleType = Union[
    Callable[[], EvaluableType],
    Callable[[GenericExpr], EvaluableType],
    Callable[[GenericExpr, AnalRecurFuncType], EvaluableType],
    Callable[[GenericExpr, AnalRecurFuncType, ResDistancesType], EvaluableType]
]


def analyzer_rule_decorator(rule_func: AnalRuleType):
    arity = len(inspect.getfullargspec(rule_func).args)

    def _analyzer_rule_wrapped(expr: Expression, analyze: AnalRecurFuncType, distances: ResDistancesType):
        args: List[Any] = [expr, analyze, distances]
        return rule_func(*args[0:arity])
    return _analyzer_rule_wrapped


@analyzer_rule_decorator
def analyze_symbol(expr: SymbolExpr, analyze: AnalRecurFuncType, distances: ResDistancesType):
    def _evaluate(env: Environment):
        return pure_resolved_eval_symbol(expr, env, distances)
    return _evaluate


@analyzer_rule_decorator
def analyze_string(expr: StringExpr):
    return lambda env: StringVal(expr.value.literal)


@analyzer_rule_decorator
def analyze_number(expr: NumberExpr):
    return lambda env: NumberVal(expr.value.literal)


@analyzer_rule_decorator
def analyze_boolean(expr: BooleanExpr):
    return lambda env: BooleanVal(expr.value.literal)


@analyzer_rule_decorator
def analyze_nil():
    return lambda env: NilVal()


@analyzer_rule_decorator
def analyze_sequence(expr: SequenceExpr, analyze: AnalRecurFuncType):
    evls: List[EvaluableType] = []
    for subexpr in expr.contents:
        evl = analyze(subexpr)
        evls.append(evl)

    def _evaluate(env: Environment):
        res: SchemeVal = UndefVal()
        for evl in evls:
            res = evl(env)
        return res
    return _evaluate


@analyzer_rule_decorator
def analyze_quote(expr: QuoteExpr):
    return lambda env: quote_token_combo(expr.content)


class ProcAnalyzedVal(ProcVal):
    '''procedure body is a EvaluableType'''

    def __init__(self, name: str, pos_paras: List[str], rest_para: Optional[str], body: EvaluableType, env: Environment):
        super().__init__(name, pos_paras, rest_para, env)
        self.body = body


def pure_eval_call_proc_analyzed(paren: Token, operator: ProcAnalyzedVal, operands: List[SchemeVal]):
    pure_check_proc_arity(paren, operator, operands)
    new_env = pure_eval_call_proc_extend_env(operator, operands)
    return operator.body(new_env)


@analyzer_rule_decorator
def analyze_call(expr: CallExpr, analyze: AnalRecurFuncType):
    operator_evl = analyze(expr.operator)
    operand_evls = [analyze(subexpr) for subexpr in expr.operands]

    def _evaluate(env: Environment):
        operator = operator_evl(env)
        operands = [evl(env) for evl in operand_evls]
        if isinstance(operator, PrimVal):
            return pure_eval_call_prim(expr.paren, operator, operands)
        elif isinstance(operator, ProcAnalyzedVal):
            return pure_eval_call_proc_analyzed(expr.paren, operator, operands)
        else:
            return pure_eval_call_invalid(expr.paren, operator)
    return _evaluate


@analyzer_rule_decorator
def analyze_set(expr: SetExpr, analyze: AnalRecurFuncType, distances: ResDistancesType):
    initializer_evl = analyze(expr.initializer)

    def _evaluate(env: Environment):
        initializer = initializer_evl(env)
        return pure_resolved_eval_set(expr, initializer, env, distances)
    return _evaluate


@analyzer_rule_decorator
def analyze_define_var(expr: DefineVarExpr, analyze: AnalRecurFuncType):
    initializer_evl = analyze(expr.initializer)

    def _evaluate(env: Environment):
        initializer = initializer_evl(env)
        return pure_eval_define_var(expr, initializer, env)
    return _evaluate


@analyzer_rule_decorator
def analyze_define_proc(expr: DefineProcExpr, analyze: AnalRecurFuncType):
    body_evl = analyze(expr.body)

    def _evaluate(env: Environment):
        proc_obj = ProcAnalyzedVal(expr.name.literal, [p.literal for p in expr.pos_paras], expr.rest_para.literal if expr.rest_para is not None else None, body_evl, env)
        env_define(env, expr.name.literal, proc_obj)
        return SymbolVal(expr.name.literal)
    return _evaluate


@analyzer_rule_decorator
def analyze_if(expr: IfExpr, analyze: AnalRecurFuncType):
    pred_evl = analyze(expr.pred)
    then_evl = analyze(expr.then_branch)
    else_evl = None
    if expr.else_branch is not None:
        else_evl = analyze(expr.else_branch)

    def _evaluate(env: Environment):
        if is_truthy(pred_evl(env)):
            return then_evl(env)
        elif else_evl is not None:
            return else_evl(env)
        else:
            return UndefVal()
    return _evaluate


@analyzer_rule_decorator
def analyze_lambda(expr: LambdaExpr, analyze: AnalRecurFuncType):
    body_evl = analyze(expr.body)

    def _evaluate(env: Environment):
        return ProcAnalyzedVal('lambda', [p.literal for p in expr.pos_paras], expr.rest_para.literal if expr.rest_para is not None else None, body_evl, env)
    return _evaluate


@analyzer_rule_decorator
def analyze_and(expr: AndExpr, analyze: AnalRecurFuncType):
    evls = [analyze(subexpr) for subexpr in expr.contents]

    def _evaluate(env: Environment):
        for evl in evls:
            res = evl(env)
            if not is_truthy(res):
                return res
        return res
    return _evaluate


@analyzer_rule_decorator
def analyze_or(expr: OrExpr, analyze: AnalRecurFuncType):
    evls = [analyze(subexpr) for subexpr in expr.contents]

    def _evaluate(env: Environment):
        for evl in evls:
            res = evl(env)
            if is_truthy(res):
                return res
        return res
    return _evaluate


@analyzer_rule_decorator
def analyze_not(expr: NotExpr, analyze: AnalRecurFuncType):
    evl = analyze(expr.content)

    def _evaluate(env: Environment):
        res = evl(env)
        return BooleanVal(False) if is_truthy(res) else BooleanVal(True)
    return _evaluate


def install_analyzer_rules():
    rules = {
        SequenceExpr: analyze_sequence,
        SymbolExpr: analyze_symbol,
        StringExpr: analyze_string,
        NumberExpr: analyze_number,
        BooleanExpr: analyze_boolean,
        NilExpr: analyze_nil,
        QuoteExpr: analyze_quote,
        CallExpr: analyze_call,
        SetExpr: analyze_set,
        DefineVarExpr: analyze_define_var,
        DefineProcExpr: analyze_define_proc,
        IfExpr: analyze_if,
        LambdaExpr: analyze_lambda,
        AndExpr: analyze_and,
        OrExpr: analyze_or,
        NotExpr: analyze_not
    }
    update_analyzer_rules(rules)


def install_rules():
    install_parse_expr_rules()
    install_stringify_expr_rules()
    install_stringify_value_rules()
    install_is_equal_rules()
    install_resolver_rules()
    install_analyzer_rules()
    install_primitives()


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

        # analyze
        evl = analyze_expr(expr, distances)

        # evaluate
        glbenv = make_global_env()
        result = evl(glbenv)
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
        # any kind of panic
        print('* panic: %s' % err.message)
        assert err.message == kargs['panic']
    print('----------')


def test():
    # use before intialization in different scopes
    test_one(
        '''
        (define (f)
          (define a (cons 1 (lambda () a)))
          (car ((cdr a))))
        (f)
        ''',
        result='1'
    )
    # global redefinition
    test_one(
        '''
        (define x 1)
        (define x 2)
        x
        ''',
        result='2'
    )
    # local variable shadows outer definitions
    test_one(
        '''
        (define x 1)
        (define (f)
          (define x 2)
          x)
        (f)
        ''',
        result='2'
    )
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
    # if, begin and set
    test_one(
        '''
        (define x 1)
        (define (f)
          (if (= x 1) (begin (set! x 2) x) (x)))
        (f)
        ''',
        result='2'
    )
    # single iteration
    test_one(
        '''
        (define (run)
          (define (factorial n)
            (define (fact-iter product counter)
              (if (> counter n)
                product
                (fact-iter (* counter product)
                  (+ counter 1))))
            (fact-iter 1 1))
          (factorial 5))
        (run)
        ''',
        result='120'
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


if __name__ == '__main__':
    install_rules()
    test()

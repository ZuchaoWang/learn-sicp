'''
analyzer turns expression into a self-evaluating function
potentially save the effort to parse expression every time it executes
in fact, it might not be that useful, since we have already parsed list expression
but it's fun, so let's implement it

anyway, I feel deeply nested functions harder to debug than deeply nested expression
so I do not recommend this step
'''


import inspect
from typing import Any, Callable, Dict, List, Type, Union

from sicp414_evaluator import AndExpr, BeginExpr, BodyExpr, BooleanExpr, BooleanVal, CallExpr, DefineProcExpr, DefineVarExpr, \
    Environment, Expression, GenericExpr, IfExpr, LambdaExpr, ListExpr, NilExpr, NilVal, NotExpr, NumberExpr, NumberVal, OrExpr, \
    PrimVal, ProcVal, QuoteExpr, SchemePanic, SchemeRuntimeError, SchemeVal, SetExpr, SymbolVal, UndefVal, \
    StringExpr, StringVal, SymbolExpr, Token, env_define, env_extend, find_type, \
    install_is_equal_rules, install_parser_list_rules, install_quote_rules, \
    install_stringify_expr_rules, install_stringify_value_rules, is_truthy, \
    make_global_env, parse_tokens, pure_eval_call_invalid, pure_eval_call_prim, pure_eval_define_var, \
    quote_expr, scan_source, scheme_flush, scheme_panic, stringify_value
from sicp416_resolver import ResDistancesType, install_resolver_rules, pure_resolved_eval_set, pure_resolved_eval_symbol, resolve_expr


class SchemeAnalysisError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self):
        return 'analysis error at %s in line %d: %s' % (str(self.token), self.token.line+1, self.message)


EvaluableType = Callable[[Environment], SchemeVal]
AnalRecurFuncType = Callable[[Expression], EvaluableType]
AnalFuncType = Callable[[Expression, AnalRecurFuncType,
                         ResDistancesType], EvaluableType]

_analyzer_rules: Dict[Type, AnalFuncType] = {}


def update_analyzer_rules(rules: Dict[Type, AnalFuncType]):
    _analyzer_rules.update(rules)


def analyze_expr(expr: BodyExpr, distances: ResDistancesType):
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
    return lambda env: StringVal(expr.token.literal)


@analyzer_rule_decorator
def analyze_number(expr: NumberExpr):
    return lambda env: NumberVal(expr.token.literal)


@analyzer_rule_decorator
def analyze_boolean(expr: BooleanExpr):
    return lambda env: BooleanVal(expr.token.literal)


@analyzer_rule_decorator
def analyze_nil():
    return lambda env: NilVal()


def pure_analyze_sequence(expr_list: List[Expression], analyze: AnalRecurFuncType):
    evls: List[EvaluableType] = []
    for expr in expr_list:
        evl = analyze(expr)
        evls.append(evl)

    def _evaluate(env: Environment):
        res: SchemeVal = UndefVal()
        for evl in evls:
            res = evl(env)
        return res
    return _evaluate


@analyzer_rule_decorator
def analyze_contents(expr: Union[BodyExpr, BeginExpr], analyze: AnalRecurFuncType):
    return pure_analyze_sequence(expr.contents, analyze)


@analyzer_rule_decorator
def analyze_quote(expr: QuoteExpr):
    return lambda env: quote_expr(expr.content)


class ProcAnalyzedVal(ProcVal):
    '''procedure body is a EvaluableType'''

    def __init__(self, name: str, parameters: List[str], body: EvaluableType, env: Environment):
        super().__init__(name, parameters, env)
        self.body = body


def pure_eval_call_proc_analyzed(expr: ListExpr, operator: ProcAnalyzedVal, operands: List[SchemeVal]):
    if len(operator.parameters) != len(operands):
        raise SchemeRuntimeError(expr.token, '%s expect %d arguments, get %d' % (
            operator.name, len(operator.parameters), len(operands)))
    new_env = env_extend(operator.env, operator.parameters, operands)
    return operator.body(new_env)


@analyzer_rule_decorator
def analyze_call(expr: CallExpr, analyze: AnalRecurFuncType):
    operator_evl = analyze(expr.operator)
    operand_evls = [analyze(subexpr) for subexpr in expr.operands]

    def _evaluate(env: Environment):
        operator = operator_evl(env)
        operands = [evl(env) for evl in operand_evls]
        if isinstance(operator, PrimVal):
            return pure_eval_call_prim(expr, operator, operands)
        elif isinstance(operator, ProcAnalyzedVal):
            return pure_eval_call_proc_analyzed(expr, operator, operands)
        else:
            return pure_eval_call_invalid(expr, operator)
    return _evaluate


@analyzer_rule_decorator
def analyze_set(expr: SetExpr, analyze: AnalRecurFuncType, distances: ResDistancesType):
    initializer_evl = analyze(expr.initializer)

    def _evaluate(env: Environment):
        initializer = initializer_evl(env)
        return pure_resolved_eval_set(expr.name, initializer, env, distances)
    return _evaluate


def pure_eval_define_proc_analyzed(name_expr: SymbolExpr, para_exprs: List[SymbolExpr], body_exprs_evl: EvaluableType, env: Environment):
    proc_obj = ProcAnalyzedVal(name_expr.token.literal, [
        p.token.literal for p in para_exprs], body_exprs_evl, env)
    env_define(env, name_expr.token.literal, proc_obj)
    return SymbolVal(name_expr.token.literal)


@analyzer_rule_decorator
def analyze_define_var(expr: DefineVarExpr, analyze: AnalRecurFuncType, distances: ResDistancesType):
    initializer_evl = analyze(expr.initializer)

    def _evaluate(env: Environment):
        initializer = initializer_evl(env)
        return pure_eval_define_var(expr.name, initializer, env)
    return _evaluate


@analyzer_rule_decorator
def analyze_define_proc(expr: DefineProcExpr, analyze: AnalRecurFuncType):
    body_evl = pure_analyze_sequence(expr.body, analyze)

    def _evaluate(env: Environment):
        return pure_eval_define_proc_analyzed(expr.name, expr.parameters, body_evl, env)
    return _evaluate


@analyzer_rule_decorator
def analyze_if(expr: IfExpr, analyze: AnalRecurFuncType):
    pred_evl = analyze(expr.pred)
    then_evl = analyze(expr.then_branch)
    else_evl = analyze(expr.else_branch)

    def _evaluate(env: Environment):
        if is_truthy(pred_evl(env)):
            return then_evl(env)
        else:
            return else_evl(env)
    return _evaluate


@analyzer_rule_decorator
def analyze_lambda(expr: LambdaExpr, analyze: AnalRecurFuncType):
    body_evl = pure_analyze_sequence(expr.body, analyze)

    def _evaluate(env: Environment):
        return ProcAnalyzedVal('lambda', [
            p.token.literal for p in expr.parameters], body_evl, env)
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
        BodyExpr: analyze_contents,
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
        BeginExpr: analyze_contents,
        LambdaExpr: analyze_lambda,
        AndExpr: analyze_and,
        OrExpr: analyze_or,
        NotExpr: analyze_not
    }
    update_analyzer_rules(rules)


def install_rules():
    install_parser_list_rules()
    install_stringify_expr_rules()
    install_stringify_value_rules()
    install_is_equal_rules()
    install_quote_rules()
    install_resolver_rules()
    install_analyzer_rules()


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
        expr = parse_tokens(tokens)

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

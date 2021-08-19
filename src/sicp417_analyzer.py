'''
analyzer turns expression into a self-evaluating function
it saves the effort for reparsing expression every time it executes
can be useful for procedure body, and loop
but I feel deeply nested functions is harder to debug than deeply nested expression
so I would recommend turning it into object rather than function
'''


import inspect
from typing import Any, Callable, Dict, List, Tuple, Type, Union, cast

from sicp414_evaluator import BooleanExpr, BooleanVal, Environment, Expression, ListExpr, NilVal, NumberExpr, NumberVal, \
    Parser, PrimVal, ProcVal, Scanner, SchemePanic, SchemeReparseError, SchemeRuntimeError, \
    SchemeVal, SymbolVal, UndefVal, StringExpr, StringVal, SymbolExpr, Token, env_define, env_extend, is_truthy, \
    make_global_env, pure_eval_call_invalid, pure_eval_call_prim, pure_eval_define_var, quote_expr, \
    reparse_and, reparse_begin, reparse_call, reparse_define, reparse_if, \
    reparse_lambda, reparse_not, reparse_or, reparse_quote, reparse_set, \
    scheme_flush, scheme_panic, stringify_token, stringify_value
from sicp416_resolver import ResolveDistancesType, make_resolver, pure_resolved_eval_set, pure_resolved_eval_symbol


class SchemeAnalysisError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self):
        return 'analysis error at %s in line %d: %s' % (stringify_token(self.token), self.token.line+1, self.message)


EvaluableType = Callable[[Environment], SchemeVal]
AnalyzeFuncType = Callable[[Expression, ResolveDistancesType], EvaluableType]


def pure_analyze_sequence(expr_list: List[Expression], distances: ResolveDistancesType, analyze: AnalyzeFuncType):
    evls: List[EvaluableType] = []
    for expr in expr_list:
        evl = analyze(expr, distances)
        evls.append(evl)

    def _evaluate(env: Environment):
        res: SchemeVal = UndefVal()
        for evl in evls:
            res = evl(env)
        return res
    return _evaluate


class Analyzer:

    _type_rules: Dict[Type, AnalyzeFuncType]
    _list_rules: Dict[str, Callable[[
        ListExpr, ResolveDistancesType, AnalyzeFuncType], EvaluableType]]

    def __init__(self, list_rules):
        self._type_rules = {
            SymbolExpr: self._analyze_symbol,
            StringExpr: self._analyze_string,
            NumberExpr: self._analyze_number,
            BooleanExpr: self._analyze_boolean,
            ListExpr: self._analyze_list,
        }
        self._list_rules = list_rules

    def analyze(self, expr_list: List[Expression], distances: ResolveDistancesType) -> EvaluableType:
        try:
            eval = pure_analyze_sequence(
                expr_list, distances, self._analyze_recursive)

            def _evaluate(env: Environment):
                try:
                    res = eval(env)
                except SchemeRuntimeError as err:
                    scheme_panic(str(err))
                return res
        except SchemeAnalysisError as err:
            scheme_panic(str(err))
        return _evaluate

    def _analyze_recursive(self, expr: Expression, distances: ResolveDistancesType):
        f = self._type_rules[type(expr)]
        return f(expr, distances)

    def _analyze_symbol(self, expr: SymbolExpr, distances: ResolveDistancesType):
        def _evaluate(env: Environment):
            return pure_resolved_eval_symbol(expr, env, distances)
        return _evaluate

    def _analyze_string(self, expr: StringExpr, distances: ResolveDistancesType):
        return lambda env: StringVal(expr.token.literal)

    def _analyze_number(self, expr: NumberExpr, distances: ResolveDistancesType):
        return lambda env: NumberVal(expr.token.literal)

    def _analyze_boolean(self, expr: BooleanExpr, distances: ResolveDistancesType):
        return lambda env: BooleanVal(expr.token.literal)

    def _analyze_list(self, expr: ListExpr, distances: ResolveDistancesType):
        if len(expr.expressions) == 0:
            return lambda env: NilVal()
        elif type(expr.expressions[0]) == SymbolExpr:
            symbol_name = cast(SymbolExpr, expr.expressions[0]).token.literal
            if symbol_name in self._list_rules:
                return self._analyze_list_rule(symbol_name, expr, distances)
        return self._analyze_list_rule('call', expr, distances)

    def _analyze_list_rule(self, rule_name: str, expr: ListExpr, distances: ResolveDistancesType):
        try:
            f = self._list_rules[rule_name]
            res = f(expr, distances, self._analyze_recursive)
        except SchemeReparseError as err:
            raise SchemeAnalysisError(err.token, err.message)
        return res


'''analyzed procedure value'''


class ProcAnalyzedVal(ProcVal):
    '''procedure body is a EvaluableType'''

    def __init__(self, name: str, parameters: List[str], body: EvaluableType, env: Environment):
        ProcVal.__init__(self, name, parameters, env)
        self.body = body


'''analysis list rule definitions'''

AnalyzeListRuleFunc = Union[
    Callable[[], EvaluableType],
    Callable[[ListExpr], EvaluableType],
    Callable[[ListExpr, ResolveDistancesType], EvaluableType],
    Callable[[ListExpr, ResolveDistancesType, AnalyzeFuncType], EvaluableType]
]


def analyze_list_rule_decorator(rule_func: AnalyzeListRuleFunc):
    arity = len(inspect.getfullargspec(rule_func).args)

    def _analyze_list_rule_wrapped(expr: ListExpr, distances: ResolveDistancesType, analyze: AnalyzeFuncType):
        args: List[Any] = [expr, distances, analyze]
        return rule_func(*args[0:arity])
    return _analyze_list_rule_wrapped


@analyze_list_rule_decorator
def analyze_quote(expr: ListExpr):
    content = reparse_quote(expr)
    return lambda env: quote_expr(content)


def pure_eval_call_proc_analyzed(expr: ListExpr, operator: ProcAnalyzedVal, operands: List[SchemeVal]):
    if len(operator.parameters) != len(operands):
        raise SchemeRuntimeError(expr.token, '%s expect %d arguments, get %d' % (
            operator.name, len(operator.parameters), len(operands)))
    new_env = env_extend(operator.env, operator.parameters, operands)
    return operator.body(new_env)


@analyze_list_rule_decorator
def analyze_call(expr: ListExpr, distances: ResolveDistancesType, analyze: AnalyzeFuncType):
    operator_expr, operand_exprs = reparse_call(expr)
    operator_evl = analyze(operator_expr, distances)
    operand_evls = [analyze(subexpr, distances) for subexpr in operand_exprs]

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


@analyze_list_rule_decorator
def analyze_set(expr: ListExpr, distances: ResolveDistancesType, analyze: AnalyzeFuncType):
    name_expr, initializer_expr = reparse_set(expr)
    initializer_evl = analyze(initializer_expr, distances)

    def _evaluate(env: Environment):
        initializer = initializer_evl(env)
        return pure_resolved_eval_set(name_expr, initializer, env, distances)
    return _evaluate


def pure_eval_define_proc_analyzed(name_expr: SymbolExpr, para_exprs: List[SymbolExpr], body_exprs_evl: EvaluableType, env: Environment):
    proc_obj = ProcAnalyzedVal(name_expr.token.literal, [
        p.token.literal for p in para_exprs], body_exprs_evl, env)
    env_define(env, name_expr.token.literal, proc_obj)
    return SymbolVal(name_expr.token.literal)


@analyze_list_rule_decorator
def analyze_define(expr: ListExpr, distances: ResolveDistancesType, analyze: AnalyzeFuncType):
    reparsed = reparse_define(expr)
    if len(reparsed) == 2:  # define variable
        name_expr, initializer_expr = cast(
            Tuple[SymbolExpr, Expression], reparsed)
        initializer_evl = analyze(initializer_expr, distances)

        def _evaluate(env: Environment):
            initializer = initializer_evl(env)
            return pure_eval_define_var(name_expr, initializer, env)
        return _evaluate
    else:  # define procedure
        name_expr, para_exprs, body_exprs = cast(
            Tuple[SymbolExpr, List[SymbolExpr], List[Expression]], reparsed)
        body_exprs_evl = pure_analyze_sequence(body_exprs, distances, analyze)

        def _evaluate(env: Environment):
            return pure_eval_define_proc_analyzed(name_expr, para_exprs, body_exprs_evl, env)
        return _evaluate


@analyze_list_rule_decorator
def analyze_if(expr: ListExpr, distances: ResolveDistancesType, analyze: AnalyzeFuncType):
    pred_expr, then_expr, else_expr = reparse_if(expr)
    pred_evl = analyze(pred_expr, distances)
    then_evl = analyze(then_expr, distances)
    else_evl = analyze(else_expr, distances)

    def _evaluate(env: Environment):
        if is_truthy(pred_evl(env)):
            return then_evl(env)
        else:
            return else_evl(env)
    return _evaluate


@analyze_list_rule_decorator
def analyze_begin(expr: ListExpr, distances: ResolveDistancesType, analyze: AnalyzeFuncType):
    subexprs = reparse_begin(expr)
    return pure_analyze_sequence(subexprs, distances, analyze)


@analyze_list_rule_decorator
def analyze_lambda(expr: ListExpr, distances: ResolveDistancesType, analyze: AnalyzeFuncType):
    para_exprs, body_exprs = reparse_lambda(expr)
    body_exprs_evl = pure_analyze_sequence(body_exprs, distances, analyze)

    def _evaluate(env: Environment):
        return ProcAnalyzedVal('lambda', [
            p.token.literal for p in para_exprs], body_exprs_evl, env)
    return _evaluate


@analyze_list_rule_decorator
def analyze_and(expr: ListExpr, distances: ResolveDistancesType, analyze: AnalyzeFuncType):
    subexprs = reparse_and(expr)
    operand_evls = [analyze(subexpr, distances) for subexpr in subexprs]

    def _evaluate(env: Environment):
        for evl in operand_evls:
            res = evl(env)
            if not is_truthy(res):
                return res
        return res
    return _evaluate


@analyze_list_rule_decorator
def analyze_or(expr: ListExpr, distances: ResolveDistancesType, analyze: AnalyzeFuncType):
    subexprs = reparse_or(expr)
    operand_evls = [analyze(subexpr, distances) for subexpr in subexprs]

    def _evaluate(env: Environment):
        for evl in operand_evls:
            res = evl(env)
            if is_truthy(res):
                return res
        return res
    return _evaluate


@analyze_list_rule_decorator
def analyze_not(expr: ListExpr, distances: ResolveDistancesType, analyze: AnalyzeFuncType):
    subexpr = reparse_not(expr)
    evl = analyze(subexpr, distances)

    def _evaluate(env: Environment):
        res = evl(env)
        return BooleanVal(False) if is_truthy(res) else BooleanVal(True)
    return _evaluate


def make_analyzer():
    '''make custom analyzer, using list rules'''
    list_rules = {
        'quote': analyze_quote,
        'call': analyze_call,
        'set!': analyze_set,
        'define': analyze_define,
        'if': analyze_if,
        'begin': analyze_begin,
        'lambda': analyze_lambda,
        'and': analyze_and,
        'or': analyze_or,
        'not': analyze_not
    }
    analyzer = Analyzer(list_rules)
    return analyzer


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
        scanner = Scanner()
        tokens = scanner.scan(source)

        # parse
        parser = Parser()
        expr_list = parser.parse(tokens)

        # resolve
        resolver = make_resolver()
        distances = resolver.resolve(expr_list)

        # analyze
        analyzer = make_analyzer()
        evl = analyzer.analyze(expr_list, distances)

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
    test()

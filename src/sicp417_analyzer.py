
# scheme analyzer
# we assume operator cannot be a procedure that evaluates to symbol
# see 4.1.7


import inspect
from typing import Any, Callable, Dict, List, Type, Union, cast

from sicp414_evaluator import BooleanExpr, BooleanVal, Environment, Expression, ListExpr, NilVal, NumberExpr, NumberVal, ProcVal, SchemeEnvError, SchemeReparseError, SchemeRuntimeError, SchemeVal, UndefVal, StringExpr, StringVal, SymbolExpr, Token, quote_expr, reparse_call, reparse_quote, scheme_panic, stringify_token
from sicp416_resolver import ResolveDistancesType, env_lookup_at, pure_resolved_eval_symbol


class SchemeAnalysisError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self):
        return 'analysis error at %s in line %d: %s' % (stringify_token(self.token), self.token.line+1, self.message)


EvaluableType = Callable[[Environment], SchemeVal]
AnalyzeFuncType = Callable[[Expression, ResolveDistancesType], EvaluableType]


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
            evls: List[EvaluableType] = []
            for expr in expr_list:
                evl = self._analyze_recursive(expr, distances)
                evls.append(evl)

            def _evaluate(env: Environment):
                try:
                    res: SchemeVal = UndefVal()
                    for evl in evls:
                        res = evl(env)
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
        rule_func(*args[0:arity])
    return _analyze_list_rule_wrapped


@analyze_list_rule_decorator
def analyze_quote(expr: ListExpr):
    content = reparse_quote(expr)
    return lambda env: quote_expr(content)


@analyze_list_rule_decorator
def analyze_call(expr: ListExpr, distances: ResolveDistancesType, analyze: AnalyzeFuncType):
    operator_expr, operand_exprs = reparse_call(expr)
    operator_evl = analyze(operator_expr, distances)
    operand_evls = [analyze(subexpr, distances) for subexpr in operand_exprs]
    def _evaluate


def analyze_set(expr: Expression, analyze: AnalyzeType) -> AnalyzeRetType:
    head: LinkedList = expr.value
    name: str = head.expr.value
    if head.length() == 2:
        get_expr = analyze(head.next)
        return lambda env: env.set(name, get_expr())
    else:
        panic('analyze_set: list length should be 2')


def analyze_define(expr: Expression, analyze: AnalyzeType) -> AnalyzeRetType:
    head: LinkedList = expr.value
    name: str = head.expr.value
    hl = head.length()
    if hl == 2:
        # define variable
        get_expr = analyze(head.next)
        return lambda env: env.define(name, get_expr())
    elif hl == 3:
        # define procedure
        if head.next.expr.tag != LIST:
            panic('analyze_define: procedure parameters must be a list')
        parameters: List[str] = []
        para_exprs: LinkedList = head.next.expr.value
        while para_exprs is not None:
            if para_exprs.expr.tag != SYMBOL:
                panic('analyze_define: procedure parameters must all be symbols')
            parameters.append(para_exprs.expr.value)
            para_exprs = para_exprs.next
        body = analyze(head.next.next.expr)
        proc = Expression(PROCEDURE, Procedure(parameters, body))
        return lambda env: env.define(name, proc)
    else:
        panic('analyze_define: list length should be 2')


def analyze_application(expr: Expression, analyze: AnalyzeType) -> AnalyzeRetType:
    head: LinkedList = expr.value
    get_operator = analyze(head.expr)
    get_operands: List[AnalyzeRetType] = []
    op_expr = head.next
    while op_expr is not None:
        get_operands.append(analyze(op_expr))
        op_expr = op_expr.next

    def _analyze_application(env: Environment):
        operator = get_operator(env)
        operands = [get_op(env) for get_op in get_operands]
        if operator.tag == PRIMITIVE:
            primitive: Primitive = operator.value
            if len(operands) != primitive.arity:
                panic('analyze_application: primitive incorrect arity %d, should be %d' % (
                    len(operands), primitive.arity))
            return primitive.body(*operands)
        elif operator.tag == PROCEDURE:
            procedure: Procedure = operator.value
            if len(operands) != len(procedure.parameters):
                panic('analyze_application: procedure incorrect arity %d, should be %d' % (
                    len(operands), len(procedure.parameters)))
            new_env = env.extend(procedure.parameters, operands)
            return procedure.body(new_env)
        else:
            panic(
                'analyze_application: expression of type %s cannot be used as operator' % operator.tag)
    return _analyze_application

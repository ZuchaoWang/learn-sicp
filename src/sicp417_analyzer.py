
# scheme analyzer
# we assume operator cannot be a procedure that evaluates to symbol
# see 4.1.7


AnalyzeRetType = Callable[[Environment], Expression]
AnalyzeType = Callable[[Optional[Expression]], AnalyzeRetType]
AnalyzeConfigType = Callable[[Environment, AnalyzeType], AnalyzeRetType]


class Analyzer:
    def __init__(self, special_forms: Dict[str, AnalyzeConfigType], application: AnalyzeConfigType, symbol: AnalyzeConfigType):
        self._special_forms = special_forms
        self._application = application
        self._symbol = symbol

    def analyze(self, expr: Optional[Expression]) -> AnalyzeRetType:
        if expr is not None:
            if expr.tag == NUMBER or expr.tag == STRING:
                return lambda _: expr
            elif expr.tag == SYMBOL:
                return self.analyze_symbol(expr)
            else:  # must be list
                return self.analyze_list(expr)

    def analyze_symbol(self, expr: Expression):
        return self._symbol(expr, self.analyze)

    def analyze_list(self, expr: Expression):
        head: Optional[LinkedList] = expr.value
        if head is None:  # empty list
            panic('analyzer: cannot evaluate empty list')
        else:
            hexpr = head.expr
            if hexpr.tag == NUMBER:
                panic('analyzer: number cannot be operator or special form')
            if hexpr.tag == STRING:
                panic('analyzer: string cannot be operator or special form')
            if hexpr.tag == SYMBOL:
                f = self._special_forms.get(hexpr.value, None)
                if f is not None:
                    return f(expr, self.analyze)
            return self._application(expr, self.analyze)


def analyze_symbol(expr: Expression, _analyze: AnalyzeType) -> AnalyzeRetType:
    '''lookup variable'''
    name = expr.value
    return lambda env: env.lookup(name)


def analyze_quote(expr: Expression, _analyze: AnalyzeType) -> AnalyzeRetType:
    head: LinkedList = expr.value
    if head.length() == 2:
        quoted = head.next.expr
        return lambda _: quoted
    else:
        panic('analyze_quote: list length should be 2')


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
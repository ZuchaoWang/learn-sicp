from typing import List
from sicp414_evaluator import Expression, IfExpr, ListExpr, SchemeParserError, update_parser_list_rules
from sicp416_resolver import ResBindingsType, ResRecurFuncType, ResStackType, pure_resolve_sequence, resolver_rule_decorator, update_resolver_rules


class AmbExpr(ListExpr):
    def __init__(self, expr: ListExpr, contents: List[Expression]):
        super().__init__(expr.token, expr.expressions)
        self.contents = contents


def parse_amb(expr: ListExpr):
    '''parse amb from list expression'''
    return AmbExpr(expr, expr.expressions[1:])


class RequireExpr(ListExpr):
    def __init__(self, expr: ListExpr, pred: Expression):
        super().__init__(expr.token, expr.expressions)
        self.pred = pred


def parse_require(expr: ListExpr):
    '''
    parse require from list expression

    we could see require as a syntactic suger, transforming it to (if pred (amb))
    but all our expression have a token to indicate its location in source code
    it's not easy to assign tokens to if-expr and amb-expr in this way
    so we have a seperate require-expr

    in fact, according to "crafting interpreter", to show resolution and runtime error
    only symbol-expr and set-expr need the name symbol token
    then call prim/proc need the left-paren token
    but we still think it's more elegant to have token in all expressions
    '''
    if len(expr.expressions) != 2:
        raise SchemeParserError(
            expr.token, 'require should have 2 expressions, now %d' % len(expr.expressions))
    return RequireExpr(expr, expr.expressions[1])


def install_parser_amb_list_rules():
    rules = {'amb': parse_amb}
    update_parser_list_rules(rules)


@resolver_rule_decorator
def resolve_amb(expr: AmbExpr, phase: bool, resolve: ResRecurFuncType, stack: ResStackType, bindings: ResBindingsType):
    '''extending resolver rule to support amb, just resolve its contents one by one'''
    pure_resolve_sequence(expr.contents, phase, resolve)


def install_resolver_lazy_rules():
    rules = {AmbExpr: resolve_amb}
    update_resolver_rules(rules)

'''
lazy evaluation interpreter can dealy evaluating expression to when needed
this results in normal-order, or non-strict evaluation

inspired by exercide 4.31, we use explicity lazy evaluation
but our syntax is (lazy expr), where "lazy" is put at front
our lazy is just another list syntax like quote
it can be anywhere in code, not restricted to proceudre parameter
out lazy also automatically memoize the value once evaluated

since the default evaluation is still eager, not lazy, we can reuse previous evaluator
we will use the resolved evaluator, and the resolution rules are almost unchanged
we will not analyze the expression tree to create evaluate function, since that's difficult to debug
'''

from typing import Optional
from sicp414_evaluator import Environment, EvalFuncType, Expression, ListExpr, PrimVal, ProcPlainVal, SchemeReparseError, SchemeVal, is_truthy, pure_eval_call_invalid, pure_eval_call_prim, pure_eval_call_proc_plain, reparse_call, reparse_if
from sicp416_resolver import ResolveDistancesType, ResFuncType, resolve_list_rule_decorator, resolved_eval_list_rule_decorator

def reparse_lazy(expr: ListExpr):
    '''reparse lazy from list expression'''
    if len(expr.expressions) != 2:
        raise SchemeReparseError(
            expr.token, 'lazy should have 2 expressions, now %d' % len(expr.expressions))
    return expr.expressions[1]

@resolve_list_rule_decorator
def resolve_lazy(expr: ListExpr, phase: bool, resolve: ResFuncType):
    '''extending resolver list rule to support lazy'''
    content = reparse_lazy(expr)
    resolve(content, phase)

class ThunkVal(SchemeVal):
    '''
    created dynamically by lazy
    will not be checked for equality or stringified, because both will trigger forcing
    therefore no need to modify ValueStringifier and EqualityChecker
    '''
    def __init__(self, expr: Expression, env: Environment):
        self.expr = expr
        self.env = env
        self.value: Optional[SchemeVal] = None # for memoization

def force(sv: SchemeVal, evl: EvalFuncType) -> SchemeVal:
    if isinstance(sv, ThunkVal):
        if sv.value is None:
            actual_value = evl(sv.expr, sv.env)
            sv.value = force(actual_value, evl)
        return sv.value
    else:
        return sv

@resolved_eval_list_rule_decorator
def lazy_resolve_eval_lazy(expr: ListExpr, env: Environment):
    content = reparse_lazy(expr)
    return ThunkVal(content, env)

@resolved_eval_list_rule_decorator
def lazy_resolved_eval_call(expr: ListExpr, env: Environment, evl: EvalFuncType):
    operator_expr, operand_exprs = reparse_call(expr)
    operator = evl(operator_expr, env)
    operands = [evl(subexpr, env) for subexpr in operand_exprs]
    operator_forced = force(operator, evl)
    if isinstance(operator_forced, PrimVal):
        operands_forced = [force(op, evl) for op in operands]
        return pure_eval_call_prim(expr, operator_forced, operands_forced)
    elif isinstance(operator_forced, ProcPlainVal):
        return pure_eval_call_proc_plain(expr, operator_forced, operands, evl)
    else:
        return pure_eval_call_invalid(expr, operator_forced)

@resolved_eval_list_rule_decorator
def lazy_resolved_eval_if(expr: ListExpr, env: Environment, evl: EvalFuncType):
    pred_expr, then_expr, else_expr = reparse_if(expr)
    pred_val = evl(pred_expr, env)
    pred_forced = force(pred_val, evl)
    if is_truthy(pred_forced):
        return evl(then_expr, env)
    else:
        return evl(else_expr, env)
from typing import Callable, Dict, List, TypedDict
from sicp414_evaluator import CallExpr, NilExpr, QuoteExpr, SequenceExpr, StringExpr, SymbolExpr, NumberExpr, BooleanExpr
from sicp523_simulator import AssignMstmt, BranchMstmt, ConstMxpr, GotoMstmt, LabelMstmt, LabelMxpr, Mstmt, OpMxpr, RegMxpr, TestMstmt

MakeEvalFuncType = Callable[[], List[Mstmt]]


class MakeEvalExprRuleType(TypedDict):
    test_and_branch: MakeEvalFuncType
    goto: MakeEvalFuncType


_make_eval_expr_rules: Dict[str, MakeEvalExprRuleType] = {}


def update_make_eval_expr_rules(rules: Dict[str, MakeEvalExprRuleType]):
    _make_eval_expr_rules.update(rules)


def call_make_eval(make_eval: MakeEvalFuncType):
    if make_eval.called:  # type: ignore
        return []
    else:
        make_eval.called = True  # type: ignore
        return make_eval()


def make_eval_dispatch():
    mstmts: List[Mstmt] = []
    for rule in _make_eval_expr_rules.values():
        mstmts.extend(call_make_eval(rule['test_and_branch']))
    mstmts.extend(GotoMstmt(LabelMstmt('unknown-expression-type')))
    return mstmts


def make_eval_sequence_tab() -> List[Mstmt]:
    return [
        TestMstmt(
            OpMxpr('py-type-eq', [RegMxpr('expr'), ConstMxpr(SequenceExpr)])),
        BranchMstmt(LabelMxpr('ev-sequence'))
    ]


def make_eval_symbol_tab() -> List[Mstmt]:
    return [
        TestMstmt(
            OpMxpr('py-type-eq', [RegMxpr('expr'), ConstMxpr(SymbolExpr)])),
        BranchMstmt(LabelMxpr('ev-symbol'))
    ]

def make_eval_symbol_goto() -> List[Mstmt]:
    return [
        LabelMstmt('ev-symbol'),
        AssignMstmt('val', OpMxpr('pure_eval_symbol', [RegMxpr('expr')])),
        GotoMstmt(LabelMxpr('continue'))
    ] 

def make_eval_string_tab() -> List[Mstmt]:
    return [
        TestMstmt(
            OpMxpr('py-type-eq', [RegMxpr('expr'), ConstMxpr(StringExpr)])),
        BranchMstmt(LabelMxpr('ev-string'))
    ]

def make_eval_string_goto() -> List[Mstmt]:
    return [
        LabelMstmt('ev-string'),
        AssignMstmt('val', OpMxpr('pure_eval_string', [RegMxpr('expr')])),
        GotoMstmt(LabelMxpr('continue'))
    ] 

def make_eval_number_tab() -> List[Mstmt]:
    return [
        TestMstmt(
            OpMxpr('py-type-eq', [RegMxpr('expr'), ConstMxpr(NumberExpr)])),
        BranchMstmt(LabelMxpr('ev-number'))
    ]

def make_eval_number_goto() -> List[Mstmt]:
    return [
        LabelMstmt('ev-number'),
        AssignMstmt('val', OpMxpr('pure_eval_number', [RegMxpr('expr')])),
        GotoMstmt(LabelMxpr('continue'))
    ]

def make_eval_boolean_tab() -> List[Mstmt]:
    return [
        TestMstmt(
            OpMxpr('py-type-eq', [RegMxpr('expr'), ConstMxpr(BooleanExpr)])),
        BranchMstmt(LabelMxpr('ev-boolean'))
    ]

def make_eval_boolean_goto() -> List[Mstmt]:
    return [
        LabelMstmt('ev-boolean'),
        AssignMstmt('val', OpMxpr('pure_eval_boolean', [RegMxpr('expr')])),
        GotoMstmt(LabelMxpr('continue'))
    ]

def make_eval_nil_tab() -> List[Mstmt]:
    return [
        TestMstmt(
            OpMxpr('py-type-eq', [RegMxpr('expr'), ConstMxpr(NilExpr)])),
        BranchMstmt(LabelMxpr('ev-nil'))
    ]

def make_eval_nil_goto() -> List[Mstmt]:
    return [
        LabelMstmt('ev-nil'),
        AssignMstmt('val', OpMxpr('pure_eval_nil', [RegMxpr('expr')])),
        GotoMstmt(LabelMxpr('continue'))
    ]

def make_eval_quote_tab() -> List[Mstmt]:
    return [
        TestMstmt(
            OpMxpr('py-type-eq', [RegMxpr('expr'), ConstMxpr(QuoteExpr)])),
        BranchMstmt(LabelMxpr('ev-quote'))
    ]

def make_eval_quote_goto() -> List[Mstmt]:
    return [
        LabelMstmt('ev-quote'),
        AssignMstmt('val', OpMxpr('pure_eval_quote', [RegMxpr('expr')])),
        GotoMstmt(LabelMxpr('continue'))
    ]

def make_eval_quote_call() -> List[Mstmt]:
    return [
        TestMstmt(
            OpMxpr('py-type-eq', [RegMxpr('expr'), ConstMxpr(CallExpr)])),
        BranchMstmt(LabelMxpr('ev-call'))
    ]
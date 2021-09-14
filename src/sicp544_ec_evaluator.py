'''
this is mostly machine language code, see ec_eval_code
we lack the mechanism to write it in a modular way in machine language
unless we generate the code using python, but that will make the code hard to read
'''

from typing import Any, Callable, Dict, List, Set, Type, TypedDict, Union
from sicp414_evaluator import AndExpr, BooleanVal, CallExpr, Environment, Expression, GenericExpr, GenericVal, NilExpr, NilVal, NumberVal, OrExpr, PairVal, PrimVal, ProcPlainVal, ProcVal, QuoteExpr, SchemeEnvError, SchemePanic, SchemeRuntimeError, SchemeVal, SequenceExpr, StringExpr, StringVal, SymbolExpr, NumberExpr, BooleanExpr, Token, TokenTag, env_extend, env_lookup, install_is_equal_rules, install_parse_expr_rules, install_primitives, install_stringify_expr_rules, install_stringify_value_rules, make_global_env, parse_expr, parse_tokens, pure_check_prim_arity, pure_check_proc_arity, pure_eval_boolean, pure_eval_call_proc_extend_env, pure_eval_lambda_plain, pure_eval_nil, pure_eval_number, pure_eval_quote, pure_eval_string, pure_eval_symbol, scan_source, scheme_flush, scheme_panic, stringify_expr, stringify_value
from sicp523_simulator import AssignMstmt, BranchMstmt, ConstMxpr, GotoMstmt, LabelMstmt, LabelMxpr, Mstmt, OpMxpr, PerformMstmt, RegMxpr, RestoreMstmt, SaveMstmt, TestMstmt, get_operations, init_machine_pc, install_assemble_mstmt_rules, install_assemble_mxpr_rules, install_operations, make_machine, make_run_machine, update_operations
from sicp524_monitor import MachineStatistic, monitor_statistics


ec_eval_code = [
    LabelMstmt('main'),
    AssignMstmt('continue', LabelMxpr('done')),


    LabelMstmt('eval-dispatch'),
    # unev stores the type name of expr
    AssignMstmt('unev', OpMxpr('get_expr_type', [RegMxpr('expr')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'),
                                ConstMxpr(StringVal('SequenceExpr'))])),
    BranchMstmt(LabelMxpr('ev-sequence')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'),
                                ConstMxpr(StringVal('SymbolExpr'))])),
    BranchMstmt(LabelMxpr('ev-symbol')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'),
                                ConstMxpr(StringVal('StringExpr'))])),
    BranchMstmt(LabelMxpr('ev-string')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'),
                                ConstMxpr(StringVal('NumberExpr'))])),
    BranchMstmt(LabelMxpr('ev-number')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'),
                                ConstMxpr(StringVal('BooleanExpr'))])),
    BranchMstmt(LabelMxpr('ev-boolean')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'),
                                ConstMxpr(StringVal('NilExpr'))])),
    BranchMstmt(LabelMxpr('ev-nil')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'),
                                ConstMxpr(StringVal('QuoteExpr'))])),
    BranchMstmt(LabelMxpr('ev-quote')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'),
                                ConstMxpr(StringVal('LambdaExpr'))])),
    BranchMstmt(LabelMxpr('ev-lambda')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'),
                                ConstMxpr(StringVal('CallExpr'))])),
    BranchMstmt(LabelMxpr('ev-call')),
    # put expression type in val, then goto error
    AssignMstmt('val', RegMxpr('unev')),
    GotoMstmt(LabelMxpr('error-unknown-expression-type')),



    LabelMstmt('ev-string'),
    AssignMstmt('val', OpMxpr('pure_eval_string', [RegMxpr('expr')])),
    GotoMstmt(RegMxpr('continue')),


    LabelMstmt('ev-number'),
    AssignMstmt('val', OpMxpr('pure_eval_number', [RegMxpr('expr')])),
    GotoMstmt(RegMxpr('continue')),


    LabelMstmt('ev-boolean'),
    AssignMstmt('val', OpMxpr('pure_eval_boolean', [RegMxpr('expr')])),
    GotoMstmt(RegMxpr('continue')),


    LabelMstmt('ev-nil'),
    AssignMstmt('val', OpMxpr('pure_eval_nil', [])),
    GotoMstmt(RegMxpr('continue')),


    LabelMstmt('ev-quote'),
    AssignMstmt('val', OpMxpr('pure_eval_quote', [RegMxpr('expr')])),
    GotoMstmt(RegMxpr('continue')),


    LabelMstmt('ev-lambda'),
    AssignMstmt('val', OpMxpr('pure_eval_lambda_plain',
                              [RegMxpr('expr'), RegMxpr('env')])),
    GotoMstmt(RegMxpr('continue')),


    LabelMstmt('ev-symbol'),
    AssignMstmt('val', OpMxpr('ec_eval_symbol', [
                RegMxpr('expr'), RegMxpr('env')])),
    # val = pair(error, result), unev = error
    AssignMstmt('unev', OpMxpr('car', [RegMxpr('val')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(NilVal())])),
    BranchMstmt(LabelMxpr('ev-symbol-no-error')),
    # val = error, where error is symbol name
    AssignMstmt('val', RegMxpr('unev')),
    GotoMstmt(LabelMxpr('error-symbol-undefined')),
    LabelMstmt('ev-symbol-no-error'),
    # val = result
    AssignMstmt('val', OpMxpr('cdr', [RegMxpr('val')])),
    GotoMstmt(RegMxpr('continue')),


    # we need three registers for contents, n=len(contents), i
    # we use unev, unev2, unev3
    LabelMstmt('ev-sequence'),
    AssignMstmt('unev', OpMxpr('get_expr_contents', [RegMxpr('expr')])),
    AssignMstmt('unev2', OpMxpr('get_exprs_len', [RegMxpr('unev')])),
    TestMstmt(OpMxpr('>', [RegMxpr('unev2'), ConstMxpr(NumberVal(0))])),
    BranchMstmt(LabelMxpr('ev-sequence-non-empty')),
    GotoMstmt(RegMxpr('continue')),
    LabelMstmt('ev-sequence-non-empty'),
    SaveMstmt('continue'),
    # now unev2 = len-1
    AssignMstmt('unev2', OpMxpr(
        '-', [RegMxpr('unev2'), ConstMxpr(NumberVal(1))])),
    # init unev3 = 0
    AssignMstmt('unev3', ConstMxpr(NumberVal(0))),
    LabelMstmt('ev-sequence-fronts'),
    TestMstmt(OpMxpr('=', [RegMxpr('unev3'), RegMxpr('unev2')])),
    BranchMstmt(LabelMxpr('ev-sequence-last')),
    SaveMstmt('unev'),
    SaveMstmt('unev2'),
    SaveMstmt('unev3'),
    SaveMstmt('env'),
    AssignMstmt('expr', OpMxpr(
        'get_expr_at', [RegMxpr('unev'), RegMxpr('unev3')])),
    AssignMstmt('continue', LabelMxpr('ev-sequence-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
    LabelMstmt('ev-sequence-ret'),
    RestoreMstmt('env'),
    RestoreMstmt('unev3'),
    RestoreMstmt('unev2'),
    RestoreMstmt('unev'),
    AssignMstmt('unev3', OpMxpr(
        '+', [RegMxpr('unev3'), ConstMxpr(NumberVal(1))])),
    GotoMstmt(LabelMxpr('ev-sequence-fronts')),
    # support for tail recursion: ensure goto eval-dispatch is the last instruction
    # to do that, can't save/restore for env/unev/unev2/unev3, and should restore continue before call rather than after
    LabelMstmt('ev-sequence-last'),
    AssignMstmt('expr', OpMxpr(
        'get_expr_at', [RegMxpr('unev'), RegMxpr('unev3')])),
    RestoreMstmt('continue'),
    GotoMstmt(LabelMxpr('eval-dispatch')),


    LabelMstmt('ev-call'),
    SaveMstmt('continue'),
    SaveMstmt('expr'),
    SaveMstmt('env'),
    AssignMstmt('unev', OpMxpr('get_call_operands', [RegMxpr('expr')])),
    SaveMstmt('unev'),
    # getting operator
    AssignMstmt('expr', OpMxpr('get_call_operator', [RegMxpr('expr')])),
    AssignMstmt('continue', LabelMxpr('ev-call-operands')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
    LabelMstmt('ev-call-operands'),
    AssignMstmt('proc', RegMxpr('val')),
    # getting operands
    # we still do save/restore for the last operand
    # this has a little performance lost, but do not destroy tail recursion
    AssignMstmt('argl', ConstMxpr([])),
    RestoreMstmt('unev'),
    RestoreMstmt('env'),
    AssignMstmt('unev2', OpMxpr('get_exprs_len', [RegMxpr('unev')])),
    AssignMstmt('unev3', ConstMxpr(NumberVal(0))),
    SaveMstmt('proc'),
    LabelMstmt('ev-call-operand-start'),
    TestMstmt(OpMxpr('=', [RegMxpr('unev3'), RegMxpr('unev2')])),
    BranchMstmt(LabelMxpr('ev-call-call')),
    SaveMstmt('env'),
    SaveMstmt('unev'),
    SaveMstmt('unev2'),
    SaveMstmt('unev3'),
    SaveMstmt('argl'),
    AssignMstmt('expr', OpMxpr(
        'get_expr_at', [RegMxpr('unev'), RegMxpr('unev3')])),
    AssignMstmt('continue', LabelMxpr('ev-call-operand-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
    RestoreMstmt('argl'),
    RestoreMstmt('unev3'),
    RestoreMstmt('unev2'),
    RestoreMstmt('unev'),
    RestoreMstmt('env'),
    PerformMstmt(OpMxpr('append_val_list', [RegMxpr('argl'), RegMxpr('val')])),
    AssignMstmt('unev3', OpMxpr(
        '+', [RegMxpr('unev3'), ConstMxpr(NumberVal(1))])),
    GotoMstmt(LabelMxpr('ev-call-operand-start')),
    # calling body, need proc, and argl is already correct
    LabelMstmt('ev-call-call'),
    RestoreMstmt('proc'),
    RestoreMstmt('expr'),
    RestoreMstmt('continue'),
    AssignMstmt('unev', OpMxpr('get_val_type', [RegMxpr('proc')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'),
                                ConstMxpr(StringVal('ProcPlainVal'))])),
    BranchMstmt(LabelMxpr('ev-call-proc-plain')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'),
                                ConstMxpr(StringVal('PrimVal'))])),
    BranchMstmt(LabelMxpr('ev-call-prim')),
    AssignMstmt('val', RegMxpr('unev')),
    GotoMstmt(LabelMxpr('error-unknown-operator-type')),


    LabelMstmt('ev-call-proc-plain'),
    AssignMstmt('val', OpMxpr('pure_check_proc_arity', [RegMxpr('expr'), RegMxpr('proc'), RegMxpr('argl')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('val'), ConstMxpr(StringVal(''))])),
    BranchMstmt(LabelMxpr('ev-call-proc-plain-arity-ok')),
    GotoMstmt(LabelMxpr('error-call-arity')),
    LabelMstmt('ev-call-proc-plain-arity-ok'),
    AssignMstmt('env', OpMxpr('pure_eval_call_proc_extend_env', [RegMxpr('proc'), RegMxpr('argl')])),
    AssignMstmt('expr', OpMxpr('get_proc_plain_val_body', [RegMxpr('proc')])),
    GotoMstmt(LabelMxpr('ev-sequence')),


    LabelMstmt('ev-call-prim'),
    AssignMstmt('val', OpMxpr('pure_check_prim_arity', [RegMxpr('expr'), RegMxpr('proc'), RegMxpr('argl')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('val'), ConstMxpr(StringVal(''))])),
    BranchMstmt(LabelMxpr('ev-call-prim-arity-ok')),
    GotoMstmt(LabelMxpr('error-call-arity')),
    LabelMstmt('ev-call-prim-arity-ok'),
    AssignMstmt('val', OpMxpr('call_primitive', [RegMxpr('proc'), RegMxpr('argl')])),
    GotoMstmt(LabelMxpr('continue')),


    LabelMstmt('error-unknown-expression-type'),
    PerformMstmt(OpMxpr('print_panic', [ConstMxpr(
        StringVal('error-unknown-expression-type')), RegMxpr('val')])),
    # following goto not really necessary, since print_panic will exit execution
    GotoMstmt(LabelMxpr('done')),


    LabelMstmt('error-unknown-operator-type'),
    PerformMstmt(OpMxpr('print_panic', [ConstMxpr(
        StringVal('error-unknown-operator-type')), RegMxpr('val')])),
    # following goto not really necessary, since print_panic will exit execution
    GotoMstmt(LabelMxpr('done')),


    LabelMstmt('error-symbol-undefined'),
    PerformMstmt(OpMxpr('print_panic', [ConstMxpr(
        StringVal('error-symbol-undefined')), RegMxpr('val')])),
    GotoMstmt(LabelMxpr('done')),


    LabelMstmt('error-call-arity'),
    PerformMstmt(OpMxpr('print_panic', [ConstMxpr(
        StringVal('error-call-arity')), RegMxpr('val')])),
    GotoMstmt(LabelMxpr('done')),


    LabelMstmt('done')
]

'''
additioanl operations
we try to make their input/ouput only of following types
Expression, List[Expression], Environment, SchemeVal, List[SchemeVal]
we try to exclude pure integer and string
'''


def ec_eval_symbol(expr: SymbolExpr, env: Environment):
    '''return error and result'''
    try:
        return PairVal(NilVal(), pure_eval_symbol(expr, env))
    except SchemeEnvError:
        return PairVal(StringVal(expr.name.literal), NilVal())


def ec_pure_check_prim_arity(expr: CallExpr, operator: PrimVal, operands: List[SchemeVal]):
    try:
        pure_check_prim_arity(expr, operator, operands)
        return StringVal('')
    except SchemeRuntimeError as err:
        return StringVal(str(err))


def ec_pure_check_proc_arity(expr: CallExpr, operator: ProcVal, operands: List[SchemeVal]):
    try:
        pure_check_proc_arity(expr, operator, operands)
        return StringVal('')
    except SchemeRuntimeError as err:
        return StringVal(str(err))


def get_expr_type(expr: GenericExpr):
    return StringVal(type(expr).__name__)


def get_expr_contents(expr: Union[SequenceExpr, AndExpr, OrExpr]):
    return expr.contents


def get_exprs_len(exprs: List[GenericExpr]):
    return NumberVal(len(exprs))


def get_expr_at(exprs: List[GenericExpr], index: NumberVal):
    return exprs[int(index.value)]


def get_call_operator(expr: CallExpr):
    return expr.operator


def get_call_operands(expr: CallExpr):
    return expr.operands


def get_proc_plain_val_body(proc: ProcPlainVal):
    return proc.body


def append_val_list(vals: List[SchemeVal], val: SchemeVal):
    vals.append(val)


def get_val_type(expr: GenericVal):
    return StringVal(type(expr).__name__)


def print_panic(error: StringVal, detail: StringVal):
    message = stringify_value(error) + ": " + stringify_value(detail)
    scheme_panic(message)


def install_ec_operations():
    ops = {
        'get_expr_type': get_expr_type,
        'get_expr_contents': get_expr_contents,
        'get_exprs_len': get_exprs_len,
        'get_expr_at': get_expr_at,
        'get_call_operator': get_call_operator,
        'get_call_operands': get_call_operands,
        'get_proc_plain_val_body': get_proc_plain_val_body,
        'append_val_list': append_val_list,
        'pure_eval_string': pure_eval_string,
        'pure_eval_number': pure_eval_number,
        'pure_eval_boolean': pure_eval_boolean,
        'pure_eval_nil': pure_eval_nil,
        'pure_eval_quote': pure_eval_quote,
        'ec_eval_symbol': ec_eval_symbol,
        'ec_pure_check_prim_arity': ec_pure_check_prim_arity,
        'ec_pure_check_proc_arity': ec_pure_check_proc_arity,
        'pure_eval_lambda_plain': pure_eval_lambda_plain,
        'pure_eval_call_proc_extend_env': pure_eval_call_proc_extend_env,
        'print_panic': print_panic
    }
    update_operations(ops)


'''we have more tmp registers: unev2, unev3'''
ec_eval_regs = {
    'val': None,
    'expr': None,
    'env': None,
    'unev': None,
    'unev2': None,
    'unev3': None,
}


def test_one(source: str, **kargs: str):
    # source
    source = source.strip()
    print('* source: %s' % source)

    try:
        # scan
        tokens = scan_source(source)

        # parse
        combos = parse_tokens(tokens)
        expr = parse_expr(combos)

        # build machine
        ops = get_operations()
        glbenv = make_global_env()
        machine = make_machine(ec_eval_regs, ops, ec_eval_code)
        machine.state.regs.update({'expr': expr, 'env': glbenv})
        execute_machine = make_run_machine(lambda _: False)

        # result
        init_machine_pc(machine)
        execute_machine(machine)
        result = machine.state.regs['val']
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
    test_one(
        'x',
        panic='error-symbol-undefined: x'
    )
    test_one(
        '''
        ()
        1
        "2"
        #t
        ''',
        result='#t',
        panic=''
    )


def install_rules():
    install_parse_expr_rules()
    install_stringify_expr_rules()
    install_stringify_value_rules()
    install_is_equal_rules()
    install_primitives()
    install_assemble_mxpr_rules()
    install_assemble_mstmt_rules()
    install_operations()
    install_ec_operations()


if __name__ == '__main__':
    install_rules()
    test()

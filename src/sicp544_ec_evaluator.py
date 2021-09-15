'''
this is mostly machine language code, see ec_eval_code
we lack the mechanism to write it in a modular way in machine language
unless we generate the code using python, but that will make the code hard to read
'''

from typing import List, Union
from sicp414_evaluator import AndExpr, BooleanVal, CallExpr, Environment, Expression, GenericExpr, GenericVal, IfExpr, \
    NilVal, NumberVal, OrExpr, PairVal, PrimVal, ProcPlainVal, ProcVal, SchemePanic, SchemePrimError, \
    SchemeRuntimeError, SchemeVal, SequenceExpr, StringVal, SymbolExpr, UndefVal, install_is_equal_rules, \
    install_parse_expr_rules, install_primitives, install_stringify_expr_rules, install_stringify_value_rules, \
    make_global_env, parse_expr, parse_tokens, pure_check_prim_arity, pure_check_proc_arity, pure_eval_boolean, \
    pure_eval_call_invalid, pure_eval_call_proc_extend_env, pure_eval_lambda_plain, pure_eval_nil, \
    pure_eval_number, pure_eval_quote, pure_eval_string, pure_eval_symbol, scan_source, \
    scheme_flush, scheme_panic, stringify_value
from sicp523_simulator import AssignMstmt, BranchMstmt, ConstMxpr, GotoMstmt, LabelMstmt, LabelMxpr, OpMxpr, \
    PerformMstmt, RegMxpr, RestoreMstmt, SaveMstmt, TestMstmt, get_operations, init_machine_pc, \
    install_assemble_mstmt_rules, install_assemble_mxpr_rules, install_operations, \
    make_machine, make_run_machine, update_operations

# fmt: off
ec_eval_code = [
  LabelMstmt('main'),
    AssignMstmt('continue', LabelMxpr('done')),

  LabelMstmt('eval-dispatch'),
    # unev stores the type name of expr
    AssignMstmt('unev', OpMxpr('get_expr_type', [RegMxpr('expr')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('SequenceExpr'))])),
    BranchMstmt(LabelMxpr('ev-sequence')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('SymbolExpr'))])),
    BranchMstmt(LabelMxpr('ev-symbol')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('StringExpr'))])),
    BranchMstmt(LabelMxpr('ev-string')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('NumberExpr'))])),
    BranchMstmt(LabelMxpr('ev-number')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('BooleanExpr'))])),
    BranchMstmt(LabelMxpr('ev-boolean')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('NilExpr'))])),
    BranchMstmt(LabelMxpr('ev-nil')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('QuoteExpr'))])),
    BranchMstmt(LabelMxpr('ev-quote')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('LambdaExpr'))])),
    BranchMstmt(LabelMxpr('ev-lambda')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('CallExpr'))])),
    BranchMstmt(LabelMxpr('ev-call')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('IfExpr'))])),
    BranchMstmt(LabelMxpr('ev-if')),
    # put expression type in val, then goto error
    AssignMstmt('val', OpMxpr('ec_eval_expr_invalid', [RegMxpr('expr')])),
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
    AssignMstmt('val', OpMxpr('pure_eval_lambda_plain', [RegMxpr('expr'), RegMxpr('env')])),
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-symbol'),
    AssignMstmt('val', OpMxpr('ec_eval_symbol', [RegMxpr('expr'), RegMxpr('env')])),
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
    AssignMstmt('unev2', OpMxpr('-', [RegMxpr('unev2'), ConstMxpr(NumberVal(1))])),
    # init unev3 = 0
    AssignMstmt('unev3', ConstMxpr(NumberVal(0))),
  LabelMstmt('ev-sequence-fronts'),
    TestMstmt(OpMxpr('=', [RegMxpr('unev3'), RegMxpr('unev2')])),
    BranchMstmt(LabelMxpr('ev-sequence-last')),
    SaveMstmt('unev'),
    SaveMstmt('unev2'),
    SaveMstmt('unev3'),
    SaveMstmt('env'),
    AssignMstmt('expr', OpMxpr('get_expr_at', [RegMxpr('unev'), RegMxpr('unev3')])),
    AssignMstmt('continue', LabelMxpr('ev-sequence-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-sequence-ret'),
    RestoreMstmt('env'),
    RestoreMstmt('unev3'),
    RestoreMstmt('unev2'),
    RestoreMstmt('unev'),
    AssignMstmt('unev3', OpMxpr('+', [RegMxpr('unev3'), ConstMxpr(NumberVal(1))])),
    GotoMstmt(LabelMxpr('ev-sequence-fronts')),
    # support for tail recursion: ensure goto eval-dispatch is the last instruction
    # to do that, can't save/restore for env/unev/unev2/unev3
    # and should restore continue before call rather than after
  LabelMstmt('ev-sequence-last'),
    AssignMstmt('expr', OpMxpr('get_expr_at', [RegMxpr('unev'), RegMxpr('unev3')])),
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
    # getting operands
    # we still do save/restore for the last operand
    # this has a little performance lost, but do not destroy tail recursion
    AssignMstmt('proc', RegMxpr('val')),
    # each time we must create a new empty list
    # therefore we must call op init_val_list
    # we cannot assign from a const [], otherwise that [] will be mutated and reused
    # an alternative solution is to not mutate to [], instead every append create a new one
    AssignMstmt('argl', OpMxpr('init_val_list', [])),
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
    AssignMstmt('expr', OpMxpr('get_expr_at', [RegMxpr('unev'), RegMxpr('unev3')])),
    AssignMstmt('continue', LabelMxpr('ev-call-operand-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-call-operand-ret'),
    RestoreMstmt('argl'),
    RestoreMstmt('unev3'),
    RestoreMstmt('unev2'),
    RestoreMstmt('unev'),
    RestoreMstmt('env'),
    # the evil list mutation, because of this argl must be recreated from op in every call
    PerformMstmt(OpMxpr('append_val_list', [RegMxpr('argl'), RegMxpr('val')])),
    AssignMstmt('unev3', OpMxpr('+', [RegMxpr('unev3'), ConstMxpr(NumberVal(1))])),
    GotoMstmt(LabelMxpr('ev-call-operand-start')),
    # calling body, need proc, and argl is already correct
  LabelMstmt('ev-call-call'),
    RestoreMstmt('proc'),
    RestoreMstmt('expr'),
    RestoreMstmt('continue'),
    AssignMstmt('unev', OpMxpr('get_val_type', [RegMxpr('proc')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('ProcPlainVal'))])),
    BranchMstmt(LabelMxpr('ev-call-proc-plain')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('PrimVal'))])),
    BranchMstmt(LabelMxpr('ev-call-prim')),
    AssignMstmt('val', OpMxpr('ec_eval_call_invalid', [RegMxpr('expr'), RegMxpr('proc')])),
    GotoMstmt(LabelMxpr('error-unknown-operator-type')),

  LabelMstmt('ev-call-proc-plain'),
    AssignMstmt('val', OpMxpr('ec_check_proc_arity', [RegMxpr('expr'), RegMxpr('proc'), RegMxpr('argl')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('val'), ConstMxpr(NilVal())])),
    BranchMstmt(LabelMxpr('ev-call-proc-plain-arity-ok')),
    GotoMstmt(LabelMxpr('error-call-arity')),
  LabelMstmt('ev-call-proc-plain-arity-ok'),
    AssignMstmt('env', OpMxpr('pure_eval_call_proc_extend_env', [RegMxpr('proc'), RegMxpr('argl')])),
    AssignMstmt('expr', OpMxpr('get_proc_plain_val_body', [RegMxpr('proc')])),
    GotoMstmt(LabelMxpr('ev-sequence')),

  LabelMstmt('ev-call-prim'),
    AssignMstmt('val', OpMxpr('ec_check_prim_arity', [RegMxpr('expr'), RegMxpr('proc'), RegMxpr('argl')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('val'), ConstMxpr(NilVal())])),
    BranchMstmt(LabelMxpr('ev-call-prim-arity-ok')),
    GotoMstmt(LabelMxpr('error-call-arity')),
  LabelMstmt('ev-call-prim-arity-ok'),
    AssignMstmt('uenv', OpMxpr('call_prim', [RegMxpr('expr'), RegMxpr('proc'), RegMxpr('argl')])),
    AssignMstmt('val', OpMxpr('car', [RegMxpr('uenv')])), 
    TestMstmt(OpMxpr('equal?', [RegMxpr('val'), ConstMxpr(NilVal())])),
    BranchMstmt(LabelMxpr('ev-call-prim-call-ok')),
    GotoMstmt(LabelMxpr('error-call-prim')),
  LabelMstmt('ev-call-prim-call-ok'),
    AssignMstmt('val', OpMxpr('cdr', [RegMxpr('uenv')])), 
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-if'),
    SaveMstmt('continue'),
    SaveMstmt('expr'),
    SaveMstmt('env'),
    AssignMstmt('expr', OpMxpr('get_if_predicate', [RegMxpr('expr')])),
    AssignMstmt('continue', LabelMxpr('ev-if-predicate-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-if-predicate-ret'),
    RestoreMstmt('env'),
    RestoreMstmt('expr'),
    RestoreMstmt('continue'),
    # directly assigning flag, not using test
    # here we assume TestMstmt will call is_truthy, so flag does not have to be boolean
    AssignMstmt('flag', RegMxpr('val')),
    BranchMstmt(LabelMxpr('ev-if-consequent')),
    TestMstmt(OpMxpr('has_if_alternative', [RegMxpr('expr')])),
    BranchMstmt(LabelMxpr('ev-if-alternative')),
    # no alternative
    AssignMstmt('val', ConstMxpr(UndefVal())),
    GotoMstmt(RegMxpr('continue')),
    # tail recursion supported
  LabelMstmt('ev-if-consequent'),
    AssignMstmt('expr', OpMxpr('get_if_consequent', [RegMxpr('expr')])),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-if-alternative'),
    AssignMstmt('expr', OpMxpr('get_if_alternative', [RegMxpr('expr')])),
    GotoMstmt(LabelMxpr('eval-dispatch')),

    # handling of all errors are the same
  LabelMstmt('error-unknown-expression-type'),
  LabelMstmt('error-unknown-operator-type'),
  LabelMstmt('error-symbol-undefined'),
  LabelMstmt('error-call-arity'),
  LabelMstmt('error-call-prim'),
    # just goto_panic, assuming the error message in val 
    PerformMstmt(OpMxpr('goto_panic', [RegMxpr('val')])),
    # following goto not really necessary, since goto_panic will exit execution
    GotoMstmt(LabelMxpr('done')),

  LabelMstmt('done')
]

# fmt: on

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
    except SchemeRuntimeError as err:
        return PairVal(StringVal(str(err)), NilVal())


def ec_eval_expr_invalid(expr: Expression):
    message = 'expression type undefined: %s' % get_expr_type(expr).value
    return StringVal(message)


def ec_eval_call_invalid(expr: CallExpr, operator: SchemeVal):
    try:
        pure_eval_call_invalid(expr, operator)
    except SchemeRuntimeError as err:
        return StringVal(str(err))


def ec_check_prim_arity(expr: CallExpr, operator: PrimVal, operands: List[SchemeVal]):
    try:
        pure_check_prim_arity(expr, operator, operands)
        return NilVal()
    except SchemeRuntimeError as err:
        return StringVal(str(err))


def ec_check_proc_arity(expr: CallExpr, operator: ProcVal, operands: List[SchemeVal]):
    try:
        pure_check_proc_arity(expr, operator, operands)
        return NilVal()
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


def init_val_list():
    ls: List[SchemeVal] = []
    return ls


def append_val_list(vals: List[SchemeVal], val: SchemeVal):
    vals.append(val)


def get_val_type(expr: GenericVal):
    return StringVal(type(expr).__name__)


def call_prim(expr: CallExpr, operator: PrimVal, operands: List[SchemeVal]):
    try:
        return PairVal(NilVal(), operator.body(*operands))
    except SchemePrimError as err:
        rt_err = SchemeRuntimeError(expr.paren, err.message)
        return PairVal(StringVal(str(rt_err)), NilVal())


def get_if_predicate(expr: IfExpr):
    return expr.pred


def get_if_consequent(expr: IfExpr):
    return expr.then_branch


def get_if_alternative(expr: IfExpr):
    return expr.else_branch


def has_if_alternative(expr: IfExpr):
    return BooleanVal(expr.else_branch is not None)


def goto_panic(message: StringVal):
    scheme_panic(message.value)


def install_ec_operations():
    ops = {
        'pure_eval_string': pure_eval_string,
        'pure_eval_number': pure_eval_number,
        'pure_eval_boolean': pure_eval_boolean,
        'pure_eval_nil': pure_eval_nil,
        'pure_eval_quote': pure_eval_quote,
        'pure_eval_lambda_plain': pure_eval_lambda_plain,
        'pure_eval_call_proc_extend_env': pure_eval_call_proc_extend_env,
        'goto_panic': goto_panic,

        'get_expr_type': get_expr_type,
        'get_expr_contents': get_expr_contents,
        'get_exprs_len': get_exprs_len,
        'get_expr_at': get_expr_at,
        'get_call_operator': get_call_operator,
        'get_call_operands': get_call_operands,
        'get_proc_plain_val_body': get_proc_plain_val_body,
        'init_val_list': init_val_list,
        'append_val_list': append_val_list,
        'get_val_type': get_val_type,
        'call_prim': call_prim,
        'get_if_predicate': get_if_predicate,
        'get_if_consequent': get_if_consequent,
        'get_if_alternative': get_if_alternative,
        'has_if_alternative': has_if_alternative,
        'ec_eval_symbol': ec_eval_symbol,
        'ec_eval_expr_invalid': ec_eval_expr_invalid,
        'ec_eval_call_invalid': ec_eval_call_invalid,
        'ec_check_prim_arity': ec_check_prim_arity,
        'ec_check_proc_arity': ec_check_proc_arity,
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
        panic='runtime error at SYMBOL:x in line 1: symbol undefined'
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
    test_one(
        '((lambda (x) (+ x 1)) 2)',
        result='3',
    )
    test_one(
        '(if #t 1 2)',
        result='1',
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

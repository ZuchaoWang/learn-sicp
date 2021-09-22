'''
mixing ec-evaluator and compiler
this is possible because they share regs, environment and most data types

the major difference is on proc value: ProcPlainVal v.s. ProcCompiledVal
the body of the procedure is invoked differently
but fortunately they follow the same convention: inputs = (proc, argl), target = val, linkage = return
so adding them is quite easy

for evaluator to call compiled procedure
just goto ProcCompiledVal.body

for compiled code to call evaluated procedure
just goto proc_plain_entry, which is a special register holding label('ev-call-proc-plain')
'''

from typing import Any, List, Literal, TypedDict
from sicp414_evaluator import CallExpr, SchemePanic, StringVal, Token, UndefVal, install_is_equal_rules, install_parse_expr_rules, install_primitives, install_stringify_expr_rules, install_stringify_value_rules, make_global_env, scheme_flush, stringify_value
from sicp416_resolver import ResDistancesType, install_resolver_rules
from sicp523_simulator import AssignMstmt, BranchMstmt, ConstMxpr, GotoMstmt, LabelMstmt, LabelMxpr, Mstmt, OpMxpr, RegMachine, RegMachineState, RegMxpr, TestMstmt, assemble, get_operations, init_machine_pc, install_assemble_mstmt_rules, install_assemble_mxpr_rules, install_operations, make_machine, make_reg_table, make_run_machine
from sicp524_monitor import install_stringify_mstmt_rules, install_stringify_mxpr_rules
from sicp544_ec_evaluator import ec_eval_code_list, install_operations_ec, prepare_source, print_code_list, stringify_inst_data
from sicp554_compiler import CompileRecurFuncType, CompileTarget, LinkageTag, SchemeCompiledSeq, SchemeLinkage, append_instructions, compile_call_branch, compile_call_invalid, compile_call_operands, compile_call_prim, compile_call_proc_any, compile_call_proc_compiled, compile_expr, compile_label, install_assemble_mxpr_compile_rules, install_compile_rules, install_operations_compile, install_stringify_mxpr_compile_rules, install_stringify_value_compile_rules, make_label, parallel_instructions, preserve_instructions, update_compile_rules

# fmt: off
call_compiled_bt_code_list: List[Mstmt] = [
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('ProcCompiledVal'))])),
    BranchMstmt(LabelMxpr('ev-call-proc-compiled')),
]

call_compiled_app_code_list: List[Mstmt] = [
  LabelMstmt('ev-call-proc-compiled'),
    AssignMstmt('val', OpMxpr('ec_check_proc_arity', [RegMxpr('proc'), RegMxpr('argl')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('val'), ConstMxpr(UndefVal())])),
    BranchMstmt(LabelMxpr('ev-call-proc-compiled-arity-ok')),
    AssignMstmt('unev', OpMxpr('get_paren_token', [RegMxpr('expr')])),
    AssignMstmt('err', OpMxpr('concat_token_message', [RegMxpr('unev'), RegMxpr('val')])),
    GotoMstmt(LabelMxpr('error-handler')),
  LabelMstmt('ev-call-proc-compiled-arity-ok'),
    AssignMstmt('env', OpMxpr('get_proc_env', [RegMxpr('proc')])),
    AssignMstmt('unev', OpMxpr('get_call_parameters', [RegMxpr('proc')])),
    AssignMstmt('unev2', OpMxpr('get_call_arguments', [RegMxpr('proc'), RegMxpr('argl')])),
    AssignMstmt('env', OpMxpr('ec_env_extend', [RegMxpr('env'), RegMxpr('unev'), RegMxpr('unev2')])),
    AssignMstmt('val', OpMxpr('get_proc_compiled_body', [RegMxpr('proc')])),
    GotoMstmt(RegMxpr('val')),
]
# fmt: on

insertion_index_bt = 0
insertion_index_app = 0

for i in range(len(ec_eval_code_list)):
    code = ec_eval_code_list[i]
    if isinstance(code, BranchMstmt) and code.label.name == 'ev-call-prim':
        insertion_index_bt = i-1
    elif isinstance(code, LabelMstmt) and code.name == 'ev-call-prim':
        insertion_index_app = i

mixed_ec_eval_code_list = ec_eval_code_list[0:insertion_index_bt] + \
    call_compiled_bt_code_list + ec_eval_code_list[insertion_index_bt:insertion_index_app] + \
    call_compiled_app_code_list + ec_eval_code_list[insertion_index_app:]


def compile_call_proc_plain(paren: Token, label_proc: str, target: CompileTarget, linkage: SchemeLinkage):
    all_regs = set(['val', 'unev', 'unev2', 'unev3',
                    'proc', 'argl', 'continue', 'env', 'expr'])
    goto_body_seq = SchemeCompiledSeq([
        GotoMstmt(RegMxpr('proc_plain_entry')),
    ], set(['proc_plain_entry']), all_regs)
    return compile_call_proc_any(paren, label_proc, target, goto_body_seq, linkage)


def compile_call_branch_mix(label_proc_compiled: str, label_proc_plain: str, label_prim: str, label_invalid: str):
    return SchemeCompiledSeq([
        AssignMstmt('unev', OpMxpr('get_val_type', [RegMxpr('proc')])),
        TestMstmt(
            OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('ProcCompiledVal'))])),
        BranchMstmt(LabelMxpr(label_proc_compiled)),
        TestMstmt(
            OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('ProcPlainVal'))])),
        BranchMstmt(LabelMxpr(label_proc_plain)),
        TestMstmt(
            OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('PrimVal'))])),
        BranchMstmt(LabelMxpr(label_prim)),
        GotoMstmt(LabelMxpr(label_invalid))
    ], set(['proc']), set(['unev']))


def compile_call_mix(expr: CallExpr, target: CompileTarget, linkage: SchemeLinkage,
                 compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    '''add ProcPlainVal support to original compile_call'''
    operator_seq = compile_recursive(
        expr.operator, 'proc', SchemeLinkage(LinkageTag.NEXT))
    operands_seq = compile_call_operands(expr.operands, compile_recursive)

    label_proc_compiled = make_label('call-proc-compiled')
    label_proc_plain = make_label('call-proc-plain') # added
    label_prim = make_label('call-prim')
    label_invalid = make_label('call-invalid')
    branch_seq = compile_call_branch_mix(label_proc_compiled, label_proc_plain, label_prim, label_invalid) # changed

    label_end = make_label('call-end')
    branch_linkage = SchemeLinkage(
        LinkageTag.GOTO, label_end) if linkage.tag == LinkageTag.NEXT else linkage

    proc_compiled_seq = compile_call_proc_compiled(
        expr.paren, label_proc_compiled, target, branch_linkage)
    proc_plain_seq = compile_call_proc_plain(
        expr.paren, label_proc_plain, target, branch_linkage) # added
    prim_seq = compile_call_prim(
        expr.paren, label_prim, target, branch_linkage)
    invalid_seq = compile_call_invalid(expr.paren, label_invalid)
    body_seq = parallel_instructions(proc_compiled_seq, proc_plain_seq, prim_seq, invalid_seq) # changed

    end_seq = compile_label(label_end)

    final_seq = append_instructions(body_seq, end_seq)
    final_seq = preserve_instructions(
        set(['env', 'proc', 'argl', 'continue']), branch_seq, final_seq)
    final_seq = preserve_instructions(
        set(['env', 'proc', 'continue']), operands_seq, final_seq)
    final_seq = preserve_instructions(
        set(['env', 'continue']), operator_seq, final_seq)
    return final_seq


def install_compile_mix_rules():
    rules = {
        CallExpr: compile_call_mix,
    }
    update_compile_rules(rules)


mixed_regs = {
    'val': None,
    'expr': None,
    'env': None,
    'unev': None,
    'unev2': None,
    'unev3': None,
    'dist': None,
    'err': None,
    'proc': None,
    'argl': None,
    'continue': None,
    'proc_plain_entry': None
}


class MixedSource(TypedDict):
    tag: Literal['eval', 'compiled']
    code: str

def test_one(source_list: List[MixedSource], **kargs: str):
    try:     
        # shared   
        ops = get_operations()
        glbenv = make_global_env()
        stack: List[Any] = []
        regs = make_reg_table(mixed_regs)
        state = RegMachineState(stack, regs, ops)
        execute_machine = make_run_machine(lambda _: False)
        symbol_table_eval, instructions_eval = assemble(mixed_ec_eval_code_list, state)
        machine_eval = RegMachine(state, symbol_table_eval, instructions_eval)
        proc_plain_entry = symbol_table_eval['ev-call-proc-plain']

        for source_obj in source_list:
            if source_obj['tag'] == 'eval':
                source_eval = source_obj['code'].strip()
                print('* source_eval: %s' % source_eval)
                expr_eval, distances_eval = prepare_source(source_eval)
                accu_dist = state.regs['dist']
                accu_dist = {} if accu_dist is None else accu_dist
                accu_dist.update(distances_eval)
                state.regs.update({'env': glbenv, 'expr': expr_eval, 'dist': accu_dist})
                init_machine_pc(machine_eval)
                execute_machine(machine_eval)
            else:
                source_compiled = source_obj['code'].strip()
                print('* source_compiled: %s' % source_compiled)
                expr_compiled, distances_compiled = prepare_source(source_compiled)
                state.regs.update({'env': glbenv, 'proc_plain_entry': proc_plain_entry})
                code_compiled = compile_expr(expr_compiled, distances_compiled).code
                symbol_table_compiled, instructions_compiled = assemble(code_compiled, state)
                machine_compiled = RegMachine(state, symbol_table_compiled, instructions_compiled)
                init_machine_pc(machine_compiled)
                execute_machine(machine_compiled)

        result = machine_eval.state.regs['val']
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


def test_eval_call_compiled():
    test_one([{
        'tag': 'compiled',
        'code': '(define x 1)'
    }, {
        'tag': 'eval',
        'code': 'x'
    }],
      result='1'
    )
    test_one([{
        'tag': 'compiled',
        'code': '''
          (define x 1)
          (define y 2)
          (define (f a b) (+ a b))
      '''
    }, {
        'tag': 'eval',
        'code': '(f x (f y 3))'
    }],
      result='6'
    )
    test_one([{
        'tag': 'compiled',
        'code': '''
          (define (factorial n)
            (if (= n 1)
              1
              (* n (factorial (- n 1)))))
      '''
    }, {
        'tag': 'eval',
        'code': '(factorial 5)'
    }],
      result='120'
    )


def test_compiled_call_eval():
    test_one([{
        'tag': 'eval',
        'code': '(define x 1)'
    }, {
        'tag': 'compiled',
        'code': 'x'
    }],
      result='1'
    )
    test_one([{
        'tag': 'eval',
        'code': '''
          (define x 1)
          (define y 2)
          (define (f a b) (+ a b))
      '''
    }, {
        'tag': 'compiled',
        'code': '(f x (f y 3))'
    }],
      result='6'
    )
    test_one([{
        'tag': 'eval',
        'code': '''
          (define (factorial n)
            (if (= n 1)
              1
              (* n (factorial (- n 1)))))
      '''
    }, {
        'tag': 'compiled',
        'code': '(factorial 5)'
    }],
      result='120'
    )
          

def test_mix():
    test_one([{
        'tag': 'eval',
        'code': '(define (even n) (if (= n 0) #t (odd (- n 1))))'
    }, {
        'tag': 'compiled',
        'code': '(define (odd n) (if (= n 0) #f (even (- n 1))))'
    }, {
        'tag': 'eval',
        'code': '(define x (odd 5))'
    }, {
        'tag': 'compiled',
        'code': '''
          (define y (even 4))
          (and x y)
        '''
    }, ],
      result='#t'
    )


def install_rules():
    install_parse_expr_rules()
    install_stringify_expr_rules()
    install_stringify_value_rules()
    install_is_equal_rules()
    install_resolver_rules()
    install_primitives()
    install_assemble_mxpr_rules()
    install_assemble_mstmt_rules()
    install_stringify_mxpr_rules()
    install_stringify_mstmt_rules()
    install_operations()
    # ec-eval rules
    install_operations_ec()
    # compile rules
    install_assemble_mxpr_compile_rules()
    install_stringify_mxpr_compile_rules()
    install_stringify_value_compile_rules()
    install_operations_compile()
    install_compile_rules()
    # mix rules
    install_compile_mix_rules()


def print_mixed_ec_eval_code_list():
    print('mixed_ec_eval_code_list:')
    print_code_list(mixed_ec_eval_code_list)
    print('----------')


def test():
    test_eval_call_compiled()
    test_compiled_call_eval()
    test_mix()


if __name__ == '__main__':
    install_rules()
    print_mixed_ec_eval_code_list()
    test()

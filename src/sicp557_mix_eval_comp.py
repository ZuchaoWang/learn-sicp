'''mixing ec-evaluator and compiler'''

from typing import List
from sicp414_evaluator import SchemePanic, StringVal, UndefVal, install_is_equal_rules, install_parse_expr_rules, install_primitives, install_stringify_expr_rules, install_stringify_value_rules, make_global_env, scheme_flush, stringify_value
from sicp416_resolver import install_resolver_rules
from sicp523_simulator import AssignMstmt, BranchMstmt, ConstMxpr, GotoMstmt, LabelMstmt, LabelMxpr, Mstmt, OpMxpr, RegMachine, RegMxpr, TestMstmt, assemble, get_operations, init_machine_pc, install_assemble_mstmt_rules, install_assemble_mxpr_rules, install_operations, make_machine, make_run_machine
from sicp524_monitor import install_stringify_mstmt_rules, install_stringify_mxpr_rules
from sicp544_ec_evaluator import ec_eval_code_list, ec_eval_regs, install_operations_ec, prepare_source, print_code_list, stringify_inst_data
from sicp554_compiler import compile_expr, install_assemble_mxpr_compile_rules, install_compile_rules, install_operations_compile, install_stringify_mxpr_compile_rules, install_stringify_value_compile_rules

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


def test_one_eval_call_compiled(source_eval: str, source_compiled: str, **kargs: str):
    # source
    source_eval = source_eval.strip()
    print('* source_eval: %s' % source_eval)
    expr_eval, distances_eval = prepare_source(source_eval)

    source_compiled = source_compiled.strip()
    print('* source_compiled: %s' % source_compiled)
    expr_compiled, distances_compiled = prepare_source(source_compiled)

    try:
        # compile phase
        code = compile_expr(expr_compiled, distances_compiled).code
        ops = get_operations()
        glbenv = make_global_env()
        machine_compiled = make_machine(ec_eval_regs, ops, code)
        machine_compiled.state.regs.update({'env': glbenv})
        execute_machine = make_run_machine(lambda _: False)
        init_machine_pc(machine_compiled)
        execute_machine(machine_compiled)

        # evaluate phase
        symbol_table, instructions = assemble(
            mixed_ec_eval_code_list, machine_compiled.state)
        machine_eval = RegMachine(
            machine_compiled.state, symbol_table, instructions)
        machine_eval.state.regs.update(
            {'expr': expr_eval, 'dist': distances_eval})
        init_machine_pc(machine_eval)
        execute_machine(machine_eval)
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
    test_one_eval_call_compiled(
      source_compiled='(define x 1)',
      source_eval='x',
      result='1'
    )
    test_one_eval_call_compiled(
      source_compiled='''
          (define x 1)
          (define y 2)
          (define (f a b) (+ a b))
      ''',
      source_eval='(f x (f y 3))',
      result='6'
    )
    test_one_eval_call_compiled(
      source_compiled='''
          (define (factorial n)
            (if (= n 1)
              1
              (* n (factorial (- n 1)))))
      ''',
      source_eval='(factorial 5)',
      result='120'
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


def print_mixed_ec_eval_code_list():
    print('mixed_ec_eval_code_list:')
    print_code_list(mixed_ec_eval_code_list)
    print('----------')


def test():
    test_eval_call_compiled()


if __name__ == '__main__':
    install_rules()
    print_mixed_ec_eval_code_list()
    test()

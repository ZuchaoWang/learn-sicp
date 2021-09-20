'''
the strategy to support statistics is to transform its exec function
original exec is wrapped in a new function which add functionalities to original function

the strategy to support breakpoint is to provide should_break function
'''

from typing import Any, Callable, Dict, List, Set, Tuple, Type, TypeVar, cast
from sicp414_evaluator import NumberVal, install_stringify_value_rules, stringify_value
from sicp523_simulator import AssignMstmt, BranchMstmt, ConstMxpr, GenericMstmt, GenericMxpr, GotoMstmt, LabelMstmt, LabelMxpr, Mstmt, Mxpr, OpMxpr, PerformMstmt, RegInst, RegInstPtr, RegMachine, RegMachineCase, RegMachineState, RegMxpr, RestoreMstmt, SaveMstmt, ShouldBreakFuncType, TestMstmt, \
    get_operations, init_machine_pc, install_assemble_mstmt_rules, install_assemble_mxpr_rules, install_operations, make_machine, \
    case_factorial_iter, case_factorial_recur, case_fib_double_recur, make_run_machine, run_machine, step_machine

'''recording statistics of stack and instructions'''


class MachineStatistic:
    def __init__(self):
        self.total_insts = 0
        self.stack_ops = 0
        self.stack_depth = 0


def reset_statistic(statistics: MachineStatistic):
    statistics.total_insts = 0
    statistics.stack_ops = 0
    statistics.stack_depth = 0


def monitor_statistics(instructions: List[RegInst], state: RegMachineState, statistics: MachineStatistic):
    '''third phase assemble, change exec functions'''
    stack = state.stack

    def _monitor_stack():
        statistics.stack_ops += 1
        statistics.stack_depth = max(statistics.stack_depth, len(stack))

    def _monitor_instruction():
        statistics.total_insts += 1

    def _monitor_one(instruction: RegInst):
        '''use this internal function s.t. instruction variable is no longer shared'''
        prev_exec = instruction.exec
        if isinstance(instruction.code, (SaveMstmt, RestoreMstmt)):
            def _exec():
                prev_exec()
                _monitor_stack()
                _monitor_instruction()
            instruction.exec = _exec
        else:
            def _exec():
                prev_exec()
                _monitor_instruction()
            instruction.exec = _exec

    for inst in instructions:
        _monitor_one(inst)


def test_one_statistics(case: RegMachineCase, nrng: Tuple[int, int]):
    ops = get_operations()
    machine = make_machine(case['regs'], ops, case['code'])
    statistics = MachineStatistic()
    monitor_statistics(machine.instructions, machine.state, statistics)
    print('statistics: %s (%d, %d)' % (case['name'], nrng[0], nrng[1]))
    for nval in range(*nrng):
        machine.state.regs.update({'n': NumberVal(nval)})
        reset_statistic(statistics)
        init_machine_pc(machine)
        execute_machine = make_run_machine(lambda _: False)
        execute_machine(machine)
        res = machine.state.regs['val']
        res_str = stringify_value(res)
        print('n = %d, val = %s, total_insts = %d, stack_ops = %d, stack_depth = %d' %
              (nval, res_str, statistics.total_insts, statistics.stack_ops, statistics.stack_depth))
        if case['regs']['n'] == nval:
            assert res_str == case['res_str_expected']
    print('----------')


def test_statistics():
    test_one_statistics(case_factorial_iter, nrng=[1, 10])
    test_one_statistics(case_factorial_recur, nrng=[1, 10])
    test_one_statistics(case_fib_double_recur, nrng=[1, 10])


'''
trace instructions, can be used for debugging
for each executed instruction, it outputs values in regs (except for pc and flag)
then output the pc together with the instruction itself
to do that we need to stringify instructions
see exercise 5.16
'''

TID = TypeVar('TID')  # type of instruction data

StringifyInstDataFuncType = Callable[[TID], str]

StringifyMxprFuncType = Callable[[GenericMxpr, StringifyInstDataFuncType], str]

_stringify_mxpr_rules: Dict[Type, StringifyMxprFuncType] = {}


def update_stringify_mxpr_rules(rules: Dict[Type, StringifyMxprFuncType]):
    _stringify_mxpr_rules.update(rules)


def stringify_mxpr(expr: Mxpr, stringify_inst_data: StringifyInstDataFuncType):
    f = _stringify_mxpr_rules[type(expr)]
    return f(expr, stringify_inst_data)


def stringify_mxpr_const(expr: ConstMxpr, stringify_inst_data: StringifyInstDataFuncType):
    return '(const %s)' % stringify_inst_data(expr.value)


def stringify_mxpr_reg(expr: RegMxpr, stringify_inst_data: StringifyInstDataFuncType):
    return '(reg %s)' % expr.name


def stringify_mxpr_label(expr: LabelMxpr, stringify_inst_data: StringifyInstDataFuncType):
    return '(label %s)' % expr.name


def stringify_mxpr_op(expr: OpMxpr, stringify_inst_data: StringifyInstDataFuncType):
    return '(op %s %s)' % (expr.operator, ' '.join([stringify_mxpr(subexpr, stringify_inst_data) for subexpr in expr.operands]))


def install_stringify_mxpr_rules():
    rules = {
        ConstMxpr: stringify_mxpr_const,
        RegMxpr: stringify_mxpr_reg,
        LabelMxpr: stringify_mxpr_label,
        OpMxpr: stringify_mxpr_op
    }
    update_stringify_mxpr_rules(rules)


StringifyMstmtFuncType = Callable[[
    GenericMstmt, StringifyInstDataFuncType], str]

_stringify_mstmt_rules: Dict[Type, StringifyMstmtFuncType] = {}


def update_stringify_mstmt_rules(rules: Dict[Type, StringifyMstmtFuncType]):
    _stringify_mstmt_rules.update(rules)


def stringify_mstmt(stmt: Mstmt, stringify_inst_data: StringifyInstDataFuncType):
    f = _stringify_mstmt_rules[type(stmt)]
    return f(stmt, stringify_inst_data)


def stringify_mstmt_assign(stmt: AssignMstmt, stringify_inst_data: StringifyInstDataFuncType):
    return '(assign %s %s)' % (stmt.name, stringify_mxpr(stmt.value, stringify_inst_data))


def stringify_mstmt_perform(stmt: PerformMstmt, stringify_inst_data: StringifyInstDataFuncType):
    return '(perform %s)' % stringify_mxpr(stmt.value, stringify_inst_data)


def stringify_mstmt_test(stmt: TestMstmt, stringify_inst_data: StringifyInstDataFuncType):
    return '(test %s)' % stringify_mxpr(stmt.value, stringify_inst_data)


def stringify_mstmt_branch(stmt: BranchMstmt, stringify_inst_data: StringifyInstDataFuncType):
    return '(branch %s)' % stringify_mxpr(stmt.label, stringify_inst_data)


def stringify_mstmt_goto(stmt: GotoMstmt, stringify_inst_data: StringifyInstDataFuncType):
    return '(goto %s)' % stringify_mxpr(stmt.dest, stringify_inst_data)


def stringify_mstmt_save(stmt: SaveMstmt, stringify_inst_data: StringifyInstDataFuncType):
    return '(save %s)' % stmt.name


def stringify_mstmt_restore(stmt: RestoreMstmt, stringify_inst_data: StringifyInstDataFuncType):
    return '(restore %s)' % stmt.name


def stringify_mstmt_label(stmt: LabelMstmt, stringify_inst_data: StringifyInstDataFuncType):
    return '%s' % stmt.name


def install_stringify_mstmt_rules():
    rules = {
        AssignMstmt: stringify_mstmt_assign,
        PerformMstmt: stringify_mstmt_perform,
        TestMstmt: stringify_mstmt_test,
        BranchMstmt: stringify_mstmt_branch,
        GotoMstmt: stringify_mstmt_goto,
        SaveMstmt: stringify_mstmt_save,
        RestoreMstmt: stringify_mstmt_restore,
        LabelMstmt: stringify_mstmt_label,
    }
    update_stringify_mstmt_rules(rules)


def trace_stringify(state: RegMachineState, stringify_inst_data: StringifyInstDataFuncType):
    outputs: List[str] = []
    for reg_name in state.regs:
        if reg_name != 'pc' and state.regs[reg_name] is not None:
            outputs.append('  %s = %s' %
                  (reg_name, stringify_inst_data(state.regs[reg_name])))
    pc: RegInstPtr = state.regs['pc']
    if pc.index < len(pc.insts):
        inst = pc.insts[pc.index]
        outputs.append('@ pc = %d (%d): %s' %
              (pc.index, id(pc.insts), stringify_mstmt(inst.code, stringify_inst_data)))
    else:
        outputs.append('@ pc = %d (%d): <end>' % (pc.index, id(pc.insts)))
    return outputs


class TraceState:
    def __init__(self):
        self.outputs: List[str] = []


def reset_trace(ts: TraceState):
    ts.outputs = []


def trace_machine(instructions: List[RegInst], state: RegMachineState, stringify_inst_data: StringifyInstDataFuncType, ts: TraceState):
    def _trace_one(inst: RegInst):
        prev_exec = inst.exec
        def _exec():
            ts.outputs.extend(trace_stringify(state, stringify_inst_data))
            prev_exec()
        inst.exec = _exec

    for inst in instructions:
        _trace_one(inst)


def test_trace():
    case = case_factorial_iter
    print('trace: %s' % case['name'])
    ops = get_operations()
    machine = make_machine(case['regs'], ops, case['code'])
    tstate = TraceState()
    trace_machine(machine.instructions, machine.state, stringify_value, tstate)
    init_machine_pc(machine)
    execute_machine = make_run_machine(lambda _: False)
    execute_machine(machine)
    print('\n'.join(tstate.outputs))
    res = machine.state.regs['val']
    res_str = stringify_value(res)
    assert res_str == case['res_str_expected']
    print('----------')


'''
setting up breakpoints on machine
see exercise 5.19
'''


class MachineBreakpoints:
    '''
    one code position can be specified in different ways, and we treat them as one breakpoint
    all breakpoints are indexed as {id(insts) : set(index)}
    here we use python's id to identify an instruction list

    if language does not provide such id, we need to generate unique id in assemble
    and each instruction list should have such id
    '''

    def __init__(self):
        self.breakpoints: Dict[int, Set[int]] = {}


def translate_breakpoint(symbol_table: Dict[str, RegInstPtr], name: str, offset: int):
    '''
    a breakpoint is specified by a label and an offset relative to the label
    in this implementation, offset will not count LabelMstmt
    this is easier to implement, but not very user friendly
    '''
    if name in symbol_table:
        label = symbol_table[name]
        index = min(max(0, label.index + offset), len(label.insts)-1)
        return RegInstPtr(label.insts, index)
    else:
        return None


def add_breakpoint(bstate: MachineBreakpoints, symbol_table: Dict[str, RegInstPtr], name: str, offset: int):
    label = translate_breakpoint(symbol_table, name, offset)
    insts_id = id(label.insts)
    if insts_id not in bstate.breakpoints:
        bstate.breakpoints[insts_id] = set()
    bstate.breakpoints[insts_id].add(label.index)


def remove_breakpoint(bstate: MachineBreakpoints, symbol_table: Dict[str, RegInstPtr], name: str, offset: int):
    label = translate_breakpoint(symbol_table, name, offset)
    insts_id = id(label.insts)
    if insts_id in bstate.breakpoints:
        if label.index in bstate.breakpoints[insts_id]:
            bstate.breakpoints[insts_id].remove(label.index)


def check_breakpoint(bstate: MachineBreakpoints, pc: RegInstPtr):
    pc_insts_id = id(pc.insts)
    return (pc_insts_id in bstate.breakpoints) and (pc.index in bstate.breakpoints[pc_insts_id])


def make_proceed_machine(should_break: ShouldBreakFuncType):
    '''
    proceed runs the first instruction regardless of breakpoint
    then run others respecting the breakpoints, just as execute_machine
    '''
    def _process_machine(machine: RegMachine):
        step_machine(machine, lambda _: False)
        run_machine(machine, should_break)
    return _process_machine


def inspect_breakpoints(machine: RegMachine):
    regs = machine.state.regs
    if regs['pc'] is None:
        assert False
    pc = cast(RegInstPtr, regs['pc'])
    n = cast(NumberVal, regs['n']).value
    val = cast(NumberVal, regs['val']).value
    print('n = %d, val = %d, pc.index = %d' % (n, val, pc.index))
    return n, val, pc.index


def test_breakpoints():
    case = case_fib_double_recur
    print('breakpoints: %s (%s)' %
          (case['name'], stringify_value(case['regs']['n'])))
    ops = get_operations()
    machine = make_machine(case['regs'], ops, case['code'])
    bstate = MachineBreakpoints()
    def should_break(pc): return check_breakpoint(bstate, pc)
    execute_machine = make_run_machine(should_break)
    proceed_machine = make_proceed_machine(should_break)

    # setup ok
    add_breakpoint(bstate, machine.symbol_table, 'return-sub-call-2', 1)
    init_machine_pc(machine)
    execute_machine(machine)
    assert inspect_breakpoints(machine) == (1, 0, 14)
    # execute after breakpoint do nothing
    execute_machine(machine)
    assert inspect_breakpoints(machine) == (1, 0, 14)
    proceed_machine(machine)
    assert inspect_breakpoints(machine) == (1, 1, 14)
    proceed_machine(machine)
    assert inspect_breakpoints(machine) == (1, 0, 14)
    proceed_machine(machine)
    assert inspect_breakpoints(machine) == (2, 1, 14)
    # add the second breakpoint, now alternatively stop at two breakpoints
    add_breakpoint(bstate, machine.symbol_table, 'base-case', -1)
    proceed_machine(machine)
    assert inspect_breakpoints(machine) == (2, 3, 16)
    proceed_machine(machine)
    assert inspect_breakpoints(machine) == (1, 0, 14)
    proceed_machine(machine)
    assert inspect_breakpoints(machine) == (1, 1, 16)
    # remove first breakpoint, but using a different specificition
    remove_breakpoint(bstate, machine.symbol_table, 'base-case', -3)
    proceed_machine(machine)
    assert inspect_breakpoints(machine) == (1, 2, 16)
    proceed_machine(machine)
    assert inspect_breakpoints(machine) == (3, 5, 16)
    # remove all breakpoints. then proceed to end
    remove_breakpoint(bstate, machine.symbol_table, 'base-case', -1)
    proceed_machine(machine)
    assert inspect_breakpoints(machine) == (34, 55, 19)


'''testing main code'''


def install_rules():
    install_stringify_value_rules()
    install_assemble_mxpr_rules()
    install_assemble_mstmt_rules()
    install_stringify_mxpr_rules()
    install_stringify_mstmt_rules()
    install_operations()


def test():
    test_statistics()
    test_trace()
    test_breakpoints()


if __name__ == '__main__':
    install_rules()
    test()

'''
the strategy to add monitor to instruction is to transform its exec function
wrapping it in a new function which add functionalities to original function
'''

from typing import List, Tuple
from sicp414_evaluator import NumberVal, install_stringify_value_rules, stringify_value
from sicp523_simulator import RegInst, RegMachineCase, RegMachineState, RestoreMstmt, SaveMstmt, execute_machine, \
    get_operations, install_assemble_mstmt_rules, install_assemble_mxpr_rules, install_operations, make_machine, \
    case_factorial_iter, case_factorial_recur, case_fib_double_recur


class RegStatistic:
    def __init__(self):
        self.total_insts = 0
        self.stack_ops = 0
        self.stack_depth = 0


def monitor_reset(instructions: List[RegInst]):
    '''reset exec to raw_exec'''
    for inst in instructions:
        inst.exec = inst.raw_exec


def monitor_statistics(instructions: List[RegInst], state: RegMachineState, statistics: RegStatistic):
    '''third phase assemble, change exec functions'''
    stack = state.stack

    def _monitor_stack():
        statistics.stack_ops += 1
        statistics.stack_depth = max(statistics.stack_depth, len(stack))

    def _monitor_instruction():
        statistics.total_insts += 1

    def _monitor_one(instruction: RegInst):
        prev_exec = instruction.exec
        if isinstance(instruction.code, (SaveMstmt, RestoreMstmt)):
            def _monitor():
                cont = prev_exec()
                _monitor_stack()
                _monitor_instruction()
                return cont
            instruction.exec = _monitor
        else:
            def _monitor():
                cont = prev_exec()
                _monitor_instruction()
                return cont
            instruction.exec = _monitor

    for inst in instructions:
        _monitor_one(inst)


def test_one_statistics(case: RegMachineCase, nrng: Tuple[int, int]):
    ops = get_operations()
    machine = make_machine(case['regs'], ops, case['code'])
    print('%s: (%d, %d)' % (case['name'], nrng[0], nrng[1]))
    for nval in range(*nrng):
        machine.state.regs.update({'n': NumberVal(nval)})
        statistics = RegStatistic()
        monitor_reset(machine.instructions)
        monitor_statistics(machine.instructions, machine.state, statistics)
        execute_machine(machine)
        res = machine.state.regs['val']
        res_str = stringify_value(res)
        print('n = %d, val = %s, total_insts = %d, stack_ops = %d, stack_depth = %d' %
              (nval, res_str, statistics.total_insts, statistics.stack_ops, statistics.stack_depth))
    print('----------')


def test_statistics():
    test_one_statistics(case_factorial_iter, nrng=[1, 10])
    test_one_statistics(case_factorial_recur, nrng=[1, 10])
    test_one_statistics(case_fib_double_recur, nrng=[1, 10])


def install_rules():
    install_stringify_value_rules()
    install_assemble_mxpr_rules()
    install_assemble_mstmt_rules()
    install_operations()


def test():
    test_statistics()


if __name__ == '__main__':
    install_rules()
    test()

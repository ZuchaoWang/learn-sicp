'''
build a register machine, to execute machine language
notice the machine language is still high level than real assembly
because registers can store complex values, e.g. string, pair (although we haven't tried this)
registers can also store label

we skip the parsing, error checking and code printing parts, because we have done enough of those in chap4
our implementation also use python list instead of linked list to implement instructions for simplicity
thus label can not directly points to instruction, instead our label contains instruction header and index
notice when updating pc label, we should create a new instruction pointer, instead of mutating existing one
mutation may run into trouble when pc value comes from a label, and label is to be used again later
'''

import inspect
from typing import Any, Callable, Dict, List, Tuple, Type, TypeVar, TypedDict, Union, cast

from sicp414_evaluator import NumberVal, install_stringify_value_rules, is_truthy, scheme_panic, stringify_value, \
    prim_op_add, prim_op_sub, prim_op_mul, prim_op_div, prim_op_eq, prim_op_gt, prim_op_lt, prim_equal, prim_length, \
    prim_car, prim_cdr, prim_cons, prim_list, prim_pair, prim_null, prim_display, prim_newline

'''machine language syntax, we will skip parsing and directly provide classes'''


class Mxpr:
    '''machine language expression'''
    pass


class ConstMxpr(Mxpr):
    '''value can be any type, we cannot type it precisely'''

    def __init__(self, value: Any):
        self.value = value


class RegMxpr(Mxpr):
    '''name is register name'''

    def __init__(self, name: str):
        self.name = name


class LabelMxpr(Mxpr):
    '''name is label name'''

    def __init__(self, name: str):
        self.name = name


class OpMxpr(Mxpr):
    def __init__(self, operator: str, operands: List[Union[ConstMxpr, RegMxpr]]):
        self.operator = operator
        self.operands = operands


class Mstmt:
    '''machine language statement'''
    pass


class InstMstmt(Mstmt):
    pass


class AssignMstmt(InstMstmt):
    def __init__(self, name: str, value: Mxpr):
        self.name = name
        self.value = value


class PerformMstmt(InstMstmt):
    def __init__(self, value: OpMxpr):
        self.value = value


class TestMstmt(InstMstmt):
    def __init__(self, value: OpMxpr):
        self.value = value


class BranchMstmt(InstMstmt):
    def __init__(self, label: LabelMxpr):
        self.label = label


class GotoMstmt(InstMstmt):
    def __init__(self, dest: Union[RegMxpr, LabelMxpr]):
        self.dest = dest


class SaveMstmt(InstMstmt):
    def __init__(self, name: str):
        self.name = name


class RestoreMstmt(InstMstmt):
    def __init__(self, name: str):
        self.name = name


class LabelMstmt(Mstmt):
    def __init__(self, name: str):
        self.name = name


'''register machine model'''


class RegInst:
    '''
    exec generated by static analysis at assemble time
    exec may be transformed to add functionalities, used in statistics
    '''

    def __init__(self, code: InstMstmt):
        self.code = code
        self.exec: Callable = lambda: None


class RegInstPtr:
    '''used for label and pc'''

    def __init__(self, insts: List[RegInst], index: int):
        self.insts = insts
        self.index = index


class RegMachineState:
    def __init__(self, stack: List[Any], regs: Dict[str, Any], ops: Dict[str, Callable]):
        self.stack = stack
        self.regs = regs
        self.ops = ops


GenericRegMachineState = TypeVar(
    "GenericRegMachineState", bound=RegMachineState)


class RegMachine:
    def __init__(self, state: RegMachineState, symbol_table: Dict[str, RegInstPtr], instructions: List[RegInst]):
        self.state = state
        self.symbol_table = symbol_table
        self.instructions = instructions


def make_reg_table(custom_regs: Dict[str, Any]):
    regs: Dict[str, Any] = {
        'pc': None,
        'flag': None
    }
    regs.update(custom_regs)
    return regs


'''
assemble performs additional static analysis to increase performance
it turns labels into instruction pointer
instructions into executable
'''


class SchemeAssembleError(Exception):
    def __init__(self, message):
        self.message = message


def assemble(code: List[Mstmt], state: GenericRegMachineState):
    instructions: List[RegInst] = []
    symbol_table: Dict[str, RegInstPtr] = {}
    try:
        '''first pass to construct symbol table'''
        for c in code:
            if isinstance(c, LabelMstmt):
                symbol_table[c.name] = RegInstPtr(
                    instructions, len(instructions))
            elif isinstance(c, InstMstmt):
                '''initially we don't assemble instructions'''
                instructions.append(RegInst(c))
            else:
                raise SchemeAssembleError(
                    'wrong machine statement type %s' % type(c).__name__)
        '''second pass to assemble instructions'''
        for inst in instructions:
            inst.exec = assemble_mstmt(inst.code, symbol_table, state)
        return symbol_table, instructions
    except SchemeAssembleError as err:
        scheme_panic(err.message)


GenericMxpr = TypeVar("GenericMxpr", bound=Mxpr)

AssembleMxprFuncType = Callable[[
    GenericMxpr, Dict[str, RegInstPtr], GenericRegMachineState], Callable]

_assemble_mxpr_rules: Dict[Tuple[Type, Type], AssembleMxprFuncType] = {}


def update_assemble_mxpr_rules(rules: Dict[Tuple[Type, Type], AssembleMxprFuncType]):
    _assemble_mxpr_rules.update(rules)


def assemble_mxpr(mxpr: Mxpr, symbol_table: Dict[str, RegInstPtr], state: GenericRegMachineState):
    func = _assemble_mxpr_rules[type(mxpr), type(state)]
    return func(mxpr, symbol_table, state)


def assemble_mxpr_const(mxpr: ConstMxpr, symbol_table: Dict[str, RegInstPtr], state: RegMachineState):
    '''constant value is ready at assemble time'''
    value = mxpr.value
    return lambda: value


def assemble_mxpr_reg(mxpr: RegMxpr, symbol_table: Dict[str, RegInstPtr], state: RegMachineState):
    '''register value should be calulated at runtime'''
    regs = state.regs
    name = mxpr.name
    return lambda: regs[name]


def assemble_mxpr_label(mxpr: LabelMxpr, symbol_table: Dict[str, RegInstPtr], state: RegMachineState):
    '''label is ready at assemble time'''
    label = symbol_table[mxpr.name]
    return lambda: label


def assemble_mxpr_op(mxpr: OpMxpr, symbol_table: Dict[str, RegInstPtr], state: RegMachineState):
    '''operator is ready at assemble time, but operands at runtime'''
    operator = state.ops[mxpr.operator]
    arity = len(inspect.getfullargspec(operator).args)
    if arity != len(mxpr.operands):
        raise SchemeAssembleError('%s operation need %d arguments, now %d provided' % (
            mxpr.operator, arity, len(mxpr.operands)))
    get_operands = [assemble_mxpr(operand, symbol_table, state)
                    for operand in mxpr.operands]
    return lambda: operator(*[gop() for gop in get_operands])


def install_assemble_mxpr_rules():
    rules = {
        (ConstMxpr, RegMachineState): assemble_mxpr_const,
        (RegMxpr, RegMachineState): assemble_mxpr_reg,
        (LabelMxpr, RegMachineState): assemble_mxpr_label,
        (OpMxpr, RegMachineState): assemble_mxpr_op
    }
    update_assemble_mxpr_rules(rules)


GenericInstMstmt = TypeVar("GenericInstMstmt", bound=InstMstmt)

AssembleMstmtFuncType = Callable[[
    GenericInstMstmt, Dict[str, RegInstPtr], GenericRegMachineState], Callable]

_assemble_mstmt_rules: Dict[Tuple[Type, Type], AssembleMstmtFuncType] = {}


def update_assemble_mstmt_rules(rules: Dict[Tuple[Type, Type], AssembleMstmtFuncType]):
    _assemble_mstmt_rules.update(rules)


def assemble_mstmt(mstmt: InstMstmt, symbol_table: Dict[str, RegInstPtr], state: GenericRegMachineState):
    func = _assemble_mstmt_rules[type(mstmt), type(state)]
    return func(mstmt, symbol_table, state)


def advance_pc(regs: Dict[str, Any]):
    pc: RegInstPtr = regs['pc']
    new_pc = RegInstPtr(pc.insts, pc.index+1)
    regs['pc'] = new_pc


def assemble_mstmt_assign(mstmt: AssignMstmt, symbol_table: Dict[str, RegInstPtr], state: RegMachineState):
    regs = state.regs
    name = mstmt.name
    get_value = assemble_mxpr(mstmt.value, symbol_table, state)

    def run():
        regs[name] = get_value()
        advance_pc(regs)
    return run


def assemble_mstmt_perform(mstmt: PerformMstmt, symbol_table: Dict[str, RegInstPtr], state: RegMachineState):
    regs = state.regs
    perform_op = assemble_mxpr_op(mstmt.value, symbol_table, state)

    def run():
        perform_op()
        advance_pc(regs)
    return run


def assemble_mstmt_test(mstmt: TestMstmt, symbol_table: Dict[str, RegInstPtr], state: RegMachineState):
    regs = state.regs
    get_value = assemble_mxpr_op(mstmt.value, symbol_table, state)

    def run():
        regs['flag'] = get_value()
        advance_pc(regs)
    return run


def assemble_mstmt_branch(mstmt: BranchMstmt, symbol_table: Dict[str, RegInstPtr], state: RegMachineState):
    regs = state.regs
    get_label = assemble_mxpr_label(mstmt.label, symbol_table, state)

    def run():
        if is_truthy(regs['flag']):
            regs['pc'] = get_label()
        else:
            advance_pc(regs)
    return run


def assemble_mstmt_goto(mstmt: GotoMstmt, symbol_table: Dict[str, RegInstPtr], state: RegMachineState):
    regs = state.regs
    get_label = assemble_mxpr(mstmt.dest, symbol_table, state)

    def run():
        regs['pc'] = get_label()
    return run


def assemble_mstmt_save(mstmt: SaveMstmt, symbol_table: Dict[str, RegInstPtr], state: RegMachineState):
    regs = state.regs
    name = mstmt.name
    stack = state.stack

    def run():
        stack.append(regs[name])
        advance_pc(regs)
    return run


def assemble_mstmt_restore(mstmt: RestoreMstmt, symbol_table: Dict[str, RegInstPtr], state: RegMachineState):
    regs = state.regs
    name = mstmt.name
    stack = state.stack

    def run():
        regs[name] = stack.pop()
        advance_pc(regs)
    return run


def install_assemble_mstmt_rules():
    rules = {
        (AssignMstmt, RegMachineState): assemble_mstmt_assign,
        (PerformMstmt, RegMachineState): assemble_mstmt_perform,
        (TestMstmt, RegMachineState): assemble_mstmt_test,
        (BranchMstmt, RegMachineState): assemble_mstmt_branch,
        (GotoMstmt, RegMachineState): assemble_mstmt_goto,
        (SaveMstmt, RegMachineState): assemble_mstmt_save,
        (RestoreMstmt, RegMachineState): assemble_mstmt_restore
    }
    update_assemble_mstmt_rules(rules)


def make_machine(custom_regs: Dict[str, Any], ops: Dict[str, Callable], code: List[Mstmt]):
    stack: List[Any] = []
    regs = make_reg_table(custom_regs)
    state = RegMachineState(stack, regs, ops)
    symbol_table, instructions = assemble(code, state)
    machine = RegMachine(state, symbol_table, instructions)
    return machine


def init_machine_pc(machine: RegMachine):
    regs = machine.state.regs
    regs['pc'] = RegInstPtr(machine.instructions, 0)


ShouldBreakFuncType = Callable[[RegInstPtr], bool]


def step_machine(machine: RegMachine, should_break: ShouldBreakFuncType):
    '''return False if cannot continue'''
    regs = machine.state.regs
    pc = regs['pc']
    assert isinstance(pc, RegInstPtr)
    if pc.index >= len(pc.insts):
        return False
    if should_break(pc):
        return False
    inst = pc.insts[pc.index]
    inst.exec()
    return True


def run_machine(machine: RegMachine, should_break: ShouldBreakFuncType):
    while True:
        contd = step_machine(machine, should_break)
        if not contd:
            break


def make_step_machine(should_break: ShouldBreakFuncType):
    return lambda machine: step_machine(machine, should_break)


def make_run_machine(should_break: ShouldBreakFuncType):
    return lambda machine: run_machine(machine, should_break)


_operations: Dict[str, Callable] = {}


def get_operations():
    return _operations


def update_operations(ops: Dict[str, Callable]):
    _operations.update(ops)


def install_operations():
    prims = {
        '+': prim_op_add,
        '-': prim_op_sub,
        '*': prim_op_mul,
        '/': prim_op_div,
        '=': prim_op_eq,
        '<': prim_op_lt,
        '>': prim_op_gt,
        '>': prim_op_gt,
        'equal?': prim_equal,
        'length': prim_length,
        'car': prim_car,
        'cdr': prim_cdr,
        'cons': prim_cons,
        'list': prim_list,
        'pair?': prim_pair,
        'null?': prim_null,
        'display': prim_display,
        'newline': prim_newline,
    }
    update_operations(prims)


class RegMachineCase(TypedDict):
    name: str
    regs: Dict[str, Any]
    code: List[Mstmt]
    res_str_expected: str


def test_one(case: RegMachineCase):
    ops = get_operations()
    machine = make_machine(case['regs'], ops, case['code'])
    init_machine_pc(machine)
    execute_machine = make_run_machine(lambda _: False)
    execute_machine(machine)
    res = machine.state.regs['val']
    res_str = stringify_value(res)
    print('%s: %s' % (case['name'], res_str))
    assert res_str == case['res_str_expected']


case_add: RegMachineCase = {
    'name': 'add',
    'regs': {'val': None, 'a': NumberVal(0)},
    'code': [
        AssignMstmt('a', ConstMxpr(NumberVal(1))),
        AssignMstmt('val', OpMxpr(
            '+', [RegMxpr('a'), ConstMxpr(NumberVal(2))]))
    ],
    'res_str_expected': '3'
}

case_factorial_iter: RegMachineCase = {
    'name': 'factorial-iter',
    'regs': {'val': None, 'n': NumberVal(5)},
    'code': [
        AssignMstmt('val', ConstMxpr(NumberVal(1))),
        LabelMstmt('loop'),
        TestMstmt(OpMxpr('=', [RegMxpr('n'), ConstMxpr(NumberVal(1))])),
        BranchMstmt(LabelMxpr('done')),
        AssignMstmt('val', OpMxpr(
            '*', [RegMxpr('val'), RegMxpr('n')])),
        AssignMstmt('n', OpMxpr(
            '-', [RegMxpr('n'), ConstMxpr(NumberVal(1))])),
        GotoMstmt(LabelMxpr('loop')),
        LabelMstmt('done')
    ],
    'res_str_expected': '120'
}

case_factorial_recur: RegMachineCase = {
    'name': 'factorial-recur',
    'regs': {'val': None, 'continue': None, 'n': NumberVal(5)},
    'code': [
        AssignMstmt('continue', LabelMxpr('return-all')),
        LabelMstmt('start'),
        TestMstmt(OpMxpr('=', [RegMxpr('n'), ConstMxpr(NumberVal(1))])),
        BranchMstmt(LabelMxpr('base-case')),
        SaveMstmt('n'),
        SaveMstmt('continue'),
        AssignMstmt('n', OpMxpr(
            '-', [RegMxpr('n'), ConstMxpr(NumberVal(1))])),
        AssignMstmt('continue', LabelMxpr('return-sub-call')),
        GotoMstmt(LabelMxpr('start')),
        LabelMstmt('return-sub-call'),
        RestoreMstmt('continue'),
        RestoreMstmt('n'),
        AssignMstmt('val', OpMxpr(
            '*', [RegMxpr('val'), RegMxpr('n')])),
        GotoMstmt(RegMxpr('continue')),
        LabelMstmt('base-case'),
        AssignMstmt('val', ConstMxpr(NumberVal(1))),
        GotoMstmt(RegMxpr('continue')),
        LabelMstmt('return-all')
    ],
    'res_str_expected': '120'
}

case_fib_double_recur: RegMachineCase = {
    'name': 'fib-double-recur',
    'regs': {'val': None, 'continue': None, 'n': NumberVal(10)},
    'code': [
        AssignMstmt('continue', LabelMxpr('return-all')),
        LabelMstmt('start'),
        TestMstmt(OpMxpr('<', [RegMxpr('n'), ConstMxpr(NumberVal(2))])),
        BranchMstmt(LabelMxpr('base-case')),
        SaveMstmt('continue'),
        SaveMstmt('n'),
        AssignMstmt('n', OpMxpr(
            '-', [RegMxpr('n'), ConstMxpr(NumberVal(1))])),
        AssignMstmt('continue', LabelMxpr('return-sub-call-1')),
        GotoMstmt(LabelMxpr('start')),
        LabelMstmt('return-sub-call-1'),
        RestoreMstmt('n'),
        SaveMstmt('val'),
        AssignMstmt('n', OpMxpr(
            '-', [RegMxpr('n'), ConstMxpr(NumberVal(2))])),
        AssignMstmt('continue', LabelMxpr('return-sub-call-2')),
        GotoMstmt(LabelMxpr('start')),
        LabelMstmt('return-sub-call-2'),
        RestoreMstmt('n'),  # prev val -> n, n used as temporary register
        AssignMstmt('val', OpMxpr(
            '+', [RegMxpr('val'), RegMxpr('n')])),
        RestoreMstmt('continue'),
        GotoMstmt(RegMxpr('continue')),
        LabelMstmt('base-case'),
        AssignMstmt('val', RegMxpr('n')),
        GotoMstmt(RegMxpr('continue')),
        LabelMstmt('return-all')
    ],
    'res_str_expected': '55'
}


def test():
    test_one(case_add)
    test_one(case_factorial_iter)
    test_one(case_factorial_recur)
    test_one(case_fib_double_recur)


def install_rules():
    install_stringify_value_rules()
    install_assemble_mxpr_rules()
    install_assemble_mstmt_rules()
    install_operations()


if __name__ == '__main__':
    install_rules()
    test()

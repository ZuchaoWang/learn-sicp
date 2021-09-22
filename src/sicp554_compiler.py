import enum
from typing import Callable, Dict, List, Literal, Optional, Tuple, Type, Set, cast
from sicp414_evaluator import BooleanExpr, CallExpr, DefineProcExpr, DefineVarExpr, Environment, Expression, GenericExpr, NilExpr, NumberExpr, NumberVal, ProcVal, QuoteExpr, SchemePanic, SchemeVal, SequenceExpr, SetExpr, StringExpr, StringVal, SymbolExpr, SymbolVal, Token, UndefVal, install_is_equal_rules, install_parse_expr_rules, install_primitives, install_stringify_expr_rules, install_stringify_value_rules, make_global_env, parse_expr, parse_tokens, pure_eval_boolean, pure_eval_nil, pure_eval_number, pure_eval_quote, pure_eval_string, scan_source, scheme_flush, scheme_panic, stringify_token_full, stringify_value, update_stringify_value_rules
from sicp416_resolver import ResDistancesType, install_resolver_rules, resolve_expr
from sicp523_simulator import AssignMstmt, BranchMstmt, ConstMxpr, GotoMstmt, LabelMstmt, LabelMxpr, Mstmt, Mxpr, OpMxpr, PerformMstmt, RegInstPtr, RegMachineState, RegMxpr, RestoreMstmt, SaveMstmt, TestMstmt, get_operations, init_machine_pc, install_assemble_mstmt_rules, install_assemble_mxpr_rules, install_operations, make_machine, make_run_machine, update_assemble_mxpr_rules, update_operations
from sicp544_ec_evaluator import append_val_list, call_prim, concat_token_message, ec_check_prim_arity, ec_check_proc_arity, ec_env_define, ec_env_extend, ec_env_lookup_at, ec_env_set_at, ec_eval_call_invalid, get_call_arguments, get_call_parameters, get_proc_env, get_val_type, goto_panic, init_val_list, print_code_list, stringify_inst_data
from sicp524_monitor import MachineStatistic, StringifyInstDataFuncType, TraceState, monitor_statistics, install_stringify_mstmt_rules, install_stringify_mxpr_rules, trace_machine, update_stringify_mxpr_rules


class SchemeCompiledSeq:
    def __init__(self, code: List[Mstmt], regs_needed: Set[str], regs_modified: Set[str]):
        self.code = code
        self.regs_needed = regs_needed
        self.regs_modified = regs_modified


def append_two_instructions(seq1: SchemeCompiledSeq, seq2: SchemeCompiledSeq):
    code = seq1.code + seq2.code
    regs_needed = seq1.regs_needed | (seq2.regs_needed - seq1.regs_modified)
    regs_modified = seq1.regs_modified | seq2.regs_modified
    return SchemeCompiledSeq(code, regs_needed, regs_modified)


def append_instructions(*seq_list: SchemeCompiledSeq):
    seq_cur = SchemeCompiledSeq([], set(), set())
    for i in range(len(seq_list)):
        seq_cur = append_two_instructions(seq_cur, seq_list[i])
    return seq_cur


def preserve_two_instructions(regs: Set[str], seq1: SchemeCompiledSeq, seq2: SchemeCompiledSeq):
    regs_preserved = regs & seq1.regs_modified & seq2.regs_needed
    regs_preserved_list = list(regs_preserved)
    save_code = [cast(Mstmt, SaveMstmt(r)) for r in regs_preserved_list]
    restore_code = [cast(Mstmt, RestoreMstmt(r))
                    for r in regs_preserved_list][::-1]
    code = save_code + seq1.code + restore_code + seq2.code
    regs_needed = seq1.regs_needed | (
        seq2.regs_needed - (seq1.regs_modified - regs_preserved))
    regs_modified = (seq1.regs_modified - regs_preserved) | seq2.regs_modified
    return SchemeCompiledSeq(code, regs_needed, regs_modified)


def preserve_instructions(regs: Set[str], *seq_list: SchemeCompiledSeq):
    seq_cur = SchemeCompiledSeq([], set(), set())
    for i in range(len(seq_list)):
        seq_cur = preserve_two_instructions(regs, seq_cur, seq_list[i])
    return seq_cur


def parallel_two_instructions(seq1: SchemeCompiledSeq, seq2: SchemeCompiledSeq):
    code = seq1.code + seq2.code
    regs_needed = seq1.regs_needed | seq2.regs_needed
    regs_modified = seq1.regs_modified | seq2.regs_modified
    return SchemeCompiledSeq(code, regs_needed, regs_modified)


def parallel_instructions(*seq_list: SchemeCompiledSeq):
    seq_cur = SchemeCompiledSeq([], set(), set())
    for i in range(len(seq_list)):
        seq_cur = parallel_two_instructions(seq_cur, seq_list[i])
    return seq_cur


def tack_instructions(seq: SchemeCompiledSeq, body_seq: SchemeCompiledSeq):
    code = seq.code + body_seq.code
    regs_needed = seq.regs_needed
    regs_modified = seq.regs_modified
    return SchemeCompiledSeq(code, regs_needed, regs_modified)


next_label_id = 0


def make_label(label: str):
    global next_label_id
    cur_label_id = next_label_id
    next_label_id += 1
    return '%s-%d' % (label, cur_label_id)


def reset_label():
    global next_label_id
    next_label_id = 0


def compile_label(label: str):
    '''usually this label comes from make_label'''
    return SchemeCompiledSeq([LabelMstmt(label)], set(), set())


@enum.unique
class LinkageTag(enum.Enum):
    NEXT = enum.auto()
    RETURN = enum.auto()
    GOTO = enum.auto()


class SchemeLinkage:
    def __init__(self, tag: LinkageTag, label: Optional[str] = None):
        self.tag = tag
        self.label = label


def compile_linkage(linkage: SchemeLinkage):
    if linkage.tag == LinkageTag.NEXT:
        return SchemeCompiledSeq([], set(), set())
    elif linkage.tag == LinkageTag.RETURN:
        return SchemeCompiledSeq([GotoMstmt(RegMxpr('continue'))], set(['continue']), set())
    else:
        assert linkage.tag == LinkageTag.GOTO
        return SchemeCompiledSeq([GotoMstmt(LabelMxpr(cast(str, linkage.label)))], set(), set())


def end_with_linkage(linkage: SchemeLinkage, seq: SchemeCompiledSeq):
    return preserve_instructions(set(['continue']), seq, compile_linkage(linkage))


def compile_error_call(reg_error: str, token: Token):
    label_no_error = make_label('no-error')
    code = [
        TestMstmt(
            OpMxpr('equal?', [RegMxpr(reg_error), ConstMxpr(UndefVal())])),
        BranchMstmt(LabelMxpr(label_no_error)),
        AssignMstmt('err', OpMxpr('concat_token_message', [
                    ConstMxpr(token), RegMxpr(reg_error)])),
        GotoMstmt(LabelMxpr('error-handler')),
        LabelMstmt(label_no_error)
    ]
    '''although it modifies val in case of error, the regs_modified here only concerns the case of no error, thus empty'''
    return SchemeCompiledSeq(code, set([reg_error]), set())


def compile_error_lib(linkage: SchemeLinkage):
    code = [
        LabelMstmt('error-handler'),
        PerformMstmt(OpMxpr('goto_panic', [RegMxpr('err')])),
    ]
    seq = SchemeCompiledSeq(code, set(['err']), set())
    return end_with_linkage(linkage, seq)


CompileTarget = Literal['val', 'proc']


def compile_const(value: SchemeVal, target: CompileTarget, linkage: SchemeLinkage):
    seq = SchemeCompiledSeq(
        [AssignMstmt(target, ConstMxpr(value))], set(), set([target]))
    return end_with_linkage(linkage, seq)


class SchemeCompileError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self) -> str:
        return 'runtime error at %s in line %d: %s' % (stringify_token_full(self.token), self.token.line+1, self.message)


CompileRecurFuncType = Callable[[
    GenericExpr, CompileTarget, SchemeLinkage], SchemeCompiledSeq]
CompileFuncType = Callable[[GenericExpr, CompileTarget, SchemeLinkage,
                            CompileRecurFuncType, ResDistancesType], SchemeCompiledSeq]

_compile_rules: Dict[Type, CompileFuncType] = {}


def update_compile_rules(rules: Dict[Type, CompileFuncType]):
    _compile_rules.update(rules)


def compile_expr(expr: GenericExpr, distances: ResDistancesType):
    reset_label()
    label_main = 'main'  # cannot use make_label, otherwise become main-0
    label_done = make_label('done')
    lkg_done = SchemeLinkage(LinkageTag.GOTO, label_done)
    seq_main = compile_label(label_main)
    seq_expr_no_lib = compile_expr_no_lib(expr, 'val', lkg_done, distances)
    seq_err_lib = compile_error_lib(lkg_done)
    seq_done = compile_label(label_done)
    return parallel_instructions(seq_main, seq_expr_no_lib, seq_err_lib, seq_done)


def compile_expr_no_lib(expr: GenericExpr, target: CompileTarget, linkage: SchemeLinkage, distances: ResDistancesType):
    def compile_recursive(expr: GenericExpr, target: CompileTarget, linkage: SchemeLinkage) -> SchemeCompiledSeq:
        f = _compile_rules[type(expr)]
        return f(expr, target, linkage, compile_recursive, distances)

    try:
        res = compile_recursive(expr, target, linkage)
    except SchemeCompileError as err:
        scheme_panic(str(err))
    return res


def compile_symbol(expr: SymbolExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    dist = NumberVal(distances[expr])
    name_val = StringVal(expr.name.literal)
    token = expr.name
    env_seq = SchemeCompiledSeq([
        AssignMstmt('val', OpMxpr('ec_env_lookup_at', [
                    RegMxpr('env'), ConstMxpr(dist), ConstMxpr(name_val)])),
        AssignMstmt('unev', OpMxpr('car', [RegMxpr('val')])),
    ], set(['env']), set(['val', 'unev']))
    error_seq = compile_error_call('unev', token)
    ret_seq = SchemeCompiledSeq([AssignMstmt(target, OpMxpr(
        'cdr', [RegMxpr('val')]))], set(['val']), set([target]))
    '''env_seq modified val and unev, then pass unev to error_seq, if no error then pass val to ret_seq'''
    return end_with_linkage(linkage, append_instructions(env_seq, error_seq, ret_seq))


def compile_set(expr: SetExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    dist = NumberVal(distances[expr])
    name_val = StringVal(expr.name.literal)
    token = expr.name
    init_seq = compile_recursive(
        expr.initializer, target, SchemeLinkage(LinkageTag.NEXT))
    env_seq = SchemeCompiledSeq([
        AssignMstmt('unev', OpMxpr('ec_env_set_at', [
                    RegMxpr('env'), ConstMxpr(dist), ConstMxpr(name_val), RegMxpr(target)])),
    ], set(['env', target]), set(['unev']))
    error_seq = compile_error_call('unev', token)
    return end_with_linkage(linkage, append_instructions(init_seq, env_seq, error_seq))


def compile_define_any(name: Token, source: str, target: CompileTarget):
    '''assuming input is in val'''
    assert source != 'env'
    env_seq = SchemeCompiledSeq([
        PerformMstmt(OpMxpr('ec_env_define', [
            RegMxpr('env'), ConstMxpr(StringVal(name.literal)), RegMxpr(source)])),
    ], set(['env', source]), set())
    symbol = SymbolVal(name.literal)
    ret_seq = SchemeCompiledSeq(
        [AssignMstmt(target, ConstMxpr(symbol))], set(), set([target]))
    return append_instructions(env_seq, ret_seq)


def compile_define_var(expr: DefineVarExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    init_seq = compile_recursive(
        expr.initializer, 'val', SchemeLinkage(LinkageTag.NEXT))
    def_seq = compile_define_any(expr.name, 'val', target)
    return end_with_linkage(linkage, append_instructions(init_seq, def_seq))


def compile_string(expr: StringExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    return compile_const(pure_eval_string(expr), target, linkage)


def compile_number(expr: NumberExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    return compile_const(pure_eval_number(expr), target, linkage)


def compile_boolean(expr: BooleanExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    return compile_const(pure_eval_boolean(expr), target, linkage)


def compile_nil(expr: NilExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    return compile_const(pure_eval_nil(), target, linkage)


def compile_quote(expr: QuoteExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    return compile_const(pure_eval_quote(expr), target, linkage)


def compile_sequence(expr: SequenceExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    '''
    all contents use the same target, all use next linkage except the last use input linkage
    the last content already fire the linkage, so no need to call end_with_linkage; otherwise may return twice
    '''
    contents = expr.contents
    contents_count = len(contents)
    lkg_next = SchemeLinkage(LinkageTag.NEXT)
    if contents_count == 0:
        return compile_const(UndefVal(), target, linkage)
    else:
        seq_list = [compile_recursive(contents[i], target, lkg_next) for i in range(contents_count-1)] + \
            [compile_recursive(contents[-1], target, linkage)]
        seq_front = preserve_instructions(set(['env']), *seq_list[:-1])
        return preserve_instructions(
            set(['env', 'continue']), seq_front, seq_list[-1])


class ProcMxpr(Mxpr):
    '''
    this is the proc mxpr, whose body is a label str, not a RegInstPtr
    '''

    def __init__(self, name: str, pos_paras: List[str], rest_para: Optional[str], body: str):
        self.name = name
        self.pos_paras = pos_paras
        self.rest_para = rest_para
        self.body = body


class ProcStaticVal(SchemeVal):
    '''
    this is the static representation of proc value
    it's assembled from ProcMxpr, turning its body from a label str into a RegInstPtr
    it doesn't have env, because env is only available at runtime, requiring an op
    '''

    def __init__(self, name: str, pos_paras: List[str], rest_para: Optional[str], body: RegInstPtr):
        self.name = name
        self.pos_paras = pos_paras
        self.rest_para = rest_para
        self.body = body


class ProcCompiledVal(ProcVal):
    '''
    this is the runtime representation of proc value
    it gains env from op
    '''

    def __init__(self, name: str, pos_paras: List[str], rest_para: Optional[str], body: RegInstPtr, env: Environment):
        super().__init__(name, pos_paras, rest_para, env)
        self.body = body


def assemble_mxpr_proc(mxpr: ProcMxpr, symbol_table: Dict[str, RegInstPtr], state: RegMachineState):
    '''label value is ready at assemble time'''
    name = mxpr.name
    pos_paras = mxpr.pos_paras
    rest_para = mxpr.rest_para
    body_entry = symbol_table[mxpr.body]
    return lambda: ProcStaticVal(name, pos_paras, rest_para, body_entry)


def make_proc_compiled(proc: ProcStaticVal, env: Environment):
    '''this is an operation, it combines static proc and runtime env'''
    return ProcCompiledVal(proc.name, proc.pos_paras, proc.rest_para, proc.body, env)


def get_proc_compiled_body(proc: ProcCompiledVal):
    '''this is an operation, because call finds its proc at runtime'''
    return proc.body


def stringify_mxpr_proc(expr: ProcMxpr, stringify_inst_data: StringifyInstDataFuncType):
    pos_para_str = ' '.join(expr.pos_paras)
    full_para_str = '%s . %s' % (
        pos_para_str, expr.rest_para) if expr.rest_para is not None else pos_para_str
    return '(proc %s (%s) %s)' % (expr.name, full_para_str, expr.body)


def stringify_value_procedure_static(sv: ProcStaticVal):
    return '[procedure-static %s]' % sv.name


def compile_define_proc_parameters(expr: DefineProcExpr, target: CompileTarget, body_label: str, end_label: str):
    name: str = expr.name.literal
    pos_paras = [s.literal for s in expr.pos_paras]
    rest_para = expr.rest_para.literal if expr.rest_para is not None else None
    return SchemeCompiledSeq([
        AssignMstmt(target, ProcMxpr(name, pos_paras, rest_para, body_label)),
        AssignMstmt(target, OpMxpr('make_proc_compiled',
                                   [RegMxpr(target), RegMxpr('env')])),
        GotoMstmt(LabelMxpr(end_label)) # jump over body instructions
    ], set(['env']), set([target]))


def compile_define_proc_body(expr: DefineProcExpr, body_label: str, compile_recursive: CompileRecurFuncType):
    body_label_seq = SchemeCompiledSeq([
        LabelMstmt(body_label),
    ], set([]), set([]))
    body_code_seq = compile_recursive(
        expr.body, 'val', SchemeLinkage(LinkageTag.RETURN))
    return append_instructions(body_label_seq, body_code_seq)


def compile_define_proc_value(expr: DefineProcExpr, target: CompileTarget, compile_recursive: CompileRecurFuncType):
    body_label = make_label('proc-body')
    end_label = make_label('proc-end')
    para_seq = compile_define_proc_parameters(expr, target, body_label, end_label)
    body_seq = compile_define_proc_body(expr, body_label, compile_recursive)
    end_seq = compile_label(end_label)
    return append_instructions(tack_instructions(para_seq, body_seq), end_seq)


def compile_define_proc_compiled(expr: DefineProcExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    proc_value_seq = compile_define_proc_value(expr, 'val', compile_recursive)
    def_seq = compile_define_any(expr.name, 'val', target)
    return end_with_linkage(linkage, append_instructions(proc_value_seq, def_seq))


def compile_call_operands(operands: List[Expression], compile_recursive: CompileRecurFuncType):
    init_seq = SchemeCompiledSeq(
        [AssignMstmt('argl', OpMxpr('init_val_list', []))], set(), set(['argl']))

    collect_sub_seqs = []
    for operand in operands:
        get_seq = compile_recursive(
            operand, 'val', SchemeLinkage(LinkageTag.NEXT))
        # mutating argl does not mean modifying argl
        append_seq = SchemeCompiledSeq([PerformMstmt(OpMxpr('append_val_list', [
            RegMxpr('argl'), RegMxpr('val')]))], set(['argl', 'val']), set())
        collect_sub_seq = preserve_instructions(
            set(['argl']), get_seq, append_seq)
        collect_sub_seqs.append(collect_sub_seq)
    collect_seq = preserve_instructions(
        set(['argl', 'env']), *collect_sub_seqs)

    return append_instructions(init_seq, collect_seq)


def compile_call_branch(label_proc: str, label_prim: str, label_invalid: str):
    return SchemeCompiledSeq([
        AssignMstmt('unev', OpMxpr('get_val_type', [RegMxpr('proc')])),
        TestMstmt(
            OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('ProcCompiledVal'))])),
        BranchMstmt(LabelMxpr(label_proc)),
        TestMstmt(
            OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('PrimVal'))])),
        BranchMstmt(LabelMxpr(label_prim)),
        GotoMstmt(LabelMxpr(label_invalid))
    ], set(['proc']), set(['unev']))


def compile_call_proc_arity(paren: Token):
    check_seq = SchemeCompiledSeq([
        AssignMstmt('unev', OpMxpr('ec_check_proc_arity',
                                   [RegMxpr('proc'), RegMxpr('argl')])),
    ], set(['proc', 'argl']), set(['unev']))
    error_seq = compile_error_call('unev', paren)
    return append_instructions(check_seq, error_seq)


def compile_call_proc_env():
    return SchemeCompiledSeq([
        AssignMstmt('env', OpMxpr('get_proc_env', [RegMxpr('proc')])),
        AssignMstmt('unev', OpMxpr('get_call_parameters', [RegMxpr('proc')])),
        AssignMstmt('unev2', OpMxpr('get_call_arguments',
                                    [RegMxpr('proc'), RegMxpr('argl')])),
        AssignMstmt('env', OpMxpr('ec_env_extend', [
                    RegMxpr('env'), RegMxpr('unev'), RegMxpr('unev2')])),
    ], set(['proc', 'argl', 'env']), set(['unev', 'unev2', 'env']))


def compile_call_proc_apply(target: CompileTarget, linkage: SchemeLinkage):
    assert linkage.tag != LinkageTag.NEXT
    # we don't know which proc is called, so potentially every reg can change
    # including pc and flag, but no need to list them here
    # this relates to tail recursion, so we use special processing, instead of end_with_linkage
    all_regs = set(['val', 'unev', 'unev2', 'unev3',
                    'proc', 'argl', 'continue', 'env'])
    if target == 'val' and linkage.tag == LinkageTag.RETURN:
        return SchemeCompiledSeq([
            AssignMstmt('val', OpMxpr(
                'get_proc_compiled_body', [RegMxpr('proc')])),
            GotoMstmt(RegMxpr('val')),
        ], set(['proc']), all_regs)
    elif target == 'val' and linkage.tag == LinkageTag.GOTO:
        return SchemeCompiledSeq([
            AssignMstmt('continue', LabelMxpr(cast(str, linkage.label))),
            AssignMstmt('val', OpMxpr(
                'get_proc_compiled_body', [RegMxpr('proc')])),
            GotoMstmt(RegMxpr('val')),
        ], set(['proc']), all_regs)
    elif target != 'val' and linkage.tag == LinkageTag.GOTO:
        '''only happens for call operator, and linkage should be a next, turned into goto'''
        label_ret = make_label('call-proc-ret')
        return SchemeCompiledSeq([
            AssignMstmt('continue', LabelMxpr(label_ret)),
            AssignMstmt('val', OpMxpr(
                'get_proc_compiled_body', [RegMxpr('proc')])),
            GotoMstmt(RegMxpr('val')),
            LabelMstmt(label_ret),
            AssignMstmt(target, RegMxpr('val')),
            GotoMstmt(LabelMxpr(cast(str, linkage.label)))
        ], set(['proc']), all_regs)
    else:
        assert False


def compile_call_proc(paren: Token, label_proc: str, target: CompileTarget, linkage: SchemeLinkage):
    label_seq = compile_label(label_proc)
    arity_seq = compile_call_proc_arity(paren)
    env_seq = compile_call_proc_env()
    apply_seq = compile_call_proc_apply(target, linkage)
    return append_instructions(label_seq, arity_seq, env_seq, apply_seq)


def compile_call_prim_arity(paren: Token):
    check_seq = SchemeCompiledSeq([
        AssignMstmt('unev', OpMxpr('ec_check_prim_arity',
                                   [RegMxpr('proc'), RegMxpr('argl')])),
    ], set(['proc', 'argl']), set(['unev']))
    error_seq = compile_error_call('unev', paren)
    return append_instructions(check_seq, error_seq)


def compile_call_prim_apply(paren: Token, target: CompileTarget, linkage: SchemeLinkage):
    apply_seq = SchemeCompiledSeq([
        AssignMstmt('val', OpMxpr(
            'call_prim', [RegMxpr('proc'), RegMxpr('argl')])),
        AssignMstmt('unev', OpMxpr('car', [RegMxpr('val')])),
    ], set(['proc', 'argl']), set(['val', 'unev']))
    error_seq = compile_error_call('unev', paren)
    value_seq = SchemeCompiledSeq([
        AssignMstmt(target, OpMxpr('cdr', [RegMxpr('val')])),
    ], set(['val']), set([target]))
    return end_with_linkage(linkage, append_instructions(apply_seq, error_seq, value_seq))


def compile_call_prim(paren: Token, label_prim: str, target: CompileTarget, linkage: SchemeLinkage):
    label_seq = compile_label(label_prim)
    arity_seq = compile_call_prim_arity(paren)
    apply_seq = compile_call_prim_apply(paren, target, linkage)
    return append_instructions(label_seq, arity_seq, apply_seq)


def compile_call_invalid(paren: Token, label_invalid: str):
    '''error must invoke, so no more sequence after error_seq'''
    label_seq = compile_label(label_invalid)
    check_seq = SchemeCompiledSeq([
        AssignMstmt('unev', OpMxpr('ec_eval_call_invalid', [RegMxpr('proc')]))
    ], set(['proc']), set(['unev']))
    error_seq = compile_error_call('unev', paren)
    return append_instructions(label_seq, check_seq, error_seq)


def compile_call(expr: CallExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    operator_seq = compile_recursive(
        expr.operator, 'proc', SchemeLinkage(LinkageTag.NEXT))
    operands_seq = compile_call_operands(expr.operands, compile_recursive)

    label_proc = make_label('call-proc-compiled')
    label_prim = make_label('call-prim')
    label_invalid = make_label('call-invalid')
    branch_seq = compile_call_branch(label_proc, label_prim, label_invalid)

    label_end = make_label('call-end')
    branch_linkage = SchemeLinkage(
        LinkageTag.GOTO, label_end) if linkage.tag == LinkageTag.NEXT else linkage

    proc_seq = compile_call_proc(
        expr.paren, label_proc, target, branch_linkage)
    prim_seq = compile_call_prim(
        expr.paren, label_prim, target, branch_linkage)
    invalid_seq = compile_call_invalid(expr.paren, label_invalid)
    body_seq = parallel_instructions(proc_seq, prim_seq, invalid_seq)

    end_seq = compile_label(label_end)

    final_seq = append_instructions(body_seq, end_seq)
    final_seq = preserve_instructions(
        set(['env', 'proc', 'argl', 'continue']), branch_seq, final_seq)
    final_seq = preserve_instructions(
        set(['env', 'proc', 'continue']), operands_seq, final_seq)
    final_seq = preserve_instructions(
        set(['env', 'continue']), operator_seq, final_seq)
    return final_seq


def install_compile_rules():
    rules = {
        SymbolExpr: compile_symbol,
        StringExpr: compile_string,
        NumberExpr: compile_number,
        BooleanExpr: compile_boolean,
        NilExpr: compile_nil,
        QuoteExpr: compile_quote,
        SetExpr: compile_set,
        DefineVarExpr: compile_define_var,
        DefineProcExpr: compile_define_proc_compiled,
        SequenceExpr: compile_sequence,
        CallExpr: compile_call
    }
    update_compile_rules(rules)


def install_operations_compile():
    ops = {
        'pure_eval_string': pure_eval_string,
        'pure_eval_number': pure_eval_number,
        'pure_eval_boolean': pure_eval_boolean,
        'pure_eval_nil': pure_eval_nil,
        'pure_eval_quote': pure_eval_quote,
        'goto_panic': goto_panic,
        'concat_token_message': concat_token_message,

        'ec_env_lookup_at': ec_env_lookup_at,
        'ec_env_set_at': ec_env_set_at,
        'ec_env_define': ec_env_define,
        'ec_env_extend': ec_env_extend,
        'get_val_type': get_val_type,
        'init_val_list': init_val_list,
        'append_val_list': append_val_list,
        'get_proc_env': get_proc_env,
        'get_call_parameters': get_call_parameters,
        'get_call_arguments': get_call_arguments,
        'ec_check_prim_arity': ec_check_prim_arity,
        'ec_check_proc_arity': ec_check_proc_arity,
        'ec_eval_call_invalid': ec_eval_call_invalid,
        'call_prim': call_prim,

        'make_proc_compiled': make_proc_compiled,
        'get_proc_compiled_body': get_proc_compiled_body,
    }
    update_operations(ops)


def install_assemble_mxpr_compile_rules():
    rules = {ProcMxpr: assemble_mxpr_proc}
    update_assemble_mxpr_rules(rules)


def install_stringify_mxpr_compile_rules():
    rules = {ProcMxpr: stringify_mxpr_proc}
    update_stringify_mxpr_rules(rules)


def install_stringify_value_compile_rules():
    rules = {ProcStaticVal: stringify_value_procedure_static}
    update_stringify_value_rules(rules)


'''
no need for expr and dist
other regs are still necessary
'''
compile_regs = {
    'val': None,
    'env': None,
    'unev': None,
    'unev2': None,
    'unev3': None,
    'err': None,
    'proc': None,
    'argl': None,
    'continue': None
}


def test_one(source: str, **kargs: str):
    # source
    source = source.strip()
    print('* source: %s' % source)

    try:
        try:
            # scan
            tokens = scan_source(source)

            # parse
            combos = parse_tokens(tokens)
            expr = parse_expr(combos)

            # resolve
            distances = resolve_expr(expr)

            # compile
            code = compile_expr(expr, distances).code
            print('compiled code:')
            print_code_list(code)

            # build machine
            ops = get_operations()
            glbenv = make_global_env()
            machine = make_machine(compile_regs, ops, code)
            machine.state.regs.update({'env': glbenv})
            execute_machine = make_run_machine(lambda _: False)

            # trace
            tstate = TraceState()
            trace_machine(machine.instructions, machine.state,
                          stringify_inst_data, tstate)

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
    except Exception as err:
        # print current instruction and regs
        print('\n'.join(tstate.outputs[-100:]))
        raise err
    print('----------')


def test_one_recursion(source_tmpl: str, name: str, nrng: Tuple[int, int], get_val: Callable[[int], int]):
    print('%s (%d, %d)' % (name, nrng[0], nrng[1]))
    source_tmpl = source_tmpl.strip()
    print(source_tmpl)
    for nval in range(*nrng):
        # source
        source = source_tmpl % nval

        try:
            # scan
            tokens = scan_source(source)

            # parse
            combos = parse_tokens(tokens)
            expr = parse_expr(combos)

            # resolve
            distances = resolve_expr(expr)

            # compile
            code = compile_expr(expr, distances).code

            # build machine
            ops = get_operations()
            glbenv = make_global_env()
            machine = make_machine(compile_regs, ops, code)
            statistics = MachineStatistic()
            monitor_statistics(machine.instructions, machine.state, statistics)
            machine.state.regs.update({'env': glbenv})
            execute_machine = make_run_machine(lambda _: False)

            # result
            init_machine_pc(machine)
            execute_machine(machine)
            res = machine.state.regs['val']
            res_str = stringify_value(res)
            assert res_str == str(get_val(nval))

            print('n = %d, val = %s, total_insts = %d, stack_ops = %d, stack_depth = %d' %
                  (nval, res_str, statistics.total_insts, statistics.stack_ops, statistics.stack_depth))

        except SchemePanic as err:
            # any kind of panic
            print('* panic: %s' % err.message)
            assert False
    print('----------')


def test_error():
    test_one(
        'x',
        panic='runtime error at SYMBOL:x in line 1: symbol undefined'
    )
    test_one(
        '''
        (define (f a b . c) c)
        (f 1)
        ''',
        panic='runtime error at LEFT_PAREN in line 2: f expect at least 2 arguments, only get 1'
    )
    test_one(
        '''
        (define f "not_an_op")
        (f 1 2)
        ''',
        panic='runtime error at LEFT_PAREN in line 2: cannot call StringVal value'
    )
    test_one(
        '(+ "1" "2")',
        panic='runtime error at LEFT_PAREN in line 1: <lambda> requires both operators to be numbers, now StringVal and StringVal'
    )


def test_expr():
    test_one(
        '''
        (define x 1)
        2
        "string"
        ()
        #f
        x
        ''',
        result='1'
    )
    return
    test_one(
        '((lambda (x) (+ x 1)) 2)',
        result='3',
    )
    test_one(
        '''
        (define (f x) (+ x 1))
        (f 2)
        ''',
        result='3',
    )
    test_one(
        '(if #t (if 3 4) 2)',
        result='4',
    )
    test_one(
        '(and (+ 1 2) (or (not #t) (list 3 4)))',
        result='(3 4)',
    )
    test_one(
        '''
        (define a 1)
        (define (incr)
          (set! a (+ a 1)))
        (incr)
        (incr)
        ''',
        result='3'
    )
    test_one(
        '''
        (define a '(2 3 4))
        (define b (cons 1 a))
        (display (car b))
        (newline)
        (display (cdr b))
        (newline)
        (display (cdr (cdr b)))
        (length b)
        ''',
        output='1\n(2 3 4)\n(3 4)',
        result='4'
    )


def test_resolve():
    # use before intialization in different scopes pass resolution
    test_one(
        '''
        (define (f)
          (define (g) x)
          (define x 1)
          (g))
        (f)
        ''',
        result='1'
    )
    # local variable shadows outer definitions
    test_one(
        '''
        (define x 1)
        (define (f)
          (define x 2)
          x)
        (f)
        ''',
        result='2'
    )
    # mutual recursion ok, even in local scope
    test_one(
        '''
        (define (f)
          (define (even n) (if (= n 0) #t (odd (- n 1))))
          (define (odd n) (if (= n 0) #f (even (- n 1))))
          (even 5))
        (f)
        ''',
        result='#f'
    )


def factorial(n: int):
    product = 1
    for i in range(1, n+1):
        product *= i
    return product


def test_recursion():
    # recursion
    test_one_recursion(
        '''
        (define (factorial n)
          (if (= n 1)
            1
            (* n (factorial (- n 1)))))
        (factorial %d)
        ''',
        name='factorial-recur',
        nrng=(1, 10),
        get_val=factorial
    )
    # iteration, should use constant stack depth
    test_one_recursion(
        '''
        (define (factorial n)
          (define (fact-iter product counter)
            (if (> counter n)
               product
               (fact-iter (* counter product)
                 (+ counter 1))))
          (fact-iter 1 1))
        (factorial %d)
        ''',
        name='factorial-iter',
        nrng=(1, 10),
        get_val=factorial
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
    # compile rules
    install_assemble_mxpr_compile_rules()
    install_stringify_mxpr_compile_rules()
    install_stringify_value_compile_rules()
    install_operations_compile()
    install_compile_rules()


def test():
    test_error()
    test_expr()
    # test_resolve()
    # test_recursion()


if __name__ == '__main__':
    install_rules()
    test()

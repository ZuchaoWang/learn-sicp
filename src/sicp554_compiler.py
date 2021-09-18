import enum
from typing import Callable, Dict, List, Optional, Type, Set, cast
from sicp414_evaluator import BooleanExpr, GenericExpr, NilExpr, NumberExpr, NumberVal, QuoteExpr, SchemeVal, SequenceExpr, StringExpr, StringVal, SymbolExpr, Token, UndefVal, pure_eval_boolean, pure_eval_nil, pure_eval_number, pure_eval_quote, pure_eval_string, scheme_panic, stringify_token_full, Expression
from sicp416_resolver import ResDistancesType
from sicp523_simulator import AssignMstmt, BranchMstmt, ConstMxpr, GotoMstmt, LabelMstmt, LabelMxpr, Mstmt, OpMxpr, RegMxpr, RestoreMstmt, SaveMstmt, TestMstmt


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
    seq_count = len(seq_list)
    if seq_count == 0:
        return SchemeCompiledSeq([], set(), set())
    elif seq_count == 1:
        return seq_list[0]
    else:
        seq_cur = append_two_instructions(seq_list[0], seq_list[1])
        for i in range(2, seq_count):
            seq_cur = append_two_instructions(seq_cur, seq_list[i])
        return seq_cur


def preserve_instructions(regs: Set[str], seq1: SchemeCompiledSeq, seq2: SchemeCompiledSeq):
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


def parallel_instructions(seq1: SchemeCompiledSeq, seq2: SchemeCompiledSeq):
    code = seq1.code + seq2.code
    regs_needed = seq1.regs_needed | seq2.regs_needed
    regs_modified = seq1.regs_modified | seq2.regs_modified
    return SchemeCompiledSeq(code, regs_needed, regs_modified)


def tack_instructions(seq: SchemeCompiledSeq, body_seq: SchemeCompiledSeq):
    code = seq.code + body_seq.code
    regs_needed = seq.regs_needed
    regs_modified = seq.regs_modified
    return SchemeCompiledSeq(code, regs_needed, regs_modified)


next_label = 0


def make_label(label: str):
    global next_label
    cur_label = next_label
    next_label += 1
    return 'label-%d' % cur_label


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


def compile_error(reg_error: str, token: Token):
    label_no_error = make_label('no-error')
    code = [
        TestMstmt(
            OpMxpr('equal?', [RegMxpr(reg_error), ConstMxpr(UndefVal())])),
        BranchMstmt(LabelMxpr(label_no_error)),
        AssignMstmt('val', OpMxpr('concat_token_message', [
                    ConstMxpr(token), RegMxpr(reg_error)])),
        GotoMstmt(LabelMxpr('error-report')),
        LabelMstmt(label_no_error)
    ]
    '''although it modifies val in case of error, the regs_modified here only concerns the case of no error, thus empty'''
    return SchemeCompiledSeq(code, set(reg_error), set())


def compile_const(value: SchemeVal, target: str, linkage: SchemeLinkage):
    seq = SchemeCompiledSeq([AssignMstmt(target, ConstMxpr(value))], set(), set([target]))
    return end_with_linkage(linkage, seq)


class SchemeCompileError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self) -> str:
        return 'runtime error at %s in line %d: %s' % (stringify_token_full(self.token), self.token.line+1, self.message)


CompileRecurFuncType = Callable[[
    GenericExpr, str, SchemeLinkage], SchemeCompiledSeq]
CompileFuncType = Callable[[GenericExpr, str, SchemeLinkage,
                            CompileRecurFuncType, ResDistancesType], SchemeCompiledSeq]

_compile_rules: Dict[Type, CompileFuncType] = {}


def update_compile_rules(rules: Dict[Type, CompileFuncType]):
    _compile_rules.update(rules)


def compile_expr(expr: GenericExpr, target: str, linkage: SchemeLinkage, distances: ResDistancesType):
    def compile_recursive(expr: GenericExpr, target: str, linkage: SchemeLinkage) -> SchemeCompiledSeq:
        f = _compile_rules[type(expr)]
        return f(expr, target, linkage, compile_recursive, distances)

    try:
        res = compile_recursive(expr, target, linkage)
    except SchemeCompileError as err:
        scheme_panic(str(err))
    return res


def compile_symbol(expr: SymbolExpr, target: str, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    dist = NumberVal(distances[expr])
    name = StringVal(expr.name.literal)
    token = expr.name
    env_seq = SchemeCompiledSeq([
        AssignMstmt('val', OpMxpr('ec_env_lookup_at', [
                    RegMxpr('env'), ConstMxpr(dist), ConstMxpr(name)])),
        AssignMstmt('unev', OpMxpr('car', [RegMxpr('val')])),
    ], set(['env']), set(['val', 'unev']))
    error_seq = compile_error('unev', token)
    ret_seq = SchemeCompiledSeq([AssignMstmt(target, OpMxpr(
        'cdr', [RegMxpr('val')]))], set(['val']), set([target]))
    '''env_seq modified val and unev, then pass unev to error_seq, if no error then pass val to ret_seq'''
    return end_with_linkage(linkage, append_instructions(env_seq, preserve_instructions(set(['val']), error_seq, ret_seq)))


def compile_string(expr: StringExpr, target: str, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    return compile_const(pure_eval_string(expr), target, linkage)


def compile_number(expr: NumberExpr, target: str, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    return compile_const(pure_eval_number(expr), target, linkage)


def compile_boolean(expr: BooleanExpr, target: str, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    return compile_const(pure_eval_boolean(expr), target, linkage)


def compile_nil(expr: NilExpr, target: str, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    return compile_const(pure_eval_nil(), target, linkage)


def compile_quote(expr: QuoteExpr, target: str, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    return compile_const(pure_eval_quote(expr), target, linkage)


def compile_sequence(expr: SequenceExpr, target: str, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    '''all contents use the same target, all use next linkage except the last use input linkage'''
    contents = expr.contents
    content_count = len(contents)
    if content_count == 0:
        return compile_const(UndefVal(), target, linkage)
    elif content_count == 1:
        return compile_recursive(contents[0], target, linkage)
    else:
        seq_cur = preserve_instructions(set(['env', 'continue']))

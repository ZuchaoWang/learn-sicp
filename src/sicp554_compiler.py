import enum
from typing import Callable, Dict, List, Optional, Type, Set, cast
from sicp414_evaluator import NumberVal, SequenceExpr, StringVal, SymbolExpr, Token, UndefVal, scheme_panic, stringify_token_full, Expression
from sicp416_resolver import ResDistancesType
from sicp523_simulator import AssignMstmt, BranchMstmt, ConstMxpr, GotoMstmt, LabelMstmt, LabelMxpr, Mstmt, OpMxpr, RegMxpr, RestoreMstmt, SaveMstmt, TestMstmt

class SchemeCompiledSeq:
    def __init__(self, code: List[Type[Mstmt]], regs_needed: Set[str], regs_modified: Set[str]):
        self.code = code
        self.regs_needed = regs_needed
        self.regs_modified = regs_modified

def append_instructions(seq1: SchemeCompiledSeq, seq2: SchemeCompiledSeq):
    code = seq1.code + seq2.code
    regs_needed = seq1.regs_needed | (seq2.regs_needed - seq1.regs_modified)
    regs_modified = seq1.regs_modified | seq2.regs_modified
    return SchemeCompiledSeq(code, regs_needed, regs_modified)

def preserve_instructions(regs: Set[str], seq1: SchemeCompiledSeq, seq2: SchemeCompiledSeq):
    regs_preserved = regs & seq1.regs_modified & seq2.regs_needed
    regs_preserved_list = list(regs_preserved)
    save_code = [cast(Type[Mstmt], SaveMstmt(r)) for r in regs_preserved_list]
    restore_code = [cast(Type[Mstmt], RestoreMstmt(r)) for r in regs_preserved_list][::-1]
    code = save_code + seq1.code + restore_code + seq2.code
    regs_needed = seq1.regs_needed | (seq2.regs_needed - (seq1.regs_modified - regs_preserved))
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

def make_label(label: str):
    code = cast(List[Type[Mstmt]], [LabelMstmt(label)])
    code = [LabelMstmt(label)]
    return SchemeCompiledSeq(code, set(), set())

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

def compile_error(reg_error: str, no_error_label: str, token: Token):
    code = [
        TestMstmt(OpMxpr('equal?', [RegMxpr(reg_error), ConstMxpr(UndefVal())])),
        BranchMstmt(LabelMxpr(no_error_label)),
        AssignMstmt('val', OpMxpr('concat_token_message', [ConstMxpr(token), RegMxpr('unev')])),
        GotoMstmt(LabelMxpr('error-report')),
    ]

class SchemeCompileError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self) -> str:
        return 'runtime error at %s in line %d: %s' % (stringify_token_full(self.token), self.token.line+1, self.message)


CompileRecurFuncType = Callable[[Type[Expression], str, SchemeLinkage], SchemeCompiledSeq]
CompileFuncType = Callable[[Type[Expression], str, SchemeLinkage, CompileRecurFuncType, ResDistancesType], SchemeCompiledSeq]

_compile_rules: Dict[Type, CompileFuncType] = {}


def update_compile_rules(rules: Dict[Type, CompileFuncType]):
    _compile_rules.update(rules)

def compile_expr(expr: Type[Expression], target: str, linkage: SchemeLinkage, distances: ResDistancesType):
    def compile_recursive(expr: Type[Expression], target: str, linkage: SchemeLinkage) -> SchemeCompiledSeq:
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
    code = [
        AssignMstmt(target, OpMxpr('ec_env_lookup_at', [RegMxpr('env'), ConstMxpr(dist), ConstMxpr(name)])),
        AssignMstmt('unev', OpMxpr('car', [RegMxpr('val')])),
        TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(UndefVal())])),
        BranchMstmt(LabelMxpr('ev-symbol-no-error')),
        AssignMstmt('val', OpMxpr('concat_token_message', [ConstMxpr(token), RegMxpr('unev')])),
        GotoMstmt(LabelMxpr('error-report')),
    ]
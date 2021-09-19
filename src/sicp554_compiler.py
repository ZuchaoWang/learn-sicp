import enum
from typing import Callable, Dict, List, Literal, Optional, Tuple, Type, Set, cast
from sicp414_evaluator import BooleanExpr, DefineVarExpr, GenericExpr, NilExpr, NumberExpr, NumberVal, QuoteExpr, SchemePanic, SchemeVal, SequenceExpr, SetExpr, StringExpr, StringVal, SymbolExpr, SymbolVal, Token, UndefVal, install_is_equal_rules, install_parse_expr_rules, install_primitives, install_stringify_expr_rules, install_stringify_value_rules, make_global_env, parse_expr, parse_tokens, pure_eval_boolean, pure_eval_nil, pure_eval_number, pure_eval_quote, pure_eval_string, scan_source, scheme_flush, scheme_panic, stringify_token_full, stringify_value
from sicp416_resolver import ResDistancesType, install_resolver_rules, resolve_expr
from sicp523_simulator import AssignMstmt, BranchMstmt, ConstMxpr, GotoMstmt, LabelMstmt, LabelMxpr, Mstmt, OpMxpr, PerformMstmt, RegMxpr, RestoreMstmt, SaveMstmt, TestMstmt, get_operations, init_machine_pc, install_assemble_mstmt_rules, install_assemble_mxpr_rules, install_operations, make_machine, make_run_machine, update_operations
from sicp544_ec_evaluator import concat_token_message, ec_env_define, ec_env_extend, ec_env_lookup_at, ec_env_set_at, goto_panic
from sicp524_monitor import MachineStatistic, monitor_statistics


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
    label_main = 'main'  # cannot use make_label, otherwise become main-0
    label_done = make_label('done')
    lkg_done = SchemeLinkage(LinkageTag.GOTO, label_done)
    seq_main = SchemeCompiledSeq([LabelMstmt(label_main)], set(), set())
    seq_expr_no_lib = compile_expr_no_lib(expr, 'val', lkg_done, distances)
    seq_err_lib = compile_error_lib(lkg_done)
    seq_done = SchemeCompiledSeq([LabelMstmt(label_done)], set(), set())
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
    name = StringVal(expr.name.literal)
    token = expr.name
    env_seq = SchemeCompiledSeq([
        AssignMstmt('val', OpMxpr('ec_env_lookup_at', [
                    RegMxpr('env'), ConstMxpr(dist), ConstMxpr(name)])),
        AssignMstmt('unev', OpMxpr('car', [RegMxpr('val')])),
    ], set(['env']), set(['val', 'unev']))
    error_seq = compile_error_call('unev', token)
    ret_seq = SchemeCompiledSeq([AssignMstmt(target, OpMxpr(
        'cdr', [RegMxpr('val')]))], set(['val']), set([target]))
    '''env_seq modified val and unev, then pass unev to error_seq, if no error then pass val to ret_seq'''
    return end_with_linkage(linkage, append_instructions(env_seq, error_seq, ret_seq))


def compile_set(expr: SetExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    dist = NumberVal(distances[expr])
    name = StringVal(expr.name.literal)
    token = expr.name
    init_seq = compile_recursive(
        expr.initializer, target, SchemeLinkage(LinkageTag.NEXT))
    env_seq = SchemeCompiledSeq([
        AssignMstmt('unev', OpMxpr('ec_env_set_at', [
                    RegMxpr('env'), ConstMxpr(dist), ConstMxpr(name), RegMxpr(target)])),
    ], set(['env', target]), set(['unev']))
    error_seq = compile_error_call('unev', token)
    return end_with_linkage(linkage, append_instructions(init_seq, env_seq, error_seq))


def compile_define_var(expr: DefineVarExpr, target: CompileTarget, linkage: SchemeLinkage, compile_recursive: CompileRecurFuncType, distances: ResDistancesType):
    name = StringVal(expr.name.literal)
    symbol = SymbolVal(expr.name.literal)
    init_seq = compile_recursive(
        expr.initializer, 'val', SchemeLinkage(LinkageTag.NEXT))
    env_seq = SchemeCompiledSeq([
        PerformMstmt(OpMxpr('ec_env_define', [
            RegMxpr('env'), ConstMxpr(name), RegMxpr('val')])),
    ], set(['env', 'val']), set())
    ret_seq = SchemeCompiledSeq(
        [AssignMstmt(target, ConstMxpr(symbol))], set(), set([target]))
    return end_with_linkage(linkage, append_instructions(init_seq, env_seq, ret_seq))


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
    '''all contents use the same target, all use next linkage except the last use input linkage'''
    contents = expr.contents
    contents_count = len(contents)
    lkg_next = SchemeLinkage(LinkageTag.NEXT)
    if contents_count == 0:
        return compile_const(UndefVal(), target, linkage)
    else:
        seq_list = [compile_recursive(contents[i], target, lkg_next) for i in range(contents_count-1)] + \
            [compile_recursive(contents[-1], target, linkage)]
        seq_front = preserve_instructions(set(['env']), *seq_list[:-1])
        seq_all = preserve_instructions(
            set(['env', 'continue']), seq_front, seq_list[-1])
        return end_with_linkage(linkage, seq_all)


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
        SequenceExpr: compile_sequence
    }
    update_compile_rules(rules)


def install_ec_operations():
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
    }
    update_operations(ops)


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
    'err': None
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

        # resolve
        distances = resolve_expr(expr)

        # compile
        code = compile_expr(expr, distances).code

        # build machine
        ops = get_operations()
        glbenv = make_global_env()
        machine = make_machine(compile_regs, ops, code)
        machine.state.regs.update({'env': glbenv})
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
    return
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
    install_operations()
    install_ec_operations()
    # compile rules
    install_compile_rules()


def test():
    test_error()
    test_expr()
    # test_resolve()
    # test_recursion()


if __name__ == '__main__':
    install_rules()
    test()

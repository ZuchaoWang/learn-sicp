'''
the goal is to implement query language
compared to that in the book, I parse from raw string and I do extra grammar checking
but I will not implement indexing and instantiate

the parsing is built on sicp414_evaluator, where raw string input is scanned to tokens, then built into token combos
after that token combos are converted into qxpressions (query-expression), and several grammar checkings are performed in qxpression
qxpression contains token information, so that failed grammar checks can refer to tokens in the source code
after that qxpressions are converted to patterns where tokens are stripped off

even with all these checking in qxpressions, we are still missing some erros:
1) when parsed within simple qxpression, and/or/not/lisp-value may be mistakenly considered as normal symbol, not keyword
2) lisp-value predicate related error are reported at runtime

the qeval (query evaluation) takes query, assertions, rules and an initial empty frame as input
where query and assertion are represented directly as patterns
rule is represented as conclusion pattern and body pattern
I don't implement indexing on assertions and rules, so they are each arranged as one long stream
frames are represented as a linked list of bindings
the qeval calculation largely follows the book, except that I don't implement pattern-match
I feel unify-match covers all the functionalities of pattern-match, so I just use unify-match
the result of qeval is a stream of frames, I just print them like ?x=1 without doing full instantiation

the general code structure is that I first implement the simple query
then add each special form: and, or, not, lisp-value
finally do the testing
'''

import inspect
from typing import Callable, Dict, Generic, List, Optional, Set, Type, TypeVar, TypedDict, Union, cast
from sicp331_cycle_detect import LinkedListNode
from sicp414_evaluator import SchemePanic, SchemeParserError, Token, TokenCombo, TokenList, TokenLiteral, TokenQuote, TokenTag, \
    find_type, format_bool, format_float, make_root_token, parse_tokens, scan_source, scheme_panic


class Qxpression:
    def __init__(self, token: Token):
        self.token = token
    '''
    the base class for all query expressions (Qxpression), use class for easier static type checking
    Qxpression will store token for debugging purpose

    although Qxpression and Pattern are very similar
    I want Qxpression to contain token information, and Pattern to not contain token information
    that's why I implemented them seperately, with a lot of efforts
    '''
    pass


GenericQxpr = TypeVar("GenericQxpr", bound=Qxpression)


class SimpleQxpr(Qxpression):
    '''
    simple query expression, useful for type checking
    e.g. ListQxpr can only contain SimpleQxpr
    e.g. rule conclusion can only be SimpleQxpr 
    '''

    def __init__(self, token: Token):
        super().__init__(token)


class StringQxpr(SimpleQxpr):
    def __init__(self, token: Token):
        super().__init__(token)


class NumberQxpr(SimpleQxpr):
    def __init__(self, token: Token):
        super().__init__(token)


class BooleanQxpr(SimpleQxpr):
    def __init__(self, token: Token):
        super().__init__(token)


class ListQxpr(SimpleQxpr):
    def __init__(self, token: Token, contents: List[SimpleQxpr], tail: Optional[SimpleQxpr]):
        super().__init__(token)
        self.contents = contents
        self.tail = tail


class SymbolQxpr(SimpleQxpr):
    def __init__(self, token: Token):
        super().__init__(token)


class VarQxpr(SimpleQxpr):
    def __init__(self, token: Token):
        super().__init__(token)


class SpecialQxpr(Qxpression):
    '''
    base class for special form, used for type checking
    '''

    def __init__(self, token: Token):
        super().__init__(token)


'''
check that the input token combo is valid
that means top level is an non-empty token list
then each level has no quote
finally dot always appear in list and not list head
'''


def check_combo_valid_qxpr(combo: TokenCombo):
    if not isinstance(combo, TokenList):
        raise SchemeParserError(combo.anchor, 'pattern should be list')
    if len(combo.contents) == 0:
        raise SchemeParserError(
            combo.anchor, 'pattern should be non-empty list')
    check_combo_valid_qxpr_recursive(combo)


def check_combo_valid_qxpr_recursive(combo: TokenCombo):
    if isinstance(combo, TokenLiteral):
        if combo.anchor.tag == TokenTag.DOT:
            raise SchemeParserError(
                combo.anchor, 'cannot have free or header dot within pattern')
    elif isinstance(combo, TokenQuote):
        raise SchemeParserError(
            combo.anchor, 'cannot have quote within pattern')
    else:
        assert isinstance(combo, TokenList)
        for (i, subcombo) in enumerate(combo.contents):
            if i == 0 or not isinstance(subcombo, TokenLiteral):
                check_combo_valid_qxpr_recursive(subcombo)


'''parsing simple pattern from token combo, very similar to quote'''


def parse_simple_qxpr_symbol(token: Token):
    name: str = token.literal
    if name.startswith('?'):
        return VarQxpr(token)
    else:
        return SymbolQxpr(token)


def parse_simple_qxpr_string(token: Token):
    return StringQxpr(token)


def parse_simple_qxpr_number(token: Token):
    return NumberQxpr(token)


def parse_simple_qxpr_boolean(token: Token):
    return BooleanQxpr(token)


_parse_simple_qxpr_literal_rules: Dict[TokenTag, Callable[[Token], SimpleQxpr]] = {
    TokenTag.SYMBOL: parse_simple_qxpr_symbol,
    TokenTag.STRING: parse_simple_qxpr_string,
    TokenTag.NUMBER: parse_simple_qxpr_number,
    TokenTag.BOOLEAN: parse_simple_qxpr_boolean,
}


def parse_simple_qxpr_literal(combo: TokenLiteral):
    assert combo.anchor.tag in _parse_simple_qxpr_literal_rules
    f = _parse_simple_qxpr_literal_rules[combo.anchor.tag]
    return f(combo.anchor)


def parse_simple_qxpr_list(combo: TokenList):
    if len(combo.contents) >= 2 and combo.contents[-2].anchor.tag == TokenTag.DOT:
        subqxprs = [parse_simple_qxpr_recursive(subcomb)
                    for subcomb in combo.contents[:-2]]
        lastqxpr = parse_simple_qxpr_recursive(combo.contents[-1])
        return ListQxpr(combo.anchor, subqxprs, lastqxpr)
    else:
        subqxprs = [parse_simple_qxpr_recursive(
            subcomb) for subcomb in combo.contents]
        return ListQxpr(combo.anchor, subqxprs, None)


def parse_simple_qxpr_recursive(combo: TokenCombo) -> SimpleQxpr:
    if isinstance(combo, TokenLiteral):
        return parse_simple_qxpr_literal(combo)
    else:
        assert isinstance(combo, TokenList)
        return parse_simple_qxpr_list(combo)

# we cannot use this to directly parse assertion or query
# otherwise it will simply consider special form keyword (and, or, not, lisp-value) as simple symbol
# we must have knowledge of special form
#
# def parse_simple_qxpr(combo: TokenCombo):
#     try:
#         check_combo_valid_qxpr(combo)
#         assert isinstance(combo, TokenList)
#         return parse_simple_qxpr_list(combo)
#     except SchemeParserError as err:
#         scheme_panic(str(err))


ParseQxprRuleType = Callable[[TokenList], SpecialQxpr]

_parse_qxpr_rules: Dict[str, ParseQxprRuleType] = {}


def parse_qxpr(combo: TokenCombo):
    try:
        check_combo_valid_qxpr(combo)
        assert isinstance(combo, TokenList)
        first_content = combo.contents[0]
        '''first check special form by first symbol'''
        if first_content.anchor.tag == TokenTag.SYMBOL:
            cmd = first_content.anchor.literal
            if cmd in _parse_qxpr_rules:
                f = _parse_qxpr_rules[cmd]
                return f(combo)
        '''default to simple pattern, must be list'''
        return parse_simple_qxpr_list(combo)
    except SchemeParserError as err:
        scheme_panic(str(err))


def update_parse_qxpr_rules(rules: Dict[str, ParseQxprRuleType]):
    _parse_qxpr_rules.update(rules)


'''
in some occassions, an expression forbids certain types of sub-epxression
e.g. assertion cannot have var and special form
e.g. rule-conclusion cannot have special form
check_qxpr_forbid checks this, and will raise error if violated
'''

CheckForbidFuncType = Callable[[GenericQxpr, List[Type]], None]

_check_qxpr_forbid_rules: Dict[Type, CheckForbidFuncType] = {}


def check_qxpr_forbid(qxpr: GenericQxpr, forbid_types: List[Type]):
    try:
        check_qxpr_forbid_recursive(qxpr, forbid_types)
    except SchemeParserError as err:
        scheme_panic(str(err))


def check_qxpr_forbid_recursive(qxpr: GenericQxpr, forbid_types: List[Type]):
    t = find_type(type(qxpr), _check_qxpr_forbid_rules)
    f = _check_qxpr_forbid_rules[t]
    f(qxpr, forbid_types)


def check_qxpr_forbid_self(qxpr: GenericQxpr, forbid_types: List[Type]):
    for ft in forbid_types:
        if isinstance(qxpr, ft):
            raise SchemeParserError(
                qxpr.token, 'pattern type %s forbidden' % ft.__name__)


def check_qxpr_forbid_list(qxpr: ListQxpr, forbid_types: List[Type]):
    check_qxpr_forbid_self(qxpr, forbid_types)
    for subqxpr in qxpr.contents:
        check_qxpr_forbid_recursive(subqxpr, forbid_types)
    if qxpr.tail is not None:
        check_qxpr_forbid_recursive(qxpr.tail, forbid_types)


def update_check_qxpr_forbid_rules(rules: Dict[Type, CheckForbidFuncType]):
    _check_qxpr_forbid_rules.update(rules)


update_check_qxpr_forbid_rules({
    Qxpression: check_qxpr_forbid_self,
    ListQxpr: check_qxpr_forbid_list,
})

'''
certain expression can not have unbounded vars, e.g. not and lisp-value
seen_variables are all variables seen in previous expressions
each not and lisp-value add depth by 1, depth > 0 means we cannot have unbounded var
i.e. variables not in seen_variables
'''

CheckUnboundFuncType = Callable[[GenericQxpr, int, Set[str]], None]

_check_qxpr_unbound_rules: Dict[Type, CheckUnboundFuncType] = {}


def check_qxpr_unbound_recursive(qxpr: GenericQxpr, depth: int, seen_variables: Set[str]):
    t = find_type(type(qxpr), _check_qxpr_unbound_rules)
    f = _check_qxpr_unbound_rules[t]
    f(qxpr, depth, seen_variables)


def check_qxpr_unbound(qxpr: GenericQxpr):
    try:
        check_qxpr_unbound_recursive(qxpr, 0, set())
    except SchemeParserError as err:
        scheme_panic(str(err))


def check_qxpr_unbound_pass(qxpr: GenericQxpr, depth: int, seen_variables: Set[str]):
    pass


def check_qxpr_unbound_var(qxpr: VarQxpr, depth: int, seen_variables: Set[str]):
    name = qxpr.token.literal
    if depth == 0:
        seen_variables.add(name)
    elif name not in seen_variables:
        raise SchemeParserError(qxpr.token, 'unbound variable')


def check_qxpr_unbound_list(qxpr: ListQxpr, depth: int, seen_variables: Set[str]):
    for subqxpr in qxpr.contents:
        check_qxpr_unbound_recursive(subqxpr, depth, seen_variables)
    if qxpr.tail is not None:
        check_qxpr_unbound_recursive(qxpr.tail, depth, seen_variables)


def update_check_qxpr_unbound_rules(rules: Dict[Type, CheckUnboundFuncType]):
    _check_qxpr_unbound_rules.update(rules)


update_check_qxpr_unbound_rules({
    Qxpression: check_qxpr_unbound_pass,
    VarQxpr: check_qxpr_unbound_var,
    ListQxpr: check_qxpr_unbound_list,
})

'''there must be some var in rule and query'''

CheckVarFuncType = Callable[[GenericQxpr], bool]

_check_qxpr_var_rules: Dict[Type, CheckVarFuncType] = {}


def check_qxpr_var(qxpr: GenericQxpr):
    try:
        has_var = check_qxpr_var_recursive(qxpr)
        if not has_var:
            raise SchemeParserError(qxpr.token, 'no variable exist')
    except SchemeParserError as err:
        scheme_panic(str(err))


def check_qxpr_var_recursive(qxpr: GenericQxpr):
    t = find_type(type(qxpr), _check_qxpr_var_rules)
    f = _check_qxpr_var_rules[t]
    return f(qxpr)


def check_qxpr_var_pass(qxpr: GenericQxpr):
    return False


def check_qxpr_var_var(qxpr: VarQxpr):
    return True


def check_qxpr_var_list(qxpr: ListQxpr):
    '''list only need to have var in one of its children expression'''
    for subqxpr in qxpr.contents:
        if check_qxpr_var_recursive(subqxpr):
            return True
    if qxpr.tail is not None:
        if check_qxpr_var_recursive(qxpr.tail):
            return True
    return False


def update_check_qxpr_var_rules(rules: Dict[Type, CheckVarFuncType]):
    _check_qxpr_var_rules.update(rules)


update_check_qxpr_var_rules({
    Qxpression: check_qxpr_var_pass,
    VarQxpr: check_qxpr_var_var,
    ListQxpr: check_qxpr_var_list,
})

'''pattern is runtime object like values'''


class Pattern:
    '''
    base class of pattern
    now static analysis is finished
    no token information remained
    '''


GenericPat = TypeVar("GenericPat", bound=Pattern)


class SimplePat(Pattern):
    '''
    simple pattern, no special form
    can exist in frame
    '''
    pass


GenericSimplePat = TypeVar("GenericSimplePat", bound=SimplePat)


class StringPat(SimplePat):
    def __init__(self, value: str):
        self.value = value


class NumberPat(SimplePat):
    def __init__(self, value: float):
        self.value = value


class BooleanPat(SimplePat):
    def __init__(self, value: bool):
        self.value = value


class NilPat(SimplePat):
    pass


class PairPat(SimplePat):
    '''
    we need pair and nil because this makes matching (?x . ?y) with (a b) easy
    using good old list is not easy to do this
    '''

    def __init__(self, left: SimplePat, right: SimplePat):
        self.left = left
        self.right = right


class SymbolPat(SimplePat):
    def __init__(self, name: str):
        self.name = name


class VarPat(SimplePat):
    def __init__(self, name: str, version: int):
        '''version for renaming'''
        self.name = name
        self.version = version


class SpecialPat(Pattern):
    '''special form pattern'''
    pass


class EmptyPat(Pattern):
    '''used for empty rule body, called always-true in the book'''
    pass


'''pair pattern'''


def pair_from_list_pattern(fronts: List[SimplePat], last: SimplePat):
    head: SimplePat = last
    for i in range(len(fronts)-1, -1, -1):
        head = PairPat(fronts[i], head)
    return head


def pair_to_list_pattern(sv: PairPat):
    fronts: List[SimplePat] = []
    head: SimplePat = sv
    while isinstance(head, PairPat):
        fronts.append(head.left)
        head = head.right
    last = head
    return fronts, last


'''parse patterns'''

ParsePatternFuncType = Callable[[GenericQxpr], Pattern]

_parse_pattern_rules: Dict[Type, ParsePatternFuncType] = {}


def parse_pattern(qxpr: GenericQxpr):
    try:
        return parse_pattern_recursive(qxpr)
    except SchemeParserError as err:
        scheme_panic(str(err))


def parse_pattern_recursive(qxpr: GenericQxpr):
    t = find_type(type(qxpr), _parse_pattern_rules)
    f = _parse_pattern_rules[t]
    return f(qxpr)


def parse_pattern_string(qxpr: StringQxpr):
    return StringPat(qxpr.token.literal)


def parse_pattern_number(qxpr: NumberQxpr):
    return NumberPat(qxpr.token.literal)


def parse_pattern_boolean(qxpr: BooleanQxpr):
    return BooleanPat(qxpr.token.literal)


def parse_pattern_symbol(qxpr: SymbolQxpr):
    return SymbolPat(qxpr.token.literal)


def parse_pattern_var(qxpr: VarQxpr):
    return VarPat(qxpr.token.literal, 0)


def parse_pattern_list(qxpr: ListQxpr):
    fronts = [parse_pattern_recursive(subqxpr)
              for subqxpr in qxpr.contents]
    last = parse_pattern_recursive(
        qxpr.tail) if qxpr.tail is not None else NilPat()
    return pair_from_list_pattern(fronts, last)


def update_parse_pattern_rules(rules: Dict[Type, ParsePatternFuncType]):
    _parse_pattern_rules.update(rules)


update_parse_pattern_rules({
    StringQxpr: parse_pattern_string,
    NumberQxpr: parse_pattern_number,
    BooleanQxpr: parse_pattern_boolean,
    SymbolQxpr: parse_pattern_symbol,
    VarQxpr: parse_pattern_var,
    ListQxpr: parse_pattern_list,
})

'''stringify patterns, very similar to stringify values'''

StringifyPatternFuncType = Callable[[GenericPat], str]

_stringify_pattern_rules: Dict[Type, StringifyPatternFuncType] = {}


def update_stringify_pattern_rules(rules: Dict[Type, StringifyPatternFuncType]):
    _stringify_pattern_rules.update(rules)


def stringify_pattern(pat: GenericPat):
    t = find_type(type(pat), _stringify_pattern_rules)
    f = _stringify_pattern_rules[t]
    return f(pat)


def stringify_pattern_symbol(pat: SymbolPat):
    return pat.name


def stringify_pattern_var(pat: VarPat):
    return pat.name


def stringify_pattern_string(pat: StringPat):
    return '"%s"' % pat.value


def stringify_pattern_number(pat: NumberPat):
    return format_float(pat.value)


def stringify_pattern_boolean(pat: BooleanPat):
    return format_bool(pat.value)


def stringify_pattern_nil(pat: NilPat):
    return '()'


def stringify_pattern_pair(pat: PairPat):
    fronts, last = pair_to_list_pattern(pat)
    left_str = ' '.join([stringify_pattern(subpat) for subpat in fronts])
    if isinstance(last, NilPat):
        return '(%s)' % left_str
    else:
        right_str = stringify_pattern(last)
        return '(%s . %s)' % (left_str, right_str)


def stringify_pattern_empty(pat: EmptyPat):
    return '[empty]'


update_stringify_pattern_rules({
    StringPat: stringify_pattern_string,
    NumberPat: stringify_pattern_number,
    BooleanPat: stringify_pattern_boolean,
    SymbolPat: stringify_pattern_symbol,
    VarPat: stringify_pattern_var,
    NilPat: stringify_pattern_nil,
    PairPat: stringify_pattern_pair,
    EmptyPat: stringify_pattern_empty
})

'''parse assertions, rules, query'''


def parse_assertion(combo: TokenCombo):
    qxpr = parse_qxpr(combo)
    check_qxpr_forbid(qxpr, [SpecialQxpr, VarQxpr])
    assert isinstance(qxpr, ListQxpr)
    pat = parse_pattern(qxpr)
    assert isinstance(pat, SimplePat)
    return pat


def read_all_assertions(source: str):
    tokens = scan_source(source)
    combos = parse_tokens(tokens)
    assertions = [parse_assertion(subcombo) for subcombo in combos]
    return assertions


def parse_query(combo: TokenCombo):
    qxpr = parse_qxpr(combo)
    check_qxpr_unbound(qxpr)
    check_qxpr_var(qxpr)
    pat = parse_pattern(qxpr)
    return pat


def get_single_query(combos: List[TokenCombo]):
    try:
        if len(combos) != 1:
            token = combos[-1].anchor if len(combos) > 1 else make_root_token()
            raise SchemeParserError(token, 'should have exactly one query')
        else:
            return combos[0]
    except SchemeParserError as err:
        scheme_panic(str(err))


def read_single_query(source: str):
    tokens = scan_source(source)
    combos = parse_tokens(tokens)
    single_combo = get_single_query(combos)
    return parse_query(single_combo)


class Rule:
    def __init__(self, conclusion: SimplePat, body: Pattern):
        self.conclusion = conclusion
        self.body = body


def get_rule_contents(combo: TokenCombo):
    try:
        if not isinstance(combo, TokenList):
            raise SchemeParserError(combo.anchor, 'rule should be a list')
        if len(combo.contents) < 2 or len(combo.contents) > 3:
            raise SchemeParserError(
                combo.anchor, 'rule should be a list of 2 or 3 terms')
        if combo.contents[0].anchor.tag != TokenTag.SYMBOL or combo.contents[0].anchor.lexeme != 'rule':
            raise SchemeParserError(
                combo.anchor, 'rule should begin with rule symbol')
        concl_combo = combo.contents[1]
        body_combo = combo.contents[2] if len(combo.contents) == 3 else None
        return concl_combo, body_combo
    except SchemeParserError as err:
        scheme_panic(str(err))


def parse_rule(combo: TokenCombo):
    concl_combo, body_combo = get_rule_contents(combo)
    concl_qxpr = parse_qxpr(concl_combo)
    check_qxpr_forbid(concl_qxpr, [SpecialQxpr])
    assert isinstance(concl_qxpr, ListQxpr)
    check_qxpr_var(concl_qxpr)
    concl_pat = parse_pattern(concl_qxpr)
    assert isinstance(concl_pat, SimplePat)
    if body_combo is not None:
        body_pat = parse_query(body_combo)
    else:
        body_pat = EmptyPat()
    return Rule(concl_pat, body_pat)


def read_all_rules(source: str):
    tokens = scan_source(source)
    combos = parse_tokens(tokens)
    rules = [parse_rule(subcombo) for subcombo in combos]
    return rules


'''
finite stream: FntStream
to hold assertions, rules, frames
rewrite of infinite stream InfStream in sicp352_prime_number
difficult to share the same implementation due to different type checking

notice finite stream can also be infinite, just that we don't assume next() is not None
we implement most operations as functions outside class for easier extension
'''

T = TypeVar('T')


class FntStream(Generic[T]):
    '''
    infinite stream
    easier to implement than possibly finite stream, because no need to check if next is None
    '''

    def __init__(self, head: T, gen_next: Optional[Callable[[], "Optional[FntStream[T]]"]]):
        self.head = head
        self.gen_next = gen_next
        # incorporate memoization within stream, will be used in next()
        self.next_cached = False
        self.next_cached_value: Optional["FntStream[T]"] = None

    def value(self):
        return self.head

    def next(self):
        if self.next_cached is False:
            self.next_cached = True
            if self.gen_next:
                self.next_cached_value = self.gen_next()
        return self.next_cached_value

    def nth_value(self, n: int):
        s = self
        for _ in range(n):
            assert s
            s = s.next()
        return s.value()

    def topn_values(self, n: int):
        values: List[T] = []
        s = self
        for _ in range(n):
            if s is None:
                break
            values.append(s.value())
            s = s.next()
        return values


OptFntStream = Optional[FntStream[T]]


def stream_filter(pred: Callable[[T], bool], s: OptFntStream[T]):
    while s is not None and not pred(s.value()):
        s = s.next()
    if s is None:
        return None
    else:
        def gen_next(): return stream_filter(pred, s.next())
        return FntStream(s.value(), gen_next)


def stream_append_delayed(s1: OptFntStream[T], delayed_s2: Callable[[], OptFntStream[T]]):
    if s1 is None:
        return delayed_s2()
    else:
        def gen_next(): return stream_append_delayed(s1.next(), delayed_s2)
        return FntStream(s1.value(), gen_next)


def stream_interleave_delayed(s1: OptFntStream[T], delayed_s2: Callable[[], OptFntStream[T]]):
    if s1 is None:
        return delayed_s2()
    else:
        def gen_next(): return stream_interleave_delayed(delayed_s2(), lambda: s1.next())
        return FntStream(s1.value(), gen_next)


def stream_flatten(ss: OptFntStream[OptFntStream[T]]):
    if ss is None:
        return None
    else:
        def delayed_rest(): return stream_flatten(ss.next())
        return stream_interleave_delayed(ss.value(), delayed_rest)


S = TypeVar('S')


def stream_map(proc: Callable[[T], S], s: OptFntStream[T]):
    '''this map only assumes one input stream'''
    if s is None:
        return None
    else:
        def gen_next(): return stream_map(proc, s.next())
        return FntStream(proc(s.value()), gen_next)


def stream_from_list(ls: List[T]):
    s: OptFntStream[T] = None
    for i in range(len(ls)-1, -1, -1):
        t = FntStream(ls[i], lambda: s)
        assert t.next() == s  # this force t to remember s
        s = t
    return s


'''
database of assertions and rules
we will just build streams for them
we won't index them, because the indexing in the book seems to assume:
1) all assertions starts with a symbol
2) all rule conclusion either starts with a symbol or a var
but our parsing process does not check these assumptions
it is possible that assertion or rule will start with string, number, bool or list
instead of checking these assumptions during parsing and build index based on these assumptions
we choose to ignore these assumptions, therefore not building the index
'''


def make_assertion_stream(assertions: List[PairPat]):
    return stream_from_list(assertions)


def make_rule_stream(rules: List[Rule]):
    return stream_from_list(rules)


'''
frame is a linked list of bindings
using linked list because one frame may be extended to multiple frames
linked list allow sharing common parent frame via tail chain
'''


class Binding:
    def __init__(self, name: str, version: int, value: SimplePat):
        self.name = name
        self.version = version
        self.value = value


class Frame:
    '''
    frame cannot be a linked list of bindings, it must contain a linked list of bindings
    if Frame = Optional[LinkedListNode[Binding]], then frame = None is ambiguous
    frame = None can be both empty frame, or no frame
    '''
    def __init__(self, bindings: Optional[LinkedListNode[Binding]]):
        self.bindings = bindings


def make_single_frame_stream(frame: Frame):
    '''called singleton-stream in the book'''
    s: FntStream[Frame] = FntStream(frame, None)
    return s


def get_binding_value(frame: Frame, name: str, version: int):
    '''search in the linked list'''
    head = frame.bindings
    while head is not None:
        if head.data.name == name and head.data.version == version:
            return head.data.value
        head = head.next
    return None


def extend_frame(frame: Frame, binding: Binding):
    return Frame(LinkedListNode(binding, frame.bindings))


'''
resolve binding value, like a deep version of get_binding_value
when value is not constant, recursively resolve its value
since binding can only contain simple value, we won't worry about special form
'''

ResolveBindingFuncType = Callable[[Frame, GenericSimplePat], SimplePat]

_resolve_binding_rules: Dict[Type, ResolveBindingFuncType] = {}


def update_resolve_binding_rules(rules: Dict[Type, ResolveBindingFuncType]):
    _resolve_binding_rules.update(rules)


def resolve_binding_value(frame: Frame, name: str, version: int):
    shallow_value = get_binding_value(frame, name, version)
    assert shallow_value is not None
    return resolve_binding_value_recursive(frame, shallow_value)


def resolve_binding_value_recursive(frame: Frame, pat: GenericSimplePat):
    t = find_type(type(pat), _resolve_binding_rules)
    f = _resolve_binding_rules[t]
    return f(frame, pat)


def resolve_binding_value_pass(frame: Frame, pat: GenericSimplePat):
    return pat


def resolve_binding_value_pass_var(frame: Frame, pat: VarPat):
    return resolve_binding_value(frame, pat.name, pat.version)


def resolve_binding_value_pair(frame: Frame, pat: PairPat):
    left_value = resolve_binding_value_recursive(frame, pat.left)
    right_value = resolve_binding_value_recursive(frame, pat.right)
    return PairPat(left_value, right_value)


update_resolve_binding_rules({
    SimplePat: resolve_binding_value_pass,
    VarPat: resolve_binding_value_pass_var,
    PairPat: resolve_binding_value_pair
})


def resolve_final_frame(frame: Frame):
    '''
    get names of vars in original query, excluding those created in rule application (version > 0)
    then resolve these names and get the binding values
    '''
    binding_ls = LinkedListNode.to_list(frame.bindings)
    binding_ls = [b for b in binding_ls if b.version == 0]
    return {b.name: resolve_binding_value(frame, b.name, b.version) for b in binding_ls}


'''rename variable, used in rule application'''

last_global_var_version = 0


def get_next_global_var_version():
    global last_global_var_version
    last_global_var_version += 1
    return last_global_var_version


RenamePatternFuncType = Callable[[GenericPat, int], GenericPat]

_rename_pattern_rules: Dict[Type, RenamePatternFuncType] = {}


def update_rename_pattern_rules(rules: Dict[Type, RenamePatternFuncType]):
    _rename_pattern_rules.update(rules)


def rename_pattern(pat: GenericPat, version: int):
    assert version > 0
    t = find_type(type(pat), _rename_pattern_rules)
    f = _rename_pattern_rules[t]
    return f(pat, version)


def rename_pattern_pass(pat: GenericPat, version: int):
    return pat


def rename_pattern_var(pat: VarPat, version: int):
    return VarPat(pat.name, version)


def rename_pattern_pair(pat: PairPat, version: int):
    return PairPat(rename_pattern(pat.left, version), rename_pattern(pat.right, version))


update_rename_pattern_rules({
    Pattern: rename_pattern_pass,
    VarPat: rename_pattern_var,
    PairPat: rename_pattern_pair,
})

'''check pattern equality'''

IsEqualPatternFuncType = Callable[[GenericPat, GenericPat], bool]

_is_equal_pattern_rules: Dict[Type, IsEqualPatternFuncType] = {}


def update_is_equal_pattern_rules(rules: Dict[Type, IsEqualPatternFuncType]):
    _is_equal_pattern_rules.update(rules)


def is_equal_pattern(pat1: GenericPat, pat2: GenericPat):
    if type(pat1) == type(pat2):
        t = find_type(type(pat1), _is_equal_pattern_rules)
        f = _is_equal_pattern_rules[t]
        return f(pat1, pat2)
    return False


def is_equal_pattern_ref(pat1: GenericPat, pat2: GenericPat):
    return pat1 == pat2


def is_equal_pattern_name(pat1: SymbolPat, pat2: SymbolPat):
    return pat1.name == pat2.name


def is_equal_pattern_value(pat1: Union[StringPat, NumberPat, BooleanPat], pat2: Union[StringPat, NumberPat, BooleanPat]):
    return pat1.value == pat2.value


def is_equal_pattern_var(pat1: VarPat, pat2: VarPat):
    return pat1.name == pat2.name and pat1.version == pat2.version


def is_equal_pattern_true(pat1: GenericPat, pat2: GenericPat):
    return True


update_is_equal_pattern_rules({
    Pattern: is_equal_pattern_ref,
    SymbolPat: is_equal_pattern_name,
    StringPat: is_equal_pattern_value,
    NumberPat: is_equal_pattern_value,
    BooleanPat: is_equal_pattern_value,
    VarPat: is_equal_pattern_var,
    NilPat: is_equal_pattern_true,
    EmptyPat: is_equal_pattern_true,
})

'''
check pattern dependence
since this is only used in extend_if_possible, which only deals with simple value, we won't worry about special form
'''

DependVarPatternFuncType = Callable[[GenericSimplePat, VarPat, Frame], bool]

_depend_var_pattern_rules: Dict[Type, DependVarPatternFuncType] = {}


def update_depend_var_pattern_rules(rules: Dict[Type, DependVarPatternFuncType]):
    _depend_var_pattern_rules.update(rules)


def depend_var_pattern(pat: GenericSimplePat, var: VarPat, frame: Frame):
    t = find_type(type(pat), _depend_var_pattern_rules)
    f = _depend_var_pattern_rules[t]
    return f(pat, var, frame)


def depend_var_pattern_pass(pat: GenericSimplePat, var: VarPat, frame: Frame):
    return False


def depend_var_pattern_var(pat: VarPat, var: VarPat, frame: Frame):
    if is_equal_pattern_var(pat, var):
        return True
    else:
        val = get_binding_value(frame, pat.name, pat.version)
        if val is not None:
            return depend_var_pattern(val, var, frame)
        else:
            return False


def depend_var_pattern_pair(pat: PairPat, var: VarPat, frame: Frame):
    return depend_var_pattern(pat.left, var, frame) or depend_var_pattern(pat.right, var, frame)


update_depend_var_pattern_rules({
    Pattern: depend_var_pattern_pass,
    VarPat: depend_var_pattern_var,
    PairPat: depend_var_pattern_pair
})

'''qeval, this is the core of the whole query language'''

QEvalRuleType = Callable[[GenericPat, OptFntStream[SimplePat],
                          OptFntStream[Rule], OptFntStream[Frame]], OptFntStream[Frame]]

_qeval_rules: Dict[Type, QEvalRuleType] = {}


def qeval_recursive(query: GenericPat, assertions: OptFntStream[SimplePat], rules: OptFntStream[Rule], frames: OptFntStream[Frame]):
    t = find_type(type(query), _qeval_rules)
    f = _qeval_rules[t]
    return f(query, assertions, rules, frames)


def qeval(query: GenericPat, assertions: OptFntStream[SimplePat], rules: OptFntStream[Rule]):
    frames = make_single_frame_stream(Frame(None))
    return qeval_recursive(query, assertions, rules, frames)


def update_qeval_rules(rules: Dict[Type, QEvalRuleType]):
    _qeval_rules.update(rules)


'''simple query qeval'''


def unify_match(pat1: SimplePat, pat2: SimplePat, frame: Frame) -> Optional[Frame]:
    '''
    unify_match assumes both pat1 and pat2 can contain variable
    this covers the functionality of pattern_match, where only pat1 can contain variable
    therefore no need to implement another pattern_match
    '''
    if is_equal_pattern(pat1, pat2):
        return frame
    elif isinstance(pat1, VarPat):
        return extend_if_possible(pat1, pat2, frame)
    elif isinstance(pat2, VarPat):
        return extend_if_possible(pat2, pat1, frame)
    elif isinstance(pat1, PairPat) and isinstance(pat2, PairPat):
        unify_res = unify_match(pat1.left, pat2.left, frame)
        if unify_res is not None:
            return unify_match(pat1.right, pat2.right, unify_res)
    return None


def extend_if_possible(pat1: VarPat, pat2: SimplePat, frame: Frame) -> Optional[Frame]:
    value1 = get_binding_value(frame, pat1.name, pat1.version)
    if value1 is not None:
        return unify_match(value1, pat2, frame)
    elif isinstance(pat2, VarPat):
        value2 = get_binding_value(frame, pat2.name, pat2.version)
        if value2 is not None:
            return unify_match(pat1, value2, frame)
        else:
            return extend_frame(frame, Binding(pat1.name, pat1.version, pat2))
    elif depend_var_pattern(pat2, pat1, frame):
        return None
    else:
        return extend_frame(frame, Binding(pat1.name, pat1.version, pat2))


def find_assertions(query: SimplePat, assertions: OptFntStream[SimplePat], frame: Frame) -> OptFntStream[Frame]:
    def _find_one_assertion(assertion: SimplePat) -> OptFntStream[Frame]:
        unify_res = unify_match(query, assertion, frame)
        return make_single_frame_stream(unify_res) if unify_res is not None else None
    frss = stream_map(_find_one_assertion, assertions)
    return stream_flatten(frss)


def rename_rule(rule: Rule) -> Rule:
    '''
    for each rule application, the whole rule share one version
    this ensures the same variable are renamed identically
    '''
    version = get_next_global_var_version()
    concl_rn = rename_pattern(rule.conclusion, version)
    body_rn = rename_pattern(rule.body, version)
    return Rule(concl_rn, body_rn)


def apply_rules(query: SimplePat, assertions: OptFntStream[SimplePat], rules: OptFntStream[Rule], frame: Frame) -> OptFntStream[Frame]:
    def _apply_one_rule(rule: Rule) -> OptFntStream[Frame]:
        rule_rn = rename_rule(rule)
        unify_res = unify_match(query, rule_rn.conclusion, frame)
        return qeval_recursive(rule_rn.body, assertions, rules, make_single_frame_stream(unify_res)) if unify_res is not None else None
    frss = stream_map(_apply_one_rule, rules)
    return stream_flatten(frss)


def qeval_simple(query: SimplePat, assertions: OptFntStream[SimplePat], rules: OptFntStream[Rule], frames: OptFntStream[Frame]) -> OptFntStream[Frame]:
    def _qeval_one_simple_query(fr: Frame):
        frames_ass = find_assertions(query, assertions, fr)
        def frames_qrl_delayed(): return apply_rules(query, assertions, rules, fr)
        return stream_append_delayed(frames_ass, frames_qrl_delayed)
    frss = stream_map(_qeval_one_simple_query, frames)
    return stream_flatten(frss)


def qeval_empty(query: EmptyPat, assertions: OptFntStream[SimplePat], rules: OptFntStream[Rule], frames: OptFntStream[Frame]) -> OptFntStream[Frame]:
    return frames


update_qeval_rules({
    SimplePat: qeval_simple,
    EmptyPat: qeval_empty,
})

'''special form: and'''


SpecialChildQxpr = Union[SpecialQxpr, ListQxpr]
SpecialChildPat = Union[SpecialPat, PairPat, NilPat]


class AndQxpr(SpecialQxpr):
    def __init__(self, token: Token, contents: List[SpecialChildQxpr]):
        super().__init__(token)
        self.contents = contents


def parse_compound_qxpr_and(combo: TokenList):
    if len(combo.contents) < 3:
        raise SchemeParserError(
            combo.anchor, 'and special form need at least 3 terms')
    contents = [parse_qxpr(subcomb) for subcomb in combo.contents[1:]]
    return AndQxpr(combo.anchor, contents)


def check_qxpr_forbid_and(qxpr: AndQxpr, forbid_types: List[Type]):
    check_qxpr_forbid_self(qxpr, forbid_types)
    for subqxpr in qxpr.contents:
        check_qxpr_forbid_recursive(subqxpr, forbid_types)


def check_qxpr_unbound_and(qxpr: AndQxpr, depth: int, seen_variables: Set[str]):
    for subqxpr in qxpr.contents:
        check_qxpr_unbound_recursive(subqxpr, depth, seen_variables)


def check_qxpr_var_and(qxpr: AndQxpr):
    '''every content must have variable'''
    for subqxpr in qxpr.contents:
        if not check_qxpr_var_recursive(subqxpr):
            raise SchemeParserError(qxpr.token, 'no variable exist')
    return True


class AndPat(SpecialPat):
    def __init__(self, contents: List[SpecialChildPat]):
        self.contents = contents


def parse_special_child_pattern(qxpr: SpecialChildQxpr):
    pat = parse_pattern_recursive(qxpr)
    return cast(SpecialChildPat, pat)


def parse_pattern_and(qxpr: AndQxpr):
    contents = [parse_special_child_pattern(
        subqxpr) for subqxpr in qxpr.contents]
    return AndPat(contents)


def stringify_pattern_and(pat: AndPat):
    contents_str = ' '.join([stringify_pattern(subpat)
                             for subpat in pat.contents])
    return '(and %s)' % contents_str


def rename_pattern_and(pat: AndPat, version: int):
    contents = [rename_pattern(subpat, version) for subpat in pat.contents]
    return AndPat(contents)


def qeval_and(query: AndPat, assertions: OptFntStream[SimplePat], rules: OptFntStream[Rule], frames: OptFntStream[Frame]) -> OptFntStream[Frame]:
    for content in query.contents:
        if frames is None:
            break
        frames = qeval_recursive(content, assertions, rules, frames)
    return frames


def install_special_form_and():
    update_parse_qxpr_rules({'and': parse_compound_qxpr_and})
    update_check_qxpr_forbid_rules({AndQxpr: check_qxpr_forbid_and})
    update_check_qxpr_unbound_rules({AndQxpr: check_qxpr_unbound_and})
    update_check_qxpr_var_rules({AndQxpr: check_qxpr_var_and})
    update_parse_pattern_rules({AndQxpr: parse_pattern_and})
    update_stringify_pattern_rules({AndPat: stringify_pattern_and})
    update_rename_pattern_rules({AndPat: rename_pattern_and})
    update_qeval_rules({AndPat: qeval_and})


'''special form: or'''


class OrQxpr(SpecialQxpr):
    def __init__(self, token: Token, contents: List[SpecialChildQxpr]):
        super().__init__(token)
        self.contents = contents


def parse_compound_qxpr_or(combo: TokenList):
    if len(combo.contents) < 3:
        raise SchemeParserError(
            combo.anchor, 'or special form need at least 3 terms')
    contents = [parse_qxpr(subcomb) for subcomb in combo.contents[1:]]
    return OrQxpr(combo.anchor, contents)


def check_qxpr_forbid_or(qxpr: OrQxpr, forbid_types: List[Type]):
    check_qxpr_forbid_self(qxpr, forbid_types)
    for subqxpr in qxpr.contents:
        check_qxpr_forbid_recursive(subqxpr, forbid_types)


def check_qxpr_unbound_or(qxpr: OrQxpr, depth: int, seen_variables: Set[str]):
    for subqxpr in qxpr.contents:
        check_qxpr_unbound_recursive(subqxpr, depth, seen_variables)


def check_qxpr_var_or(qxpr: OrQxpr):
    '''every content must have variable'''
    for subqxpr in qxpr.contents:
        if not check_qxpr_var_recursive(subqxpr):
            raise SchemeParserError(qxpr.token, 'no variable exist')
    return True


class OrPat(SpecialPat):
    def __init__(self, contents: List[SpecialChildPat]):
        self.contents = contents


def parse_pattern_or(qxpr: OrQxpr):
    contents = [parse_special_child_pattern(subqxpr)
                for subqxpr in qxpr.contents]
    return OrPat(contents)


def stringify_pattern_or(pat: OrPat):
    contents_str = ' '.join([stringify_pattern(subpat)
                             for subpat in pat.contents])
    return '(or %s)' % contents_str


def rename_pattern_or(pat: OrPat, version: int):
    contents = [rename_pattern(subpat, version) for subpat in pat.contents]
    return OrPat(contents)


def qeval_or(query: OrPat, assertions: OptFntStream[SimplePat], rules: OptFntStream[Rule], frames: OptFntStream[Frame]) -> OptFntStream[Frame]:
    def _qeval_or_from(start: int):
        if start == len(query.contents):
            return None
        else:
            headf = qeval_recursive(
                query.contents[start], assertions, rules, frames)

            def restf_delayed(): return _qeval_or_from(start+1)
            return stream_interleave_delayed(headf, restf_delayed)
    return _qeval_or_from(0)


def install_special_form_or():
    update_parse_qxpr_rules({'or': parse_compound_qxpr_or})
    update_check_qxpr_forbid_rules({OrQxpr: check_qxpr_forbid_or})
    update_check_qxpr_unbound_rules({OrQxpr: check_qxpr_unbound_or})
    update_check_qxpr_var_rules({OrQxpr: check_qxpr_var_or})
    update_parse_pattern_rules({OrQxpr: parse_pattern_or})
    update_stringify_pattern_rules({OrPat: stringify_pattern_or})
    update_rename_pattern_rules({OrPat: rename_pattern_or})
    update_qeval_rules({OrPat: qeval_or})


'''special form: not'''


class NotQxpr(SpecialQxpr):
    def __init__(self, token: Token, content: SpecialChildQxpr):
        super().__init__(token)
        self.content = content


def parse_compound_qxpr_not(combo: TokenList):
    if len(combo.contents) != 2:
        raise SchemeParserError(
            combo.anchor, 'not special form need exactly 2 terms')
    content = parse_qxpr(combo.contents[1])
    return NotQxpr(combo.anchor, content)


def check_qxpr_forbid_not(qxpr: NotQxpr, forbid_types: List[Type]):
    check_qxpr_forbid_self(qxpr, forbid_types)
    check_qxpr_forbid_recursive(qxpr.content, forbid_types)


def check_qxpr_unbound_not(qxpr: NotQxpr, depth: int, seen_variables: Set[str]):
    check_qxpr_unbound_recursive(qxpr.content, depth+1, seen_variables)


def check_qxpr_var_not(qxpr: NotQxpr):
    '''content must have variable'''
    if not check_qxpr_var_recursive(qxpr.content):
        raise SchemeParserError(qxpr.token, 'no variable exist')
    return True


class NotPat(SpecialPat):
    def __init__(self, content: SpecialChildPat):
        self.content = content


def parse_pattern_not(qxpr: NotQxpr):
    content = parse_special_child_pattern(qxpr.content)
    return NotPat(content)


def stringify_pattern_not(pat: NotPat):
    content_str = stringify_pattern(pat.content)
    return '(not %s)' % content_str


def rename_pattern_not(pat: NotPat, version: int):
    content = rename_pattern(pat.content, version)
    return NotPat(content)


def qeval_not(query: NotPat, assertions: OptFntStream[SimplePat], rules: OptFntStream[Rule], frames: OptFntStream[Frame]) -> OptFntStream[Frame]:
    def _qeval_not_filter(frame: Frame):
        return qeval_recursive(query, assertions, rules, make_single_frame_stream(frame)) is None
    return stream_filter(_qeval_not_filter, frames)


def install_special_form_not():
    update_parse_qxpr_rules({'not': parse_compound_qxpr_not})
    update_check_qxpr_forbid_rules({NotQxpr: check_qxpr_forbid_not})
    update_check_qxpr_unbound_rules({NotQxpr: check_qxpr_unbound_not})
    update_check_qxpr_var_rules({NotQxpr: check_qxpr_var_not})
    update_parse_pattern_rules({NotQxpr: parse_pattern_not})
    update_stringify_pattern_rules({NotPat: stringify_pattern_not})
    update_rename_pattern_rules({NotPat: rename_pattern_not})
    update_qeval_rules({NotPat: qeval_not})


'''special form: lisp-value'''


class PredQxpr(SpecialQxpr):
    def __init__(self, token: Token, operator: Token, operands: List[SimpleQxpr]):
        super().__init__(token)
        self.operator = operator
        self.operands = operands


def parse_compound_qxpr_pred(combo: TokenList):
    '''notice operands can only be simple qxpressions'''
    if len(combo.contents) < 3:
        raise SchemeParserError(
            combo.anchor, 'lisp-value special form need at least 3 terms')
    if combo.contents[1].anchor.tag != TokenTag.SYMBOL:
        raise SchemeParserError(
            combo.anchor, 'lisp-value special form must have a symbolic operator name')
    operator = combo.contents[1].anchor
    operands = [parse_simple_qxpr_recursive(subqxpr)
                for subqxpr in combo.contents[2:]]
    return PredQxpr(combo.anchor, operator, operands)


def check_qxpr_forbid_pred(qxpr: PredQxpr, forbid_types: List[Type]):
    check_qxpr_forbid_self(qxpr, forbid_types)
    for subqxpr in qxpr.operands:
        check_qxpr_forbid_recursive(subqxpr, forbid_types)


def check_qxpr_unbound_pred(qxpr: PredQxpr, depth: int, seen_variables: Set[str]):
    for subqxpr in qxpr.operands:
        check_qxpr_unbound_recursive(subqxpr, depth+1, seen_variables)


def check_qxpr_var_pred(qxpr: PredQxpr):
    '''at least on operand must have variable'''
    for subqxpr in qxpr.operands:
        if check_qxpr_var_recursive(subqxpr):
            return True
    raise SchemeParserError(qxpr.token, 'no variable exist')


class PredPat(SpecialPat):
    def __init__(self, operator: str, operands: List[SimplePat]):
        self.operator = operator
        self.operands = operands


def parse_pattern_pred(qxpr: PredQxpr):
    operands = [parse_pattern_recursive(subqxpr)
                for subqxpr in qxpr.operands]
    return PredPat(qxpr.operator.literal, operands)


def stringify_pattern_pred(pat: PredPat):
    operands_str = ' '.join([stringify_pattern(subpat)
                             for subpat in pat.operands])
    return '(lisp-value %s %s)' % (pat.operator, operands_str)


def rename_pattern_pred(pat: PredPat, version: int):
    operands = [rename_pattern(subpat, version) for subpat in pat.operands]
    return PredPat(pat.operator, operands)


class Predicate:
    def __init__(self, name: str, py_func: Callable[..., bool]):
        self.name = name
        self.arity = len(inspect.getfullargspec(py_func).args)
        self.body = py_func


class SchemePredError(Exception):
    def __init__(self, message):
        self.message = message


_predicates: Dict[str, Predicate] = {}


def update_predicates(py_func_dict: Dict[str, Callable[..., bool]]):
    preds = {key: Predicate(key, py_func_dict[key]) for key in py_func_dict}
    _predicates.update(preds)


def qeval_pred(query: PredPat, assertions: OptFntStream[SimplePat], rules: OptFntStream[Rule], frames: OptFntStream[Frame]) -> OptFntStream[Frame]:
    try:
        if query.operator not in _predicates:
            raise SchemePredError('%s predicate undefined' % query.operator)
        pred = _predicates[query.operator]
        if pred.arity != len(query.operands):
            raise SchemePredError('%s predicate need %d argument, now %d provided' % (
                query.operator, pred.arity, len(query.operands)))

        def _qeval_pred_filter(frame: Frame):
            return pred.body(*query.operands)
        return stream_filter(_qeval_pred_filter, frames)
    except SchemePredError as err:
        scheme_panic(str(err))
    return None  # just for typing


def make_pred_num2_bool(py_func: Callable[[float, float], bool]):
    def _pred_num2_bool(x: SimplePat, y: SimplePat) -> bool:
        if not isinstance(x, NumberPat) or not isinstance(y, NumberPat):
            raise SchemePredError('%s requires both operators to be numbers, now %s and %s' % (
                py_func.__name__, type(x), type(y)))
        x = cast(NumberPat, x)
        y = cast(NumberPat, y)
        return py_func(x.value, y.value)
    return _pred_num2_bool


pred_op_eq = make_pred_num2_bool(lambda a, b: a == b)
pred_op_lt = make_pred_num2_bool(lambda a, b: a < b)
pred_op_gt = make_pred_num2_bool(lambda a, b: a > b)


def install_special_form_pred():
    update_parse_qxpr_rules(
        {'lisp-value': parse_compound_qxpr_pred})
    update_check_qxpr_forbid_rules({PredQxpr: check_qxpr_forbid_pred})
    update_check_qxpr_unbound_rules({PredQxpr: check_qxpr_unbound_pred})
    update_check_qxpr_var_rules({PredQxpr: check_qxpr_var_pred})
    update_parse_pattern_rules({PredQxpr: parse_pattern_pred})
    update_stringify_pattern_rules({PredPat: stringify_pattern_pred})
    update_rename_pattern_rules({PredPat: rename_pattern_pred})
    update_qeval_rules({PredPat: qeval_pred})
    update_predicates({
        '=': pred_op_eq,
        '<': pred_op_lt,
        '>': pred_op_gt
    })


'''initialize test'''


def install_rules():
    install_special_form_and()
    install_special_form_or()
    install_special_form_not()
    install_special_form_pred()


def test_stream():
    assert stream_from_list([1, 2, 3, 4]).topn_values(4) == [1, 2, 3, 4]
    assert stream_filter(lambda x: x % 2, stream_from_list(
        [1, 2, 3, 4])).topn_values(4) == [1, 3]
    assert stream_map(
        lambda x: x*2, stream_from_list([1, 2, 3, 4])).topn_values(4) == [2, 4, 6, 8]
    assert stream_append_delayed(stream_from_list(
        [1, 2]), lambda: stream_from_list([3, 4])).topn_values(4) == [1, 2, 3, 4]
    assert stream_interleave_delayed(stream_from_list(
        [1, 2]), lambda: stream_from_list([3, 4])).topn_values(4) == [1, 3, 2, 4]
    assert stream_flatten(stream_from_list([stream_from_list(
        [1, 2]), stream_from_list([3, 4])])).topn_values(4) == [1, 3, 2, 4]


class SrcParRes(TypedDict):
    source: str
    parsed: Optional[str]
    result: Optional[str]


def stringify_rule(qrl: Rule):
    concl_str = stringify_pattern(qrl.conclusion)
    body_str = stringify_pattern(qrl.body)
    return '(rule %s %s)' % (concl_str, body_str)


def stringify_result_frame(fs: OptFntStream[Frame], limit: int):
    unq_binding_strs: Set[str] = set()
    while fs is not None and len(unq_binding_strs) < limit:
        f = fs.value()
        d = resolve_final_frame(f)
        keys = sorted(d.keys())
        binding_str = '(%s)' % (', '.join(['%s=%s' % (k, stringify_pattern(d[k])) for k in keys]))
        if binding_str not in unq_binding_strs:
            unq_binding_strs.add(binding_str)
    return ' '.join(sorted(list(unq_binding_strs)))



def test_one(assertions_obj: SrcParRes, rules_obj: SrcParRes, query_objs: List[SrcParRes], panic: str):
    '''
    each test tries to execute the source code as much as possible
    capture the output, panic and result
    print them and compare to expected value
    '''

    try:
        assertion_stream = None
        assertions_source = assertions_obj['source'].strip()
        if len(assertions_source):
            print('* assertions-source: %s' % assertions_source)
            assertions = read_all_assertions(assertions_source)
            assertions_str = '\n'.join(
                [stringify_pattern(pat) for pat in assertions])
            print('* assertions-parsed: %s' % assertions_str)
            if assertions_obj['parsed'] is not None:
                assert assertions_str == assertions_obj['parsed']
            assertion_stream = make_assertion_stream(assertions)

        rule_stream = None
        rules_source = rules_obj['source'].strip()
        if len(rules_source):
            print('* rules-source: %s' % rules_source)
            rules = read_all_rules(rules_source)
            rules_str = '\n'.join([stringify_rule(qrl) for qrl in rules])
            print('* rules-parsed: %s' % rules_str)
            if rules_obj['parsed'] is not None:
                assert rules_str == rules_obj['parsed']
            rule_stream = make_rule_stream(rules)

        for query_obj in query_objs:
            query_source = query_obj['source'].strip()
            print('* query-source: %s' % query_source)
            query = read_single_query(query_source)
            query_str = stringify_pattern(query)
            print('* query-parsed: %s' % query_str)
            if query_obj['parsed'] is not None:
                assert query_str == query_obj['parsed']
            result = qeval(query, assertion_stream, rule_stream)
            result_str = stringify_result_frame(result, 3)
            print('* query-result: %s' % result_str)
            if query_obj['result'] is not None:
                assert result_str == query_obj['result']

        assert panic == ''
    except SchemePanic as err:
        # any kind of panic
        print('* panic: %s' % err.message)
        assert err.message == panic
    print('----------')


def make_src_par_res(**kargs: str) -> SrcParRes:
    d: SrcParRes = {'source': '', 'parsed': None, 'result': None}
    if 'source' in kargs:
        d['source'] = kargs['source']
    if 'parsed' in kargs:
        d['parsed'] = kargs['parsed']
    if 'result' in kargs:
        d['result'] = kargs['result']
    return d


def test_parse_assertions():
    test_one(
        assertions_obj=make_src_par_res(source='some-symbol'),
        rules_obj=make_src_par_res(),
        query_objs=[],
        panic='parser error at SYMBOL:some-symbol in line 1: pattern should be list'
    )
    test_one(
        assertions_obj=make_src_par_res(source='()'),
        rules_obj=make_src_par_res(),
        query_objs=[],
        panic='parser error at LEFT_PAREN in line 1: pattern should be non-empty list'
    )
    test_one(
        assertions_obj=make_src_par_res(source='(salary (Bitdiddle Ben) ?amount)'),
        rules_obj=make_src_par_res(),
        query_objs=[],
        panic='parser error at SYMBOL:?amount in line 1: pattern type VarQxpr forbidden'
    )
    test_one(
        assertions_obj=make_src_par_res(
            source='''
            (and (job (Bitdiddle Ben) (computer wizard))
            (salary (Bitdiddle Ben) 60000))
            '''),
        rules_obj=make_src_par_res(),
        query_objs=[],
        panic='parser error at LEFT_PAREN in line 1: pattern type SpecialQxpr forbidden'
    )
    test_one(
        assertions_obj=make_src_par_res(
            source='''
            (job   (Bitdiddle Ben) (computer wizard))
            (salary (Bitdiddle Ben) 60000)
            ''',
            result='(job (Bitdiddle Ben) (computer wizard))\n(salary (Bitdiddle Ben) 60000)'),
        rules_obj=make_src_par_res(),
        query_objs=[],
        panic=''
    )


def test_parse_queries():
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(),
        query_objs=[
            make_src_par_res(
                source='(salary   (Bitdiddle Ben) ?amount)',
                parsed='(salary (Bitdiddle Ben) ?amount)'
            )
        ],
        panic=''
    )
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(),
        query_objs=[
            make_src_par_res(
                source='(salary (Bitdiddle ?faimily-name) ?amount)',
                parsed='(salary (Bitdiddle ?faimily-name) ?amount)'
            )
        ],
        panic=''
    )
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(),
        query_objs=[
            make_src_par_res(
                source='''
            (and (job ?name (computer wizard))
            (salary ?name 60000))
            ''',
                parsed='(and (job ?name (computer wizard)) (salary ?name 60000))'
            )
        ],
        panic=''
    )
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(),
        query_objs=[
            make_src_par_res(
                source='''
            (and (job ?name (computer wizard))
            (salary (Bitdiddle Ben) 60000))
            '''
            )
        ],
        panic='parser error at LEFT_PAREN in line 1: no variable exist'
    )
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(),
        query_objs=[
            make_src_par_res(
                source='(salary (Bitdiddle . ?rest-name) ?amount)',
                parsed='(salary (Bitdiddle . ?rest-name) ?amount)'
            )
        ],
        panic=''
    )
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(),
        query_objs=[
            make_src_par_res(source='(salary (. ?name) ?amount)')
        ],
        panic='parser error at DOT in line 1: cannot have free or header dot within pattern'
    )
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(),
        query_objs=[
            make_src_par_res(
                source='''
            (job (Bitdiddle Ben) (computer wizard))
            (salary (Bitdiddle Ben) 60000)
            '''
            )
        ],
        panic='parser error at LEFT_PAREN in line 2: should have exactly one query'
    )
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(),
        query_objs=[
            make_src_par_res(source='(job (Bitdiddle Ben) (computer wizard))')
        ],
        panic='parser error at LEFT_PAREN in line 1: no variable exist'
    )
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(),
        query_objs=[
            make_src_par_res(
                source='''
            (and (job ?name (computer wizard))
            (not (salary ?name ?amount)))
            ''',
            )
        ],
        panic='parser error at SYMBOL:?amount in line 2: unbound variable'
    )
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(),
        query_objs=[
            make_src_par_res(
                source='''
            (and (job ?name (computer wizard))
            (lisp-value > ?amount 10000))
            ''',
            )
        ],
        panic='parser error at SYMBOL:?amount in line 2: unbound variable'
    )


def test_parse_rules():
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(
            source='(salary (Bitdiddle . ?rest-name) ?amount)'),
        query_objs=[],
        panic='parser error at LEFT_PAREN in line 1: rule should begin with rule symbol'
    )
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(source='(rule () ())'),
        query_objs=[],
        panic='parser error at LEFT_PAREN in line 1: pattern should be non-empty list'
    )
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(
            source='''
          (rule (lives-near ?p-1 ?p-2)
            (and (address ?p-1 (?town . ?rest-1)) (address ?p-2 (?town . ?rest-2))
            (not (same ?p-1 ?p-2))))
          (rule (same ?x ?x))
          ''',
            parsed='(rule (lives-near ?p-1 ?p-2) (and (address ?p-1 (?town . ?rest-1)) (address ?p-2 (?town . ?rest-2))' +
            ' (not (same ?p-1 ?p-2))))\n(rule (same ?x ?x) [empty])'
        ),
        query_objs=[],
        panic=''
    )


def test_parse_undetected():
    '''
    not is not detected as keyword inside simple pattern, so this rule conclusion can have not
    static checking are too much in this problem, I decide not to add more checking, so I ignore this
    '''
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(
            source='(rule (job ?name (computer wizard) (not (salary ?name 60000))))',
            parsed='(rule (job ?name (computer wizard) (not (salary ?name 60000))) [empty])'
        ),
        query_objs=[],
        panic=''
    )

def test_qeval_pattern():
    '''see chap 4.4.1 logic as programming'''
    test_one(
        assertions_obj=make_src_par_res(),
        rules_obj=make_src_par_res(
            source='''
            (rule (append-to-form () ?y ?y))
            (rule (append-to-form (?u . ?v) ?y (?u . ?z))
                  (append-to-form ?v ?y ?z))
            '''
        ),
        query_objs=[
            make_src_par_res(
                source='(append-to-form (a b) (c d) ?z)',
                result='(?z=(a b c d))'
            )
        ],
        panic=''
    )


def test():
    test_stream()
    test_parse_assertions()
    test_parse_queries()
    test_parse_rules()
    test_parse_undetected()
    test_qeval_pattern()


if __name__ == '__main__':
    install_rules()
    test()

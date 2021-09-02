'''
raw string input will be scanned to tokens
the following parsing takes 3 steps:
step 1 converts tokens into token combos
step 2 converts token combos into qexpressions
step 3 converts qexpressions into qpatterns
in step 1-2, errors are detected and printed with token information
step 3 assumes input qexpressions are valid, and will generates qpatterns that has no token information
it's the qpatterns that will be used for matching calculation
'''

from typing import Callable, Dict, List, Optional, Set, Type, TypeVar, TypedDict, Union
from sicp414_evaluator import SchemePanic, SchemeParserError, Token, TokenCombo, TokenList, TokenLiteral, TokenQuote, TokenTag, find_type, format_bool, format_float, make_root_token, parse_tokens, scan_source, scheme_panic


class QExpression:
    def __init__(self, token: Token):
        self.token = token
    '''
    the base class for all query expressions (QExpression), use class for easier static type checking
    QExpression will store token for debugging purpose
    '''
    pass


GenericQExpr = TypeVar("GenericQExpr", bound=QExpression)


class StringQExpr(QExpression):
    def __init__(self, token: Token):
        super().__init__(token)


class NumberQExpr(QExpression):
    def __init__(self, token: Token):
        super().__init__(token)


class BooleanQExpr(QExpression):
    def __init__(self, token: Token):
        super().__init__(token)


class ListQExpr(QExpression):
    def __init__(self, token: Token, contents: List[QExpression], tail: Optional[QExpression]):
        super().__init__(token)
        self.contents = contents
        self.tail = tail


class SymbolQExpr(QExpression):
    def __init__(self, token: Token):
        super().__init__(token)


class VarQExpr(QExpression):
    def __init__(self, token: Token):
        super().__init__(token)


class SpecialQExpr(QExpression):
    '''
    base class for special form
    this class makes it easy to check whether a pattern is a special form
    '''

    def __init__(self, token: Token):
        super().__init__(token)


'''
check that the input token combo is valid
that means top level is an non-empty token list
then each level has no quote
finally dot always appear in list and not list head
'''


def parse_qexpr_check_valid(combo: TokenCombo):
    if not isinstance(combo, TokenList):
        raise SchemeParserError(combo.anchor, 'pattern should be list')
    if len(combo.contents) == 0:
        raise SchemeParserError(
            combo.anchor, 'pattern should be non-empty list')
    parse_qexpr_check_valid_recursive(combo)


def parse_qexpr_check_valid_recursive(combo: TokenCombo):
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
                parse_qexpr_check_valid_recursive(subcombo)


'''parsing simple pattern from token combo, very similar to quote'''


def parse_simple_qexpr_symbol(token: Token):
    name: str = token.literal
    if name.startswith('?'):
        return VarQExpr(token)
    else:
        return SymbolQExpr(token)


def parse_simple_qexpr_string(token: Token):
    return StringQExpr(token)


def parse_simple_qexpr_number(token: Token):
    return NumberQExpr(token)


def parse_simple_qexpr_boolean(token: Token):
    return BooleanQExpr(token)


_parse_simple_qexpr_literal_rules: Dict[TokenTag, Callable[[Token], QExpression]] = {
    TokenTag.SYMBOL: parse_simple_qexpr_symbol,
    TokenTag.STRING: parse_simple_qexpr_string,
    TokenTag.NUMBER: parse_simple_qexpr_number,
    TokenTag.BOOLEAN: parse_simple_qexpr_boolean,
}


def parse_simple_qexpr_list(combo: TokenList):
    if len(combo.contents) >= 2 and combo.contents[-2].anchor.tag == TokenTag.DOT:
        subqexprs = [parse_simple_qexpr(subcomb)
                     for subcomb in combo.contents[:-2]]
        lastqexpr = parse_simple_qexpr(combo.contents[-1])
        return ListQExpr(combo.anchor, subqexprs, lastqexpr)
    else:
        subqexprs = [parse_simple_qexpr(subcomb) for subcomb in combo.contents]
        return ListQExpr(combo.anchor, subqexprs, None)


def parse_simple_qexpr(combo: TokenCombo) -> QExpression:
    if isinstance(combo, TokenLiteral):
        assert combo.anchor.tag in _parse_simple_qexpr_literal_rules
        f = _parse_simple_qexpr_literal_rules[combo.anchor.tag]
        return f(combo.anchor)
    else:
        assert isinstance(combo, TokenList)
        return parse_simple_qexpr_list(combo)


ParseCompoundQExprRuleType = Callable[[TokenList], QExpression]

_parse_compound_qexpr_rules: Dict[str, ParseCompoundQExprRuleType] = {}


def parse_qexpr(combo: TokenCombo):
    try:
        parse_qexpr_check_valid(combo)
        assert isinstance(combo, TokenList)
        first_content = combo.contents[0]
        '''first check special form by first symbol'''
        if first_content.anchor.tag == TokenTag.SYMBOL:
            cmd = first_content.anchor.literal
            if cmd in _parse_compound_qexpr_rules:
                f = _parse_compound_qexpr_rules[cmd]
                return f(combo)
        '''default to simple pattern'''
        return parse_simple_qexpr(combo)
    except SchemeParserError as err:
        scheme_panic(str(err))


def update_parse_compound_qexpr_rules(rules: Dict[str, ParseCompoundQExprRuleType]):
    _parse_compound_qexpr_rules.update(rules)


'''forbid types, e.g. assertion cannot have var and special form, rule-conclusion cannot have special form'''

CheckForbidFuncType = Callable[[GenericQExpr, List[Type]], None]

_check_qexpr_forbid_rules: Dict[Type, CheckForbidFuncType] = {}


def check_qexpr_forbid(qexpr: QExpression, forbid_types: List[Type]):
    try:
        check_qexpr_forbid_recursive(qexpr, forbid_types)
    except SchemeParserError as err:
        scheme_panic(str(err))


def check_qexpr_forbid_recursive(qexpr: QExpression, forbid_types: List[Type]):
    t = find_type(type(qexpr), _check_qexpr_forbid_rules)
    f = _check_qexpr_forbid_rules[t]
    f(qexpr, forbid_types)


def check_qexpr_forbid_self(qexpr: QExpression, forbid_types: List[Type]):
    for ft in forbid_types:
        if isinstance(qexpr, ft):
            raise SchemeParserError(qexpr.token, 'pattern type %s forbidden' % ft.__name__)


def check_qexpr_forbid_list(qexpr: ListQExpr, forbid_types: List[Type]):
    check_qexpr_forbid_self(qexpr, forbid_types)
    for subqexpr in qexpr.contents:
        check_qexpr_forbid_recursive(subqexpr, forbid_types)
    if qexpr.tail is not None:
        check_qexpr_forbid_recursive(qexpr.tail, forbid_types)


def update_check_qexpr_forbid_rules(rules: Dict[Type, CheckForbidFuncType]):
    _check_qexpr_forbid_rules.update(rules)


update_check_qexpr_forbid_rules({
    QExpression: check_qexpr_forbid_self,
    ListQExpr: check_qexpr_forbid_list,
})

'''check certain expression can not have unbounded vars, e.g. not and lisp-value'''

CheckUnboundFuncType = Callable[[GenericQExpr, int, Set[str]], None]

_check_qexpr_unbound_rules: Dict[Type, CheckUnboundFuncType] = {}


def check_qexpr_unbound_recursive(qexpr: QExpression, depth: int, seen_variables: Set[str]):
    t = find_type(type(qexpr), _check_qexpr_unbound_rules)
    f = _check_qexpr_unbound_rules[t]
    f(qexpr, depth, seen_variables)


def check_qexpr_unbound(qexpr: QExpression):
    try:
        check_qexpr_unbound_recursive(qexpr, 0, set())
    except SchemeParserError as err:
        scheme_panic(str(err))


def check_qexpr_unbound_pass(qexpr: QExpression, depth: int, seen_variables: Set[str]):
    pass


def check_qexpr_unbound_var(qexpr: QExpression, depth: int, seen_variables: Set[str]):
    name = qexpr.token.literal
    if depth == 0:
        seen_variables.add(name)
    elif name not in seen_variables:
        raise SchemeParserError(qexpr.token, 'unbound variable')


def check_qexpr_unbound_list(qexpr: ListQExpr, depth: int, seen_variables: Set[str]):
    for subqexpr in qexpr.contents:
        check_qexpr_unbound_recursive(subqexpr, depth, seen_variables)
    if qexpr.tail is not None:
        check_qexpr_unbound_recursive(qexpr.tail, depth, seen_variables)


def update_check_qexpr_unbound_rules(rules: Dict[Type, CheckUnboundFuncType]):
    _check_qexpr_unbound_rules.update(rules)


update_check_qexpr_unbound_rules({
    QExpression: check_qexpr_unbound_pass,
    VarQExpr: check_qexpr_unbound_var,
    ListQExpr: check_qexpr_unbound_list,
})

'''check there exist some var in rule and query'''

CheckVarFuncType = Callable[[GenericQExpr], bool]

_check_qexpr_var_rules: Dict[Type, CheckVarFuncType] = {}


def check_qexpr_var(qexpr: QExpression):
    try:
        has_var = check_qexpr_var_recursive(qexpr)
        if not has_var:
            raise SchemeParserError(qexpr.token, 'no variable exist')
    except SchemeParserError as err:
        scheme_panic(str(err))


def check_qexpr_var_recursive(qexpr: QExpression):
    t = find_type(type(qexpr), _check_qexpr_var_rules)
    f = _check_qexpr_var_rules[t]
    return f(qexpr)


def check_qexpr_var_pass(qexpr: QExpression):
    return False


def check_qexpr_var_var(qexpr: VarQExpr):
    return True


def check_qexpr_var_list(qexpr: ListQExpr):
    for subqexpr in qexpr.contents:
        if check_qexpr_var_recursive(subqexpr):
            return True
    if qexpr.tail is not None:
        if check_qexpr_var_recursive(qexpr.tail):
            return True
    return False


def update_check_qexpr_var_rules(rules: Dict[Type, CheckVarFuncType]):
    _check_qexpr_var_rules.update(rules)


update_check_qexpr_var_rules({
    QExpression: check_qexpr_var_pass,
    VarQExpr: check_qexpr_var_var,
    ListQExpr: check_qexpr_var_list,
})

'''patterns'''


class QPattern:
    '''
    base class of pattern
    now static analysis is finished
    no token information remained
    '''


GenericQPat = TypeVar("GenericQPat", bound=QPattern)


class StringQPat(QPattern):
    def __init__(self, value: str):
        self.value = value


class NumberQPat(QPattern):
    def __init__(self, value: float):
        self.value = value


class BooleanQPat(QPattern):
    def __init__(self, value: bool):
        self.value = value


class NilQPat(QPattern):
    pass


class PairQPat(QPattern):
    '''
    we need pair and nil because this makes matching (?x . ?y) with (a b) easy
    using good old list is not easy to do this
    '''

    def __init__(self, left: QPattern, right: QPattern):
        self.left = left
        self.right = right


class SymbolQPat(QPattern):
    def __init__(self, name: str):
        self.name = name


class VarQPat(QPattern):
    def __init__(self, name: str, version: int):
        '''version for renaming'''
        self.name = name
        self.version = version


class EmptyQPat(QPattern):
    '''used for empty rule body, called always-true in the book'''
    pass


'''pair pattern'''


def pair_from_list_pattern(fronts: List[QPattern], last: QPattern):
    head: QPattern = last
    for i in range(len(fronts)-1, -1, -1):
        head = PairQPat(fronts[i], head)
    return head


def pair_to_list_pattern(sv: PairQPat):
    fronts: List[QPattern] = []
    head: QPattern = sv
    while isinstance(head, PairQPat):
        fronts.append(head.left)
        head = head.right
    last = head
    return fronts, last


'''parse patterns'''

ParseQPatternFuncType = Callable[[GenericQExpr], QPattern]

_parse_qpattern_rules: Dict[Type, ParseQPatternFuncType] = {}


def parse_qpattern(qexpr: QExpression):
    try:
        return parse_qpattern_recursive(qexpr)
    except SchemeParserError as err:
        scheme_panic(str(err))

def parse_qpattern_recursive(qexpr: QExpression):
    t = find_type(type(qexpr), _parse_qpattern_rules)
    f = _parse_qpattern_rules[t]
    return f(qexpr)


def parse_qpattern_string(qexpr: StringQExpr):
    return StringQPat(qexpr.token.literal)


def parse_qpattern_number(qexpr: NumberQExpr):
    return NumberQPat(qexpr.token.literal)


def parse_qpattern_boolean(qexpr: BooleanQExpr):
    return BooleanQPat(qexpr.token.literal)


def parse_qpattern_symbol(qexpr: SymbolQExpr):
    return SymbolQPat(qexpr.token.literal)


def parse_qpattern_var(qexpr: VarQExpr):
    return VarQPat(qexpr.token.literal, 0)


def parse_qpattern_list(qexpr: ListQExpr):
    fronts = [parse_qpattern_recursive(subqexpr) for subqexpr in qexpr.contents]
    last = parse_qpattern_recursive(qexpr.tail) if qexpr.tail is not None else NilQPat()
    return pair_from_list_pattern(fronts, last)


def update_parse_qpattern_rules(rules: Dict[Type, ParseQPatternFuncType]):
    _parse_qpattern_rules.update(rules)


update_parse_qpattern_rules({
    StringQExpr: parse_qpattern_string,
    NumberQExpr: parse_qpattern_number,
    BooleanQExpr: parse_qpattern_boolean,
    SymbolQExpr: parse_qpattern_symbol,
    VarQExpr: parse_qpattern_var,
    ListQExpr: parse_qpattern_list,
})

'''stringify patterns'''

StringifyQPatternFuncType = Callable[[GenericQPat], str]

_stringify_qpattern_rules: Dict[Type, StringifyQPatternFuncType] = {}


def update_stringify_qpattern_rules(rules: Dict[Type, StringifyQPatternFuncType]):
    _stringify_qpattern_rules.update(rules)


def stringify_qpattern(pat: QPattern):
    t = find_type(type(pat), _stringify_qpattern_rules)
    f = _stringify_qpattern_rules[t]
    return f(pat)


def stringify_qpattern_symbol(pat: SymbolQPat):
    return pat.name


def stringify_qpattern_var(pat: VarQPat):
    return pat.name


def stringify_qpattern_string(pat: StringQPat):
    return '"%s"' % pat.value


def stringify_qpattern_number(pat: NumberQPat):
    return format_float(pat.value)


def stringify_qpattern_boolean(pat: BooleanQPat):
    return format_bool(pat.value)


def stringify_qpattern_nil(pat: NilQPat):
    return '()'


def stringify_qpattern_pair(pat: PairQPat):
    fronts, last = pair_to_list_pattern(pat)
    left_str = ' '.join([stringify_qpattern(subpat) for subpat in fronts])
    if isinstance(last, NilQPat):
        return '(%s)' % left_str
    else:
        right_str = stringify_qpattern(last)
        return '(%s . %s)' % (left_str, right_str)


def stringify_qpattern_empty(pat: EmptyQPat):
    return '[empty]'


update_stringify_qpattern_rules({
    StringQPat: stringify_qpattern_string,
    NumberQPat: stringify_qpattern_number,
    BooleanQPat: stringify_qpattern_boolean,
    SymbolQPat: stringify_qpattern_symbol,
    VarQPat: stringify_qpattern_var,
    NilQPat: stringify_qpattern_nil,
    PairQPat: stringify_qpattern_pair,
    EmptyQPat: stringify_qpattern_empty
})

'''parse assertions, rules, query'''


def parse_assertion(combo: TokenCombo):
    qexpr = parse_qexpr(combo)
    check_qexpr_forbid(qexpr, [VarQExpr, SpecialQExpr])
    pat = parse_qpattern(qexpr)
    return pat


def read_all_assertions(source: str):
    tokens = scan_source(source)
    combos = parse_tokens(tokens)
    assertions = [parse_assertion(subcombo) for subcombo in combos]
    return assertions


def parse_query(combo: TokenCombo):
    qexpr = parse_qexpr(combo)
    check_qexpr_unbound(qexpr)
    check_qexpr_var(qexpr)
    pat = parse_qpattern(qexpr)
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


class QRule:
    def __init__(self, conclusion: QPattern, body: QPattern):
        self.conclusion = conclusion
        self.body = body


def get_qrule_contents(combo: TokenCombo):
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


def parse_qrule(combo: TokenCombo):
    concl_combo, body_combo = get_qrule_contents(combo)
    concl_qexpr = parse_qexpr(concl_combo)
    check_qexpr_forbid(concl_qexpr, [SpecialQExpr])
    check_qexpr_var(concl_qexpr)
    concl_pat = parse_qpattern(concl_qexpr)
    if body_combo is not None:
        body_pat = parse_query(body_combo)
    else:
        body_pat = EmptyQPat()
    return QRule(concl_pat, body_pat)


def read_all_qrules(source: str):
    tokens = scan_source(source)
    combos = parse_tokens(tokens)
    qrules = [parse_qrule(subcombo) for subcombo in combos]
    return qrules


'''special form: and'''


class AndQExpr(SpecialQExpr):
    def __init__(self, token: Token, contents: List[QExpression]):
        super().__init__(token)
        self.contents = contents


def parse_compound_qexpr_and(combo: TokenList):
    if len(combo.contents) < 3:
        raise SchemeParserError(
            combo.anchor, 'and special form need at least 3 terms')
    contents = [parse_qexpr(subcomb) for subcomb in combo.contents[1:]]
    return AndQExpr(combo.anchor, contents)


def check_qexpr_forbid_and(qexpr: AndQExpr, forbid_types: List[Type]):
    check_qexpr_forbid_self(qexpr, forbid_types)
    for subqexpr in qexpr.contents:
        check_qexpr_forbid_recursive(subqexpr, forbid_types)


def check_qexpr_unbound_and(qexpr: AndQExpr, depth: int, seen_variables: Set[str]):
    for subqexpr in qexpr.contents:
        check_qexpr_unbound_recursive(subqexpr, depth, seen_variables)


def check_qexpr_var_and(qexpr: AndQExpr):
    '''every content must have variable'''
    for subqexpr in qexpr.contents:
        if not check_qexpr_var_recursive(subqexpr):
            raise SchemeParserError(qexpr.token, 'no variable exist')
    return True


class AndQPat(QPattern):
    def __init__(self, contents: List[QPattern]):
        self.contents = contents


def parse_qpattern_and(qexpr: AndQExpr):
    contents = [parse_qpattern_recursive(subqexpr) for subqexpr in qexpr.contents]
    return AndQPat(contents)


def stringify_qpattern_and(pat: AndQPat):
    contents_str = ' '.join([stringify_qpattern(subpat)
                             for subpat in pat.contents])
    return '(and %s)' % contents_str


def install_special_form_and():
    update_parse_compound_qexpr_rules({'and': parse_compound_qexpr_and})
    update_check_qexpr_forbid_rules({AndQExpr: check_qexpr_forbid_and})
    update_check_qexpr_unbound_rules({AndQExpr: check_qexpr_unbound_and})
    update_check_qexpr_var_rules({AndQExpr: check_qexpr_var_and})
    update_parse_qpattern_rules({AndQExpr: parse_qpattern_and})
    update_stringify_qpattern_rules({AndQPat: stringify_qpattern_and})


'''special form: or'''


class OrQExpr(SpecialQExpr):
    def __init__(self, token: Token, contents: List[QExpression]):
        super().__init__(token)
        self.contents = contents


def parse_compound_qexpr_or(combo: TokenList):
    if len(combo.contents) < 3:
        raise SchemeParserError(
            combo.anchor, 'or special form need at least 3 terms')
    contents = [parse_qexpr(subcomb) for subcomb in combo.contents[1:]]
    return OrQExpr(combo.anchor, contents)


def check_qexpr_forbid_or(qexpr: OrQExpr, forbid_types: List[Type]):
    check_qexpr_forbid_self(qexpr, forbid_types)
    for subqexpr in qexpr.contents:
        check_qexpr_forbid_recursive(subqexpr, forbid_types)


def check_qexpr_unbound_or(qexpr: OrQExpr, depth: int, seen_variables: Set[str]):
    for subqexpr in qexpr.contents:
        check_qexpr_unbound_recursive(subqexpr, depth, seen_variables)


def check_qexpr_var_or(qexpr: OrQExpr):
    '''every content must have variable'''
    for subqexpr in qexpr.contents:
        if not check_qexpr_var_recursive(subqexpr):
            raise SchemeParserError(qexpr.token, 'no variable exist')
    return True


class OrQPat(QPattern):
    def __init__(self, contents: List[QPattern]):
        self.contents = contents


def parse_qpattern_or(qexpr: OrQExpr):
    contents = [parse_qpattern_recursive(subqexpr) for subqexpr in qexpr.contents]
    return OrQPat(contents)


def stringify_qpattern_or(pat: OrQPat):
    contents_str = ' '.join([stringify_qpattern(subpat)
                             for subpat in pat.contents])
    return '(or %s)' % contents_str


def install_special_form_or():
    update_parse_compound_qexpr_rules({'or': parse_compound_qexpr_or})
    update_check_qexpr_forbid_rules({OrQExpr: check_qexpr_forbid_or})
    update_check_qexpr_unbound_rules({OrQExpr: check_qexpr_unbound_or})
    update_check_qexpr_var_rules({OrQExpr: check_qexpr_var_or})
    update_parse_qpattern_rules({OrQExpr: parse_qpattern_or})
    update_stringify_qpattern_rules({OrQPat: stringify_qpattern_or})


'''special form: not'''


class NotQExpr(SpecialQExpr):
    def __init__(self, token: Token, content: QExpression):
        super().__init__(token)
        self.content = content


def parse_compound_qexpr_not(combo: TokenList):
    if len(combo.contents) != 2:
        raise SchemeParserError(
            combo.anchor, 'not special form need exactly 2 terms')
    content = parse_qexpr(combo.contents[1])
    return NotQExpr(combo.anchor, content)


def check_qexpr_forbid_not(qexpr: NotQExpr, forbid_types: List[Type]):
    check_qexpr_forbid_self(qexpr, forbid_types)
    check_qexpr_forbid_recursive(qexpr.content, forbid_types)


def check_qexpr_unbound_not(qexpr: NotQExpr, depth: int, seen_variables: Set[str]):
    check_qexpr_unbound_recursive(qexpr.content, depth+1, seen_variables)


def check_qexpr_var_not(qexpr: NotQExpr):
    '''content must have variable'''
    if not check_qexpr_var_recursive(qexpr.content):
        raise SchemeParserError(qexpr.token, 'no variable exist')
    return True


class NotQPat(QPattern):
    def __init__(self, content: QPattern):
        self.content = content


def parse_qpattern_not(qexpr: NotQExpr):
    content = parse_qpattern_recursive(qexpr.content)
    return NotQPat(content)


def stringify_qpattern_not(pat: NotQPat):
    content_str = stringify_qpattern(pat.content)
    return '(not %s)' % content_str


def install_special_form_not():
    update_parse_compound_qexpr_rules({'not': parse_compound_qexpr_not})
    update_check_qexpr_forbid_rules({NotQExpr: check_qexpr_forbid_not})
    update_check_qexpr_unbound_rules({NotQExpr: check_qexpr_unbound_not})
    update_check_qexpr_var_rules({NotQExpr: check_qexpr_var_not})
    update_parse_qpattern_rules({NotQExpr: parse_qpattern_not})
    update_stringify_qpattern_rules({NotQPat: stringify_qpattern_not})


'''special form: lisp-value'''


class PredQExpr(SpecialQExpr):
    def __init__(self, token: Token, operator: Token, operands: List[QExpression]):
        super().__init__(token)
        self.operator = operator
        self.operands = operands


def parse_compound_qexpr_pred(combo: TokenList):
    '''notice operands can only be simple qexpressions'''
    if len(combo.contents) < 3:
        raise SchemeParserError(
            combo.anchor, 'lisp-value special form need at least 3 terms')
    if combo.contents[1].anchor.tag != TokenTag.SYMBOL:
        raise SchemeParserError(
            combo.anchor, 'lisp-value special form must have a symbolic operator name')
    operator = combo.contents[1].anchor
    operands = [parse_simple_qexpr(subqexpr)
                for subqexpr in combo.contents[2:]]
    return PredQExpr(combo.anchor, operator, operands)


def check_qexpr_forbid_pred(qexpr: PredQExpr, forbid_types: List[Type]):
    check_qexpr_forbid_self(qexpr, forbid_types)
    for subqexpr in qexpr.operands:
        check_qexpr_forbid_recursive(subqexpr, forbid_types)


def check_qexpr_unbound_pred(qexpr: PredQExpr, depth: int, seen_variables: Set[str]):
    for subqexpr in qexpr.operands:
        check_qexpr_unbound_recursive(subqexpr, depth+1, seen_variables)


def check_qexpr_var_pred(qexpr: PredQExpr):
    '''at least on operand must have variable'''
    for subqexpr in qexpr.operands:
        if check_qexpr_var_recursive(subqexpr):
            return True
    raise SchemeParserError(qexpr.token, 'no variable exist')


class PredQPat(QPattern):
    def __init__(self, operator: str, operands: List[QPattern]):
        self.operator = operator
        self.operands = operands


def parse_qpattern_pred(qexpr: PredQExpr):
    operands = [parse_qpattern_recursive(subqexpr) for subqexpr in qexpr.operands]
    return PredQPat(qexpr.operator.literal, operands)


def stringify_qpattern_pred(pat: PredQPat):
    operands_str = ' '.join([stringify_qpattern(subpat)
                             for subpat in pat.operands])
    return '(lisp-value %s %s)' % (pat.operator, operands_str)


def install_special_form_pred():
    update_parse_compound_qexpr_rules(
        {'lisp-value': parse_compound_qexpr_pred})
    update_check_qexpr_forbid_rules({PredQExpr: check_qexpr_forbid_pred})
    update_check_qexpr_unbound_rules({PredQExpr: check_qexpr_unbound_pred})
    update_check_qexpr_var_rules({PredQExpr: check_qexpr_var_pred})
    update_parse_qpattern_rules({PredQExpr: parse_qpattern_pred})
    update_stringify_qpattern_rules({PredQPat: stringify_qpattern_pred})


'''initialize test'''


def install_rules():
    install_special_form_and()
    install_special_form_or()
    install_special_form_not()
    install_special_form_pred()


class SrcRes(TypedDict):
    source: str
    result: Optional[str]


def stringify_qrule(qrl: QRule):
    concl_str = stringify_qpattern(qrl.conclusion)
    body_str = stringify_qpattern(qrl.body)
    return '(rule %s %s)' % (concl_str, body_str)


def test_one(assertions_obj: SrcRes, qrules_obj: SrcRes, query_objs: List[SrcRes], panic: str):
    '''
    each test tries to execute the source code as much as possible
    capture the output, panic and result
    print them and compare to expected value
    '''

    try:
        assertions_source = assertions_obj['source'].strip()
        if len(assertions_source):
            print('* assertions-source: %s' % assertions_source)
            assertions = read_all_assertions(assertions_source)
            assertions_str = '\n'.join(
                [stringify_qpattern(qpat) for qpat in assertions])
            print('* assertions-parsed: %s' % assertions_str)
            if assertions_obj['result'] is not None:
                assert assertions_str == assertions_obj['result']

        qrules_source = qrules_obj['source'].strip()
        if len(qrules_source):
            print('* qrules-source: %s' % qrules_source)
            qrules = read_all_qrules(qrules_source)
            qrules_str = '\n'.join([stringify_qrule(qrl) for qrl in qrules])
            print('* qrules-parsed: %s' % qrules_str)
            if qrules_obj['result'] is not None:
                assert qrules_str == qrules_obj['result']

        for query_obj in query_objs:
            query_source = query_obj['source'].strip()
            print('* query-source: %s' % query_source)
            query = read_single_query(query_source)
            query_str = stringify_qpattern(query)
            print('* query-parsed: %s' % query_str)
            if query_obj['result'] is not None:
                assert query_str == query_obj['result']
        
        assert panic == ''
    except SchemePanic as err:
        # any kind of panic
        print('* panic: %s' % err.message)
        assert err.message == panic
    print('----------')


def make_src_res(**kargs: str) -> SrcRes:
    if 'source' in kargs:
        if 'result' in kargs:
            return {'source': kargs['source'], 'result': kargs['result']}
        else:
            return {'source': kargs['source'], 'result': None}
    else:
        return {'source': '', 'result': None}


def test_parse_assertions():
    test_one(
        assertions_obj=make_src_res(source='some-symbol'),
        qrules_obj=make_src_res(),
        query_objs=[],
        panic='parser error at SYMBOL:some-symbol in line 1: pattern should be list'
    )
    test_one(
        assertions_obj=make_src_res(source='()'),
        qrules_obj=make_src_res(),
        query_objs=[],
        panic='parser error at LEFT_PAREN in line 1: pattern should be non-empty list'
    )
    test_one(
        assertions_obj=make_src_res(source='(salary (Bitdiddle Ben) ?amount)'),
        qrules_obj=make_src_res(),
        query_objs=[],
        panic='parser error at SYMBOL:?amount in line 1: pattern type VarQExpr forbidden'
    )
    test_one(
        assertions_obj=make_src_res(
            source='''
            (and (job (Bitdiddle Ben) (computer wizard))
            (salary (Bitdiddle Ben) 60000))
            ''',
            result='(job (Bitdiddle Ben) (computer wizard))\n(salary (Bitdiddle Ben) 60000)'),
        qrules_obj=make_src_res(),
        query_objs=[],
        panic='parser error at LEFT_PAREN in line 1: pattern type SpecialQExpr forbidden'
    )
    test_one(
        assertions_obj=make_src_res(
            source='''
            (job   (Bitdiddle Ben) (computer wizard))
            (salary (Bitdiddle Ben) 60000)
            ''',
            result='(job (Bitdiddle Ben) (computer wizard))\n(salary (Bitdiddle Ben) 60000)'),
        qrules_obj=make_src_res(),
        query_objs=[],
        panic=''
    )

def test_parse_queries():
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(),
        query_objs=[
          make_src_res(
            source='(salary   (Bitdiddle Ben) ?amount)',
            result='(salary (Bitdiddle Ben) ?amount)'
            )
        ],
        panic=''
    )
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(),
        query_objs=[
          make_src_res(
            source='(salary (Bitdiddle ?faimily-name) ?amount)',
            result='(salary (Bitdiddle ?faimily-name) ?amount)'
            )
        ],
        panic=''
    )
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(),
        query_objs=[
          make_src_res(
            source='''
            (and (job ?name (computer wizard))
            (salary ?name 60000))
            ''',
            result='(and (job ?name (computer wizard)) (salary ?name 60000))'
            )
        ],
        panic=''
    )
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(),
        query_objs=[
          make_src_res(
            source='''
            (and (job ?name (computer wizard))
            (salary (Bitdiddle Ben) 60000))
            '''
            )
        ],
        panic='parser error at LEFT_PAREN in line 1: no variable exist'
    )
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(),
        query_objs=[
          make_src_res(
            source='(salary (Bitdiddle . ?rest-name) ?amount)',
            result='(salary (Bitdiddle . ?rest-name) ?amount)'
            )
        ],
        panic=''
    )
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(),
        query_objs=[
          make_src_res(source='(salary (. ?name) ?amount)')
        ],
        panic='parser error at DOT in line 1: cannot have free or header dot within pattern'
    )
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(),
        query_objs=[
          make_src_res(
            source='''
            (job (Bitdiddle Ben) (computer wizard))
            (salary (Bitdiddle Ben) 60000)
            '''
            )
        ],
        panic='parser error at LEFT_PAREN in line 2: should have exactly one query'
    )
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(),
        query_objs=[
          make_src_res(source='(job (Bitdiddle Ben) (computer wizard))')
        ],
        panic='parser error at LEFT_PAREN in line 1: no variable exist'
    )
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(),
        query_objs=[
          make_src_res(
            source='''
            (and (job ?name (computer wizard))
            (not (salary ?name ?amount)))
            ''',
            )
        ],
        panic='parser error at SYMBOL:?amount in line 2: unbound variable'
    )
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(),
        query_objs=[
          make_src_res(
            source='''
            (and (job ?name (computer wizard))
            (lisp-value > ?amount 10000))
            ''',
            )
        ],
        panic='parser error at SYMBOL:?amount in line 2: unbound variable'
    )
    

def test_parse_qrules():
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(source='(salary (Bitdiddle . ?rest-name) ?amount)'),
        query_objs=[],
        panic='parser error at LEFT_PAREN in line 1: rule should begin with rule symbol'
    )
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(source='(rule () ())'),
        query_objs=[],
        panic='parser error at LEFT_PAREN in line 1: pattern should be non-empty list'
    )
    test_one(
        assertions_obj=make_src_res(),
        qrules_obj=make_src_res(
          source='''
          (rule (lives-near ?p-1 ?p-2)
            (and (address ?p-1 (?town . ?rest-1)) (address ?p-2 (?town . ?rest-2))
            (not (same ?p-1 ?p-2))))
          (rule (same ?x ?x))
          ''',
          result='(rule (lives-near ?p-1 ?p-2) (and (address ?p-1 (?town . ?rest-1)) (address ?p-2 (?town . ?rest-2))' + \
            ' (not (same ?p-1 ?p-2))))\n(rule (same ?x ?x) [empty])'
        ),
        query_objs=[],
        panic=''
    )


def test():
    test_parse_assertions()
    test_parse_queries()
    test_parse_qrules()


if __name__ == '__main__':
    install_rules()
    test()

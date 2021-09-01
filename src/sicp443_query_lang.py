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

from typing import Any, Callable, Dict, List, Optional, Set, Tuple, Type, TypeVar
from sicp414_evaluator import SchemeParserError, Token, TokenCombo, TokenList, TokenLiteral, TokenQuote, TokenTag, find_type


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
        raise SchemeParserError(combo.anchor, 'pattern should be non-empty list')
    parse_qexpr_check_valid_recursive(combo)

def parse_qexpr_check_valid_recursive(combo: TokenCombo):
    if isinstance(combo, TokenLiteral):
        if combo.anchor.tag == TokenTag.DOT:
            raise SchemeParserError(combo.anchor, 'cannot have free or header dot within pattern')
    elif isinstance(combo, TokenQuote):
        raise SchemeParserError(combo.anchor, 'cannot have quote within pattern')
    else:
        assert isinstance(combo, TokenList)
        for (i, subcombo) in enumerate(combo.contents):
            if i == 0 or not isinstance(subcombo, TokenLiteral):
                parse_qexpr_check_valid_recursive(subcombo)

'''parsing simple pattern from token combo, very similar to quote'''

def parse_simple_qexpr_symbol(token: Token):
    name:str = token.literal
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
        subqexprs = [parse_simple_qexpr(subcomb) for subcomb in combo.contents[:-2]]
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

def update_parse_compound_qexpr_rules(rules: Dict[str, ParseCompoundQExprRuleType]):
    _parse_compound_qexpr_rules.update(rules)

'''forbid types'''

ParseForbidFuncType = Callable[[GenericQExpr, List[Type]], None]

_parse_qexpr_forbid_rules: Dict[Type, ParseForbidFuncType] = {}

def parse_qexpr_forbid(qexpr: QExpression, forbid_types: List[Type]):
    t = find_type(type(qexpr), _parse_qexpr_forbid_rules)
    f = _parse_qexpr_forbid_rules[t]
    f(qexpr, forbid_types)

def parse_qexpr_forbid_self(qexpr: QExpression, forbid_types: List[Type]):
    if isinstance(qexpr, tuple(forbid_types)):
        raise SchemeParserError(qexpr.token, 'pattern type forbidden')

def parse_qexpr_forbid_list(qexpr: ListQExpr, forbid_types: List[Type]):
    parse_qexpr_forbid_self(qexpr, forbid_types)
    for subqexpr in qexpr.contents:
        parse_qexpr_forbid(subqexpr, forbid_types)
    if qexpr.tail is not None:
        parse_qexpr_forbid(qexpr.tail, forbid_types)

def update_parse_qexpr_forbid_rules(rules: Dict[Type, ParseForbidFuncType]):
    _parse_qexpr_forbid_rules.update(rules)

update_parse_qexpr_forbid_rules({
    QExpression: parse_qexpr_forbid_self,
    ListQExpr: parse_qexpr_forbid_list,
})

'''check unbounded vars'''

ParseUnboundFuncType = Callable[[GenericQExpr, int, Set[str]], None]

_parse_qexpr_unbound_rules: Dict[Type, ParseUnboundFuncType] = {}

def parse_qexpr_unbound_recursive(qexpr: QExpression, depth: int, seen_variables: Set[str]):
    t = find_type(type(qexpr), _parse_qexpr_unbound_rules)
    f = _parse_qexpr_unbound_rules[t]
    f(qexpr, depth, seen_variables)

def parse_qexpr_unbound(qexpr: QExpression):
    parse_qexpr_unbound_recursive(qexpr, 0, set())

def parse_qexpr_unbound_pass(qexpr: QExpression, depth: int, seen_variables: Set[str]):
    pass

def parse_qexpr_unbound_var(qexpr: QExpression, depth: int, seen_variables: Set[str]):
    name = qexpr.token.literal
    if depth == 0:
        seen_variables.add(name)
    elif name not in seen_variables:
        raise SchemeParserError(qexpr.token, 'unbound variable')
      
def parse_qexpr_unbound_list(qexpr: ListQExpr, depth: int, seen_variables: Set[str]):
    for subqexpr in qexpr.contents:
        parse_qexpr_unbound_recursive(subqexpr, depth, seen_variables)
    if qexpr.tail is not None:
        parse_qexpr_unbound_recursive(qexpr.tail, depth, seen_variables)

def update_parse_qexpr_unbound_rules(rules: Dict[Type, ParseUnboundFuncType]):
    _parse_qexpr_unbound_rules.update(rules)

update_parse_qexpr_unbound_rules({
    QExpression: parse_qexpr_unbound_pass,
    VarQExpr: parse_qexpr_unbound_var,
    ListQExpr: parse_qexpr_unbound_list,
})

'''patterns'''

class QPattern:
    '''
    base class of pattern
    now static analysis is finished
    no token information remained
    '''

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

'''parse patterns'''

ParseQPatternFuncType = Callable[[GenericQExpr], QPattern]

_parse_qpattern_rules: Dict[Type, ParseQPatternFuncType] = {}

def parse_qpattern(qexpr: QExpression):
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
    head: QPattern = parse_qpattern(qexpr.tail) if qexpr.tail is not None else NilQPat()
    for i in range(len(qexpr.contents)-1, -1, -1):
        head = PairQPat(parse_qpattern(qexpr.contents[i]), head)
    return head

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

'''parse assertions, rules, query'''

def parse_assertion(combo: TokenCombo):
    qexpr = parse_qexpr(combo)
    parse_qexpr_forbid(qexpr, [VarQExpr, SpecialQExpr])
    pat = parse_qpattern(qexpr)
    return pat

def parse_all_assertions(combos: List[TokenCombo]):
    return [parse_assertion(subcombo) for subcombo in combos]

def parse_query(combo: TokenCombo):
    qexpr = parse_qexpr(combo)
    parse_qexpr_unbound(qexpr)
    pat = parse_qpattern(qexpr)
    return pat

def parse_single_query(combos: List[TokenCombo]):
    if len(combos) > 1:
        raise SchemeParserError(combos[-1].anchor, 'should have exactly one query')
    elif len(combos) == 0:
        root_token = Token(TokenTag.ROOT, 0, '', None)
        raise SchemeParserError(root_token, 'should have exactly one query')
    return parse_query(combos[0])

class EmptyQPat(QPattern):
    '''used for empty rule body, called always-true in the book'''
    pass

class QRule:
    def __init__(self, conclusion: QPattern, body: QPattern):
        self.conclusion = conclusion
        self.body = body

def parse_qrule(combo: TokenCombo):
    if not isinstance(combo, TokenList):
        raise SchemeParserError(combo.anchor, 'rule should be a list')
    if len(combo.contents) < 2 or len(combo.contents) > 3:
        raise SchemeParserError(combo.anchor, 'rule should be a list of 2 or 3 terms')
    if combo.contents[0].anchor.tag != TokenTag.SYMBOL or combo.contents[0].anchor.lexeme != 'rule':
        raise SchemeParserError(combo.anchor, 'rule should begin with rule symbol')
    concl_qexpr = parse_qexpr(combo.contents[1])
    parse_qexpr_forbid(concl_qexpr, [SpecialQExpr])
    concl_pat = parse_qpattern(concl_qexpr)
    if len(combo.contents) == 3:
        body_pat = parse_query(combo.contents[2])
    else:
        body_pat = EmptyQPat()
    return QRule(concl_pat, body_pat)

def parse_all_qrules(combos: List[TokenCombo]):
    return [parse_qrule(subcombo) for subcombo in combos]

'''special form: and'''

class AndQExpr(SpecialQExpr):
    def __init__(self, token: Token, contents: List[QExpression]):
        super().__init__(token)
        self.contents = contents      

def parse_compound_qexpr_and(combo: TokenList):
    if len(combo.contents) < 3:
        raise SchemeParserError(combo.anchor, 'and special form need at least 3 terms')
    contents = [parse_qexpr(subcomb) for subcomb in combo.contents[1:]]
    return AndQExpr(combo.anchor, contents)

def parse_qexpr_forbid_and(qexpr: AndQExpr, forbid_types: List[Type]):
    parse_qexpr_forbid_self(qexpr, forbid_types)
    for subqexpr in qexpr.contents:
        parse_qexpr_forbid(subqexpr, forbid_types)
      
def parse_qexpr_unbound_and(qexpr: AndQExpr, depth: int, seen_variables: Set[str]):
    for subqexpr in qexpr.contents:
        parse_qexpr_unbound_recursive(subqexpr, depth, seen_variables)

class AndQPat(QPattern):
    def __init__(self, contents: List[QPattern]):
        self.contents = contents  

def parse_qpattern_and(qexpr: AndQExpr):
    contents = [parse_qpattern(subqexpr) for subqexpr in qexpr.contents]
    return AndQPat(contents)

'''special form: or'''

class OrQExpr(SpecialQExpr):
    def __init__(self, token: Token, contents: List[QExpression]):
        super().__init__(token)
        self.contents = contents      

def parse_compound_qexpr_or(combo: TokenList):
    if len(combo.contents) < 3:
        raise SchemeParserError(combo.anchor, 'or special form need at least 3 terms')
    contents = [parse_qexpr(subcomb) for subcomb in combo.contents[1:]]
    return OrQExpr(combo.anchor, contents)

def parse_qexpr_forbid_or(qexpr: OrQExpr, forbid_types: List[Type]):
    parse_qexpr_forbid_self(qexpr, forbid_types)
    for subqexpr in qexpr.contents:
        parse_qexpr_forbid(subqexpr, forbid_types)
      
def parse_qexpr_unbound_or(qexpr: OrQExpr, depth: int, seen_variables: Set[str]):
    for subqexpr in qexpr.contents:
        parse_qexpr_unbound_recursive(subqexpr, depth, seen_variables)

class OrQPat(QPattern):
    def __init__(self, contents: List[QPattern]):
        self.contents = contents  

def parse_qpattern_or(qexpr: OrQExpr):
    contents = [parse_qpattern(subqexpr) for subqexpr in qexpr.contents]
    return OrQPat(contents)

'''special form: not'''

class NotQExpr(SpecialQExpr):
    def __init__(self, token: Token, content: QExpression):
        super().__init__(token)
        self.content = content      

def parse_compound_qexpr_not(combo: TokenList):
    if len(combo.contents) != 2:
        raise SchemeParserError(combo.anchor, 'not special form need exactly 2 terms')
    content = parse_qexpr(combo.contents[1])
    return NotQExpr(combo.anchor, content)

def parse_qexpr_forbid_not(qexpr: NotQExpr, forbid_types: List[Type]):
    parse_qexpr_forbid_self(qexpr, forbid_types)
    parse_qexpr_forbid(qexpr.content, forbid_types)
      
def parse_qexpr_unbound_not(qexpr: NotQExpr, depth: int, seen_variables: Set[str]):
    parse_qexpr_unbound_recursive(qexpr.content, depth+1, seen_variables)

class NotQPat(QPattern):
    def __init__(self, content: QPattern):
        self.content = content  

def parse_qpattern_not(qexpr: NotQExpr):
    content = parse_qpattern(qexpr.content)
    return NotQPat(content)

'''special form'''

class PredQExpr(SpecialQExpr):
    def __init__(self, token: Token, operator: Token, operands: List[QExpression]):
        super().__init__(token)
        self.operator = operator
        self.operands = operands

def parse_compound_qexpr_pred(combo: TokenList):
    if len(combo.contents) < 2:
        raise SchemeParserError(combo.anchor, 'lisp-value special form need at least 2 terms')
    if combo.contents[1].anchor.tag != TokenTag.SYMBOL:
        raise SchemeParserError(combo.anchor, 'lisp-value special form must have a symbolic operator name')
    operator = combo.contents[1].anchor
    operands = [parse_qexpr(subqexpr) for subqexpr in combo.contents[2:]]
    return PredQExpr(combo.anchor, operator, operands)

def parse_qexpr_forbid_pred(qexpr: PredQExpr, forbid_types: List[Type]):
    parse_qexpr_forbid_self(qexpr, forbid_types)
    for subqexpr in qexpr.operands:
        parse_qexpr_forbid(subqexpr, forbid_types)
      
def parse_qexpr_unbound_pred(qexpr: PredQExpr, depth: int, seen_variables: Set[str]):
    for subqexpr in qexpr.operands:
        parse_qexpr_unbound_recursive(subqexpr, depth+1, seen_variables)

class PredQPat(QPattern):
    def __init__(self, operator: str, operands: List[QPattern]):
        self.operator = operator  
        self.operands = operands  

def parse_qpattern_pred(qexpr: PredQExpr):
    operands = [parse_qpattern(subqexpr) for subqexpr in qexpr.operands]
    return PredQPat(qexpr.operator.literal, operands)

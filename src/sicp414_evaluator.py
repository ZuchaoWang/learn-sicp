'''
the goal is to implement a simplified scheme language
it's only a toy, which will not follow the language specification
and only support a small proportion of the feautres
no guarantee for performance, or even correctness (we have so few tests)

the input of the language is a string, which will be transformed to tokens via Scanner
then Parser transforms a list of tokens to several trees of tokens called token combos
the combos are then parsed to expression tree, including symbol, call, if, define_var, ...
the root of the resultant tree is a sequence expression, emcompassing all top level expressions
finally this expression tree is evaluated directly

we use simple class to represent token, expression, value
token is so simple and not likely to change, so we use single class for it, and add stringify method directly as __str__
expression and value are extensible, so we use more complex strategy
we use different derived class for different types, to facilitate static type checking
we implement operations (stringify, is_equal, quote, evaluate) as functions outside class, because in-class methods are difficult to extend

this functions are extensible by rules, and the rules are defined in global variable to defer configuration
e.g. we can define prim_equal() based on is_equal(), then update_is_equal_rules() later 
  if we were to recreate the rules every time, we have to first define is_equal() with rules, then define prim_equal() with is_equal()
  each time we need to create a class instance or a closure
'''

import sys
import inspect
import enum
from typing import Any, Callable, ClassVar, Dict, List, Optional, Set, Type, TypeVar, Union, cast


'''basic formatting'''


def format_float(x: float):
    if (x == int(x)):
        return '%d' % x
    else:
        return '%.3f' % x


def format_bool(x: bool):
    return '#t' if x else '#f'


'''dynamic dispatching by type'''


def find_type(cur_type: Type[object], type_dict: Dict[Type, Any]):
    '''searching cur_type in the type hierarchy, until finding a base class in type_dict'''
    while cur_type != object:
        if cur_type in type_dict:
            return cur_type
        else:
            cur_type = cur_type.__base__
    return cur_type


'''
global config

with suppress_panic being True
error will not exit process directly
instead error is turned into panic, handled by test_one

with suppress_print being True
print will not go to console directly
instead it is buffer, and later explicitly dumps as string

both make test easier
'''

scheme_config = {
    'suppress_panic': True,
    'suppress_print': True
}


class SchemePanic(Exception):
    def __init__(self, message: str):
        self.message = message


def scheme_panic(message: str):
    if scheme_config['suppress_panic']:
        raise SchemePanic(message)
    else:
        print(message, file=sys.stderr)
        exit(1)


_scheme_buf: List[str] = []


def scheme_print(message: str):
    if scheme_config['suppress_print']:
        _scheme_buf.append(message)
    else:
        print(message, end='')


def scheme_flush():
    res = ''.join(_scheme_buf)
    _scheme_buf.clear()
    return res


'''
scheme scanner: string -> tokens
only support paranthesis, quote, symbol, string, number, boolean
string does not support backslash escaped string character
we do not generate EOF token, because it seems unnecessary
ref: https://craftinginterpreters.com/scanning.html
'''


@enum.unique
class TokenTag(enum.Enum):
    LEFT_PAREN = enum.auto()
    RIGHT_PAREN = enum.auto()
    QUOTE = enum.auto()
    DOT = enum.auto()
    SYMBOL = enum.auto()
    STRING = enum.auto()
    NUMBER = enum.auto()
    BOOLEAN = enum.auto()

    '''
    ROOT is only to be used in parser for root level sequence expression
    will have line=0, lexeme='', literal=None
    '''
    ROOT = enum.auto()


class Token:
    '''token is simple and relatively fixed, we won't use different classes'''

    def __init__(self, tag: TokenTag, line: int, lexeme: str, literal):
        self.tag = tag
        self.line = line
        self.lexeme = lexeme
        self.literal = literal


def stringify_token(token: Token):
    if token.tag == TokenTag.NUMBER:
        return format_float(token.literal)
    elif token.tag == TokenTag.STRING or token.tag == TokenTag.SYMBOL:
        return token.literal
    elif token.tag == TokenTag.BOOLEAN:
        return format_bool(token.literal)
    else:
        return token.lexeme


def stringify_token_full(token: Token):
    if token.tag == TokenTag.NUMBER:
        return '%s:%s' % (token.tag.name, format_float(token.literal))
    elif token.tag == TokenTag.STRING or token.tag == TokenTag.SYMBOL:
        return '%s:%s' % (token.tag.name, token.literal)
    elif token.tag == TokenTag.BOOLEAN:
        return '%s:%s' % (token.tag.name, format_bool(token.literal))
    else:
        return token.tag.name


class SchemeScannerError(Exception):
    def __init__(self, line: int, message: str):
        self.line = line
        self.message = message

    def __str__(self) -> str:
        return 'scanner error in line %d: %s' % (self.line+1, self.message)


class Scanner:
    # class vars
    _invalid_nonstring_chars: ClassVar[Set[str]] = set(
        ''.split('[]{}\"\',`;|\\'))

    # instance vars
    _source: str
    _start: int
    _current: int
    _line: int
    _tokens: List[Token]

    def __init__(self):
        self._restart('')

    def scan(self, source: str):
        self._restart(source)
        try:
            while(not self._is_at_end()):
                self._scan_one_token()
                self._start = self._current
        except SchemeScannerError as err:
            scheme_panic(str(err))
        return self._tokens

    def _restart(self, source: str):
        self._source = source
        self._start = 0
        self._current = 0
        self._line = 0
        self._tokens: List[Token] = []

    def _scan_one_token(self):
        c = self._advance()
        if c == '(':
            self._add_token(TokenTag.LEFT_PAREN)
        elif c == ')':
            self._add_token(TokenTag.RIGHT_PAREN)
        elif c == '\'':
            self._scan_quote()
        elif c == '.':
            self._scan_dot()
        elif c == '"':
            self._scan_string()
        elif c == '\n':
            self._scan_newline()
        elif not c.isspace():
            self._scan_nonstring()

    def _is_at_end(self):
        return self._current >= len(self._source)

    def _advance(self):
        c = self._source[self._current]
        self._current += 1
        return c

    def _peek(self):
        return self._source[self._current]

    def _add_token(self, tag: TokenTag, literal=None):
        lexeme = self._source[self._start:self._current]
        self._tokens.append(Token(tag, self._line, lexeme, literal))

    def _scan_quote(self):
        if self._is_at_end():
            self._error('quote should not be at the end')
        elif self._peek().isspace():
            self._error('quote should not be followed by space')
        else:
            self._add_token(TokenTag.QUOTE, 'quote')

    def _scan_dot(self):
        if self._is_at_end():
            self._error('dot should not be at the end')
        elif not self._peek().isspace():
            self._error('dot should be followed by space')
        else:
            self._add_token(TokenTag.DOT)

    def _scan_string(self):
        while not self._is_at_end() and self._peek() != '"':
            if self._peek() == '\n':
                self._scan_newline()
            self._advance()

        if self._is_at_end():
            self._error('unterminated string: %s' %
                        self._source[self._start:self._current])

        # consume ending "
        self._advance()

        # trim the surrounding quotes
        literal = self._source[self._start+1:self._current-1]
        self._add_token(TokenTag.STRING, literal)

    def _scan_newline(self):
        self._line += 1

    def _scan_nonstring(self):
        while not self._is_at_end() and not Scanner._can_terminate_nonstring(self._peek()):
            c = self._advance()
            if c in Scanner._invalid_nonstring_chars:
                self._error('invalid nonstring: %s' %
                            self._source[self._start:self._current])
        substr = self._source[self._start:self._current]
        # first try boolean
        if substr[0] == '#':
            if substr == '#t':
                self._add_token(TokenTag.BOOLEAN, True)
            elif substr == '#f':
                self._add_token(TokenTag.BOOLEAN, False)
            else:
                self._error('invalid boolean: %s' % substr)
        else:
            # then try number
            try:
                literal = float(substr)
                self._add_token(TokenTag.NUMBER, literal)
            except:
                # finally try symbol
                literal = substr
                if literal[0].isnumeric():
                    self._error(
                        'symbol should not start with number: %s' % literal)
                self._add_token(TokenTag.SYMBOL, literal)

    def _error(self, message: str):
        raise SchemeScannerError(self._line, message)

    @staticmethod
    def _can_terminate_nonstring(c: str):
        return c.isspace() or c == '(' or c == ')'


_scanner = Scanner()


def scan_source(source: str):
    return _scanner.scan(source)


'''
parse token from list to tree structure called combo, can be token, list or quote
the result is a list of token combos
'''


class SchemeParserError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self) -> str:
        return 'parser error at %s in line %d: %s' % (stringify_token_full(self.token), self.token.line+1, self.message)


class TokenCombo:
    '''combo means combination'''
    def __init__(self, anchor: Token):
        self.anchor = anchor

class TokenLiteral(TokenCombo):
    def __init__(self, anchor: Token):
        super().__init__(anchor)


class TokenQuote(TokenCombo):
    def __init__(self, anchor: Token, content: TokenCombo):
        super().__init__(anchor)
        self.content = content


class TokenList(TokenCombo):
    def __init__(self, anchor: Token, contents: List[TokenCombo]):
        super().__init__(anchor)
        self.contents = contents


def stringify_token_combo(combo: TokenCombo):
    if isinstance(combo, TokenLiteral):
        return stringify_token(combo.anchor)
    elif isinstance(combo, TokenQuote):
        return '\'' + stringify_token_combo(combo.content)
    else:
        assert isinstance(combo, TokenList)
        return '(%s)' % (' '.join([stringify_token_combo(subcombo) for subcombo in combo.contents]))


TokenParserFuncType = Callable[[Token], TokenCombo]


class TokenParser:
    '''
    the first phase of parsing: token list -> token trees
    it extract tree structure from input token list, in a bottom-up manner
    the result is a list of combos, which can be further parsed to expressions, or values, or ...

    it's a very simple recursive descent, see how _parse_quote and _parse_left_paren call _parse_recursive
    ref: https://craftinginterpreters.com/parsing-expressions.html

    combo -> literal | quote | list;
    literal -> SYMBOL | STRING | NUMBER
    quote -> QUOTE combo;
    list -> LEFT_PAREN ( combo )* RIGHT_PAREN;
    '''

    _rules: Dict[TokenTag, TokenParserFuncType]
    _tokens: List[Token]
    _current: int

    def __init__(self):
        self._rules = {
            TokenTag.SYMBOL: self._parse_literal,
            TokenTag.NUMBER: self._parse_literal,
            TokenTag.STRING: self._parse_literal,
            TokenTag.BOOLEAN: self._parse_literal,
            TokenTag.DOT: self._parse_literal,
            TokenTag.QUOTE: self._parse_quote,
            TokenTag.LEFT_PAREN: self._parse_left_paren,
            TokenTag.RIGHT_PAREN: self._parse_right_paren
        }
        self._list_rules = {}
        self._restart([])

    def parse(self, tokens: List[Token]):
        self._restart(tokens)
        combos: List[TokenCombo] = []
        try:
            while not self._is_at_end():
                combo = self._parse_recursive()
                combos.append(combo)
        except SchemeParserError as err:
            scheme_panic(str(err))
        return combos
        
    def _restart(self, tokens: List[Token]):
        self.tokens = tokens
        self.current = 0

    def _parse_recursive(self) -> TokenCombo:
        token = self._advance()
        return self._rules[token.tag](token)

    def _parse_literal(self, token: Token):
        return TokenLiteral(token)

    def _parse_quote(self, token: Token):
        if self._is_at_end():
            raise SchemeParserError(token, 'quote cannot be at the end')
        if self._peek().tag == TokenTag.RIGHT_PAREN:
            raise SchemeParserError(token, 'quote cannot be at list end')
        content = self._parse_recursive()
        return TokenQuote(token, content)

    def _parse_left_paren(self, token: Token):
        contents: List[TokenCombo] = []
        while not self._is_at_end() and self._peek().tag != TokenTag.RIGHT_PAREN:
            contents.append(self._parse_recursive())
        if self._is_at_end() or self._peek().tag != TokenTag.RIGHT_PAREN:
            raise SchemeParserError(token, 'list missing right parenthesis')
        self._advance()  # consume right parenthesis
        self._check_dots(contents)
        return TokenList(token, contents)

    def _parse_right_paren(self, token: Token):
        raise SchemeParserError(token, 'unmatched right parenthesis')

    def _is_at_end(self):
        return self.current >= len(self.tokens)

    def _advance(self):
        token = self.tokens[self.current]
        self.current += 1
        return token

    def _peek(self):
        return self.tokens[self.current]

    def _check_dots(self, combos: List[TokenCombo]):
        '''one list can have at most one dot, if exist the dot should be at position -2'''
        dot_indices = [index for (index, subcombo) in enumerate(combos) if subcombo.anchor.tag == TokenTag.DOT]
        dot_num = len(dot_indices)
        if dot_num > 1:
            raise SchemeParserError(combos[dot_indices[-1]].anchor, 'one list can have at most one dot, now %d' % dot_num)
        elif dot_num == 1 and dot_indices[-1] != len(combos)-2:
            raise SchemeParserError(combos[dot_indices[-1]].anchor, 'dot should be at -2 position of list')



_token_parser = TokenParser()

def parse_tokens(tokens: List[Token]):
    combos = _token_parser.parse(tokens)
    return combos


'''
the second phase of parsing turns token combos into expressions
it build expression tree from top down, and the tree root is still the top level SequenceExpr

notice expressions under quote should not be parsed in this phase, it remains as tokenCombo
because when executed they will be turned into value, so no syntax is relevant
'''


class Expression:
    pass


'''GenericExpr seem to equivalent to Any, maybe later implementation will fix this'''
GenericExpr = TypeVar('GenericExpr', bound=Expression)

ParseExprFuncType = Callable[[TokenCombo], Expression]

_parse_expr_rules: Dict[str, ParseExprFuncType] = {}

def update_parse_expr_rules(rules: Dict[str, ParseExprFuncType]):
    _parse_expr_rules.update(rules)

def parse_expr_recursive(combo: TokenCombo) -> Expression:
    if isinstance(combo, TokenList):
        if len(combo.contents) == 0:
            return _parse_expr_rules['#nil'](combo)
        else:
            head = combo.contents[0]
            if isinstance(head, TokenLiteral):
                if head.anchor.tag == TokenTag.SYMBOL:
                    symbol_name = head.anchor.literal
                    if symbol_name in _parse_expr_rules:
                        return _parse_expr_rules[symbol_name](combo)
                else:
                    raise SchemeParserError(head.anchor, 'list cannot start with %s' % head.anchor.tag.name)
            return _parse_expr_rules['#call'](combo)
    elif isinstance(combo, TokenQuote):
        return _parse_expr_rules['#quote'](combo)
    else:
        assert isinstance(combo, TokenLiteral)
        return _parse_expr_rules['#literal'](combo)

class SequenceExpr(Expression):
    '''
    can be all top-level code, or a begin expression, or procedure body
    keyword is either a ROOT token, or the begin keyword, or the LEFT_PAREN
    
    notice: procedure parameters is not SequenceExpr
    '''

    def __init__(self, keyword: Token, contents: List[Expression]):
        self.keyword = keyword
        self.contents = contents

def parse_expr(combos: List[TokenCombo]):
    try:
        expressions: List[Expression] = []
        for combo in combos:
            expr = parse_expr_recursive(combo)
            expressions.append(expr)
    except SchemeParserError as err:
        scheme_panic(str(err))
    root_token = Token(TokenTag.ROOT, 0, '', None)
    return SequenceExpr(root_token, expressions)


'''
define different types of expressions as difference classes for better type checking
conplex syntax are just represented as list, e.g. if, define, begin
see chap 4.1.2

we store the source code position in expression as much as possible
every expression will have a token marking its position
symbol, number, string, bool expression's token is obvious
most list-type expression's token will be the keyword, i.e. first symbol in list
call and nil's token will be LEFT_PAREN, top level sequence's token will be ROOT

in case of desugaring, expression can be created without token, in such case we approximate its position
for example, when parsing let, the generated lambda and call's token will be the "let" keyword

this is different from that in crafting interpreter, where token are only stored where resolution/runtime error reporting is needed
in that case, we only need SymbolExpr, CallExpr, DefineVarExpr, DefineProcExpr and LambdaExpr to store token
SymbolExpr need to store the SYMBOL token, because it needs to check if symbol defined or initialized legally
CallExpr need to store the LEFT_PAREN token, because it needs to check parameter arity
DefineVarExpr and DefineProcExpr may store the name SYMBOL token
DefineProcExpr and LambdaExpr may store parameters SYMBOL token
ref: https://craftinginterpreters.com/appendix-ii.html
'''


class SymbolExpr(Expression):
    def __init__(self, name: Token):
        self.name = name


class StringExpr(Expression):
    def __init__(self, value: Token):
        self.value = value


class NumberExpr(Expression):
    def __init__(self, value: Token):
        self.value = value


class BooleanExpr(Expression):
    def __init__(self, value: Token):
        self.value = value


_parse_expr_literal_rules: Dict[TokenTag, Callable[[Token], Expression]] = {
    TokenTag.SYMBOL: lambda token: SymbolExpr(token),
    TokenTag.STRING: lambda token: StringExpr(token),
    TokenTag.NUMBER: lambda token: NumberExpr(token),
    TokenTag.BOOLEAN: lambda token: BooleanExpr(token),
}

def parse_literal(combo: TokenLiteral):
    anchor = combo.anchor
    if anchor.tag in _parse_expr_literal_rules:
        f = _parse_expr_literal_rules[anchor.tag]
        return f(anchor)
    else:
        raise SchemeParserError(anchor, 'unexpected token type')


class QuoteExpr(Expression):
    '''
    keyword can be either single quote, or LEFT_PAREN, depending which syntax is used
    content is token combo, only turning into value at runtime
    '''

    def __init__(self, keyword: Token, content: TokenCombo):
        self.keyword = keyword
        self.content = content


def parse_check_dot_in_quote(combo: TokenCombo):
    if isinstance(combo, TokenLiteral):
        if combo.anchor.tag == TokenTag.DOT:
            raise SchemeParserError(combo.anchor, 'cannot have free or header dot within quote')
    elif isinstance(combo, TokenQuote):
        parse_check_dot_in_quote(combo.content)
    else:
        assert isinstance(combo, TokenList)
        for (i, subcombo) in enumerate(combo.contents):
            if i == 0 or not isinstance(subcombo, TokenLiteral):
                parse_check_dot_in_quote(subcombo)


def parse_quote(combo: TokenQuote):
    parse_check_dot_in_quote(combo.content)
    return QuoteExpr(combo.anchor, combo.content)


class NilExpr(Expression):
    def __init__(self, paren: Token):
        self.paren = paren


def parse_list_nil(combo: TokenList):
    return NilExpr(combo.anchor)


class CallExpr(Expression):
    def __init__(self, paren: Token, operator: Expression, operands: List[Expression]):
        self.paren = paren
        self.operator = operator
        self.operands = operands


def parse_list_call(combo: TokenList):
    if len(combo.contents) == 0:
        raise SchemeParserError(combo.anchor, 'call should not be empty')
    operator_expr = parse_expr_recursive(combo.contents[0])
    operand_exprs = [parse_expr_recursive(subcombo) for subcombo in combo.contents[1:]]
    return CallExpr(combo.anchor, operator_expr, operand_exprs)


def parse_sub_symbol_token(combo: TokenCombo, prefix: str):
    if isinstance(combo, TokenLiteral):
        anchor = cast(TokenLiteral, combo).anchor
        if anchor.tag == TokenTag.SYMBOL:
            return anchor
    raise SchemeParserError(anchor, '%s should be symbol, now %s' % (prefix, anchor.tag.name))


def parse_list_quote(combo: TokenList):
    if len(combo.contents) != 2:
        raise SchemeParserError(combo.anchor, 'quote should have 2 expressions, now %d' % len(combo.contents))
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    # should not recursively parse expressions under QuoteExpr, but should check it
    parse_check_dot_in_quote(combo.contents[1])
    return QuoteExpr(keyword, combo.contents[1])


class SetExpr(Expression):
    def __init__(self, keyword: Token, name: Token, initializer: Expression):
        self.keyword = keyword
        self.name = name
        self.initializer = initializer
        

def parse_list_set(combo: TokenList):
    if len(combo.contents) != 3:
        raise SchemeParserError(
            combo.anchor, 'set should have 3 expressions, now %d' % len(combo.contents))
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    name = parse_sub_symbol_token(combo.contents[1], 'name')
    initializer = parse_expr_recursive(combo.contents[2])
    return SetExpr(keyword, name, initializer)


class DefineVarExpr(Expression):
    def __init__(self, keyword: Token, name: Token, initializer: Expression):
        self.keyword = keyword
        self.name = name
        self.initializer = initializer


class DefineProcExpr(Expression):
    def __init__(self, keyword: Token, name: Token, pos_paras: List[Token], rest_para: Optional[Token], body: SequenceExpr):
        self.keyword = keyword
        self.name = name
        self.pos_paras = pos_paras
        self.rest_para = rest_para
        self.body = body


def check_duplicate_parameters(parameters: List[Token]):
    '''if duplicate, return the second token; otherwise return None'''
    unq: Set[str] = set([])
    for p in parameters:
        if p.literal in unq:
            return p
        else:
            unq.add(p.literal)
    return None


def parse_parameters(combos: List[TokenCombo]):
    pos_combos = combos
    rest_para = None
    if len(combos) >= 2 and combos[-2].anchor.tag == TokenTag.DOT:
        pos_combos = combos[:-2]
        rest_para = parse_sub_symbol_token(combos[-1], 'rest parameter')
    pos_paras = [parse_sub_symbol_token(subcombo, 'positional parameter') for subcombo in pos_combos]
    para_dup = check_duplicate_parameters(pos_paras if rest_para is None else [*pos_paras, rest_para])
    if para_dup is not None:
        raise SchemeParserError(para_dup, 'parameter show up twice')
    return pos_paras, rest_para


def parse_list_define(combo: TokenList):
    if len(combo.contents) < 3:
        raise SchemeParserError(
            combo.anchor, 'define should have at least 3 expressions, now %d' % len(combo.contents))
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    subcombo1 = combo.contents[1]
    if isinstance(subcombo1, TokenLiteral) and subcombo1.anchor.tag == TokenTag.SYMBOL:  # define variable
        name = parse_sub_symbol_token(subcombo1, 'define variable name')
        if len(combo.contents) != 3:
            raise SchemeParserError(
                combo.anchor, 'define variable should have 3 expressions, now %d' % len(combo.contents))
        initializer = parse_expr_recursive(combo.contents[2])
        return DefineVarExpr(keyword, name, initializer)
    elif isinstance(subcombo1, TokenList):  # define procedure
        if len(subcombo1.contents) == 0:
            raise SchemeParserError(
                combo.anchor, 'define procedure should provide name')
        subcombo10 = subcombo1.contents[0]
        name = parse_sub_symbol_token(subcombo10, 'define procedure name')
        pos_paras, rest_para = parse_parameters(subcombo1.contents[1:])
        body = SequenceExpr(combo.anchor, [parse_expr_recursive(subcombo) for subcombo in combo.contents[2:]])
        return DefineProcExpr(keyword, name, pos_paras, rest_para, body)
    else:
        raise SchemeParserError(combo.anchor, 'define 2nd expression should be symbol or list')


class IfExpr(Expression):
    def __init__(self, keyword: Token, pred: Expression, then_branch: Expression, else_branch: Optional[Expression]):
        self.keyword = keyword
        self.pred = pred
        self.then_branch = then_branch
        self.else_branch = else_branch


def parse_list_if(combo: TokenList):
    if len(combo.contents) != 3 and len(combo.contents) != 4:
        raise SchemeParserError(
            combo.anchor, 'if should have 3 or 4 expressions, now %d' % len(combo.contents))
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    pred_expr = parse_expr_recursive(combo.contents[1])
    then_expr = parse_expr_recursive(combo.contents[2])
    else_expr = None
    if len(combo.contents) == 4:
        else_expr = parse_expr_recursive(combo.contents[3])
    return IfExpr(keyword, pred_expr, then_expr, else_expr)


def parse_list_begin(combo: TokenList):
    if len(combo.contents) < 2:
        raise SchemeParserError(
            combo.anchor, 'begin should have at least 2 expressions, now %d' % len(combo.contents))
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    contents = [parse_expr_recursive(subcombo) for subcombo in combo.contents[1:]]
    return SequenceExpr(keyword, contents)


class LambdaExpr(Expression):
    def __init__(self, keyword: Token, pos_paras: List[Token], rest_para: Optional[Token], body: SequenceExpr):
        self.keyword = keyword
        self.pos_paras = pos_paras
        self.rest_para = rest_para
        self.body = body


def parse_list_lambda(combo: TokenList):
    if len(combo.contents) < 3:
        raise SchemeParserError(
            combo.anchor, 'lambda should have at least 3 expressions, now %d' % len(combo.contents))
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    subcombo1 = combo.contents[1]
    if isinstance(subcombo1, TokenList):
        pos_paras, rest_para = parse_parameters(subcombo1.contents)
        body = SequenceExpr(combo.anchor, [parse_expr_recursive(subcombo) for subcombo in combo.contents[2:]])
        return LambdaExpr(keyword, pos_paras, rest_para, body)
    else:
        raise SchemeParserError(combo.anchor, 'lambda 2nd expression should be list')


def parse_list_let(combo: TokenList):
    '''
    desugar let to lambda and call
    call.paren = let.paren, lambda.keyword = let.keyword
    '''
    if len(combo.contents) < 3:
        raise SchemeParserError(
            combo.anchor, 'let should have at least 3 expressions, now %d' % len(combo.contents))
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    subcombo1 = combo.contents[1]
    if isinstance(subcombo1, TokenList):
        if not all([isinstance(subcombo, TokenList) for subcombo in subcombo1.contents]):
            raise SchemeParserError(combo.anchor, 'let 2nd expression should be list of list')
        names_and_intializers = [cast(TokenList, subcombo).contents for subcombo in subcombo1.contents]
        if not all([len(combo_pair) == 2 for combo_pair in names_and_intializers]):
            raise SchemeParserError(combo.anchor, 'let 2nd expression should be list of list of 2 expressions')
        pos_paras, rest_para = parse_parameters([expr_pair[0] for expr_pair in names_and_intializers])
        body = SequenceExpr(combo.anchor, [parse_expr_recursive(subcombo) for subcombo in combo.contents[2:]])
        operator = LambdaExpr(keyword, pos_paras, rest_para, body)
        operands = [parse_expr_recursive(combo_pair[1]) for combo_pair in names_and_intializers]
        return CallExpr(combo.anchor, operator, operands)
    else:
        raise SchemeParserError(
            combo.anchor, 'let 2nd expression should be list, now %s' % type(subcombo1).__name__)


class AndExpr(Expression):
    def __init__(self, keyword: Token, contents: List[Expression]):
        self.keyword = keyword
        self.contents = contents


def parse_list_and(combo: TokenList):
    if len(combo.contents) < 3:
        raise SchemeParserError(
            combo.anchor, 'and should have at least 3 expressions, now %d' % len(combo.contents))
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    contents = [parse_expr_recursive(subcombo) for subcombo in combo.contents[1:]]
    return AndExpr(keyword, contents)


class OrExpr(Expression):
    def __init__(self, keyword: Token, contents: List[Expression]):
        self.keyword = keyword
        self.contents = contents


def parse_list_or(combo: TokenList):
    if len(combo.contents) < 3:
        raise SchemeParserError(
            combo.anchor, 'or should have at least 3 expressions, now %d' % len(combo.contents))
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    contents = [parse_expr_recursive(subcombo) for subcombo in combo.contents[1:]]
    return OrExpr(keyword, contents)


class NotExpr(Expression):
    def __init__(self, keyword: Token, content: Expression):
        self.keyword = keyword
        self.content = content


def parse_list_not(combo: TokenList):
    if len(combo.contents) != 2:
        raise SchemeParserError(
            combo.anchor, 'not should have 2 expressions, now %d' % len(combo.contents))
    keyword = parse_sub_symbol_token(combo.contents[0], 'keyword')
    content = parse_expr_recursive(combo.contents[1])
    return NotExpr(keyword, content)


def install_parse_expr_rules():
    '''
    we use #nil instead of nil, #call instead of call
    because #nil and #call are both invalid tokens
    this forbids the syntax of (#nill blabla) and (#call blabla)
    '''
    rules = {
        '#literal': parse_literal,
        '#quote': parse_quote,
        '#nil': parse_list_nil,
        '#call': parse_list_call,
        'quote': parse_list_quote,
        'set!': parse_list_set,
        'define': parse_list_define,
        'if': parse_list_if,
        'begin': parse_list_begin,
        'lambda': parse_list_lambda,
        'let': parse_list_let,
        'and': parse_list_and,
        'or': parse_list_or,
        'not': parse_list_not
    }
    update_parse_expr_rules(rules)


'''expression stringifier'''

StringifyExprFuncType = Callable[[Expression], str]

_stringify_expr_rules: Dict[Type, StringifyExprFuncType] = {}


def update_stringify_expr_rules(rules: Dict[Type, StringifyExprFuncType]):
    _stringify_expr_rules.update(rules)


def stringify_expr(expr: Expression):
    t = find_type(type(expr), _stringify_expr_rules)
    f = _stringify_expr_rules[t]
    return f(expr)


StringifyExprRuleType = Union[
    Callable[[], str],
    Callable[[GenericExpr], str],
]


def stringify_expr_rule_decorator(rule_func: StringifyExprRuleType):
    arity = len(inspect.getfullargspec(rule_func).args)

    def _stringify_expr_rule_wrapped(expr: Expression):
        args: List[Any] = [expr]
        return rule_func(*args[0:arity])
    return _stringify_expr_rule_wrapped


@stringify_expr_rule_decorator
def stringify_expr_symbol(expr: SymbolExpr):
    return expr.name.literal


@stringify_expr_rule_decorator
def stringify_expr_string(expr: StringExpr):
    return '"%s"' % expr.value.literal


@stringify_expr_rule_decorator
def stringify_expr_number(expr: NumberExpr):
    return format_float(expr.value.literal)


@stringify_expr_rule_decorator
def stringify_expr_boolean(expr: BooleanExpr):
    return format_bool(expr.value.literal)


@stringify_expr_rule_decorator
def stringify_expr_sequence(expr: SequenceExpr):
    substrs = [stringify_expr(subexpr) for subexpr in expr.contents]
    substrs = ['sequence', *substrs]
    return '(%s)' % (' '.join(substrs))


@stringify_expr_rule_decorator
def stringify_expr_quote(expr: QuoteExpr):
    substrs = ['quote', stringify_token_combo(expr.content)]
    return '(%s)' % (' '.join(substrs))


@stringify_expr_rule_decorator
def stringify_expr_nil(expr: NilExpr):
    return '(nil)'


@stringify_expr_rule_decorator
def stringify_expr_call(expr: CallExpr):
    operator_substr = stringify_expr(expr.operator)
    operands_substrs = [stringify_expr(subexpr) for subexpr in expr.operands]
    substrs = ['call', operator_substr, *operands_substrs]
    return '(%s)' % (' '.join(substrs))


@stringify_expr_rule_decorator
def stringify_expr_set(expr: SetExpr):
    substrs = ['set', expr.name.literal, stringify_expr(expr.initializer)]
    return '(%s)' % (' '.join(substrs))


@stringify_expr_rule_decorator
def stringify_expr_define_var(expr: DefineVarExpr):
    substrs = ['define-var', expr.name.literal, stringify_expr(expr.initializer)]
    return '(%s)' % (' '.join(substrs))


@stringify_expr_rule_decorator
def stringify_expr_define_proc(expr: DefineProcExpr):
    para_substrs = [token.literal for token in expr.pos_paras]
    if expr.rest_para is not None:
        para_substrs = [*para_substrs, '.', expr.rest_para.literal]
    substrs = ['define-proc', expr.name.literal, '(%s)' % (' '.join(para_substrs)), stringify_expr(expr.body)]
    return '(%s)' % (' '.join(substrs))


@stringify_expr_rule_decorator
def stringify_expr_if(expr: IfExpr):
    substrs = ['if', stringify_expr(expr.pred), stringify_expr(expr.then_branch)]
    if expr.else_branch is not None:
        substrs.append(stringify_expr(expr.else_branch))
    return '(%s)' % (' '.join(substrs))


@stringify_expr_rule_decorator
def stringify_expr_lambda(expr: LambdaExpr):
    para_substrs = [token.literal for token in expr.pos_paras]
    if expr.rest_para is not None:
        para_substrs = [*para_substrs, '.', expr.rest_para.literal]
    substrs = ['lambda', '(%s)' % (' '.join(para_substrs)), stringify_expr(expr.body)]
    return '(%s)' % (' '.join(substrs))


@stringify_expr_rule_decorator
def stringify_expr_and(expr: AndExpr):
    substrs = [stringify_expr(subexpr) for subexpr in expr.contents]
    substrs = ['and', *substrs]
    return '(%s)' % (' '.join(substrs))


@stringify_expr_rule_decorator
def stringify_expr_or(expr: OrExpr):
    substrs = [stringify_expr(subexpr) for subexpr in expr.contents]
    substrs = ['or', *substrs]
    return '(%s)' % (' '.join(substrs))


@stringify_expr_rule_decorator
def stringify_expr_not(expr: NotExpr):
    substrs = ['not', stringify_expr(expr.content)]
    return '(%s)' % (' '.join(substrs))


def install_stringify_expr_rules():
    rules = {
        SymbolExpr: stringify_expr_symbol,
        StringExpr: stringify_expr_string,
        NumberExpr: stringify_expr_number,
        BooleanExpr: stringify_expr_boolean,
        SequenceExpr: stringify_expr_sequence,
        QuoteExpr: stringify_expr_quote,
        NilExpr: stringify_expr_nil,
        CallExpr: stringify_expr_call,
        SetExpr: stringify_expr_set,
        DefineVarExpr: stringify_expr_define_var,
        DefineProcExpr: stringify_expr_define_proc,
        IfExpr: stringify_expr_if,
        LambdaExpr: stringify_expr_lambda,
        AndExpr: stringify_expr_and,
        OrExpr: stringify_expr_or,
        NotExpr: stringify_expr_not
    }
    update_stringify_expr_rules(rules)


'''
schemeval will be specified as various classes, and this helps static type checking
if we represent it as single class with different tag (like token), we won't have type checking with python's typing
'''

class SchemeVal:
    '''
    schemeVal defaults to be truthy, including 0, (), nil
    the only thing not truthy is #f
    we should declare this with vode below, but since object follows this rule, so no need to declare

    def __bool__(self) -> bool:
        return True
    '''
    pass


GenericVal = TypeVar('GenericVal', bound=SchemeVal)


class SchemeEnvError(Exception):
    def __init__(self, env: "Environment"):
        self.env = env


class Environment:
    '''
    see chap 4.1.3 and https://craftinginterpreters.com/statements-and-state.html

    should not pass {} to __init__.bindings, because this {} will be shared among different instance
    e.g. def __init__(self, bindings: Dict[str, SchemeVal]={}, enclosing: Optional["Environment"] = None):
    see: https://stackoverflow.com/questions/26320899/why-is-the-empty-dictionary-a-dangerous-default-value-in-python
    '''

    def __init__(self, bindings: Dict[str, SchemeVal], enclosing: Optional["Environment"] = None):
        self.bindings = bindings
        self.enclosing = enclosing


'''
we use functional programming style, i.e. moving all methods out of class
in this way, new operations can be easily added
'''


def _env_find(env: Environment, name: str):
    cur: Optional[Environment] = env
    while cur is not None:
        if name in cur.bindings:
            return cur
        cur = cur.enclosing
    return None


def env_define(env: Environment, name: str, sv: SchemeVal):
    env.bindings[name] = sv


def env_set(env: Environment, name: str, sv: SchemeVal):
    env = _env_find(env, name)
    if env is None:
        raise SchemeEnvError(env)
    else:
        env.bindings[name] = sv


def env_lookup(env: Environment, name: str):
    env = _env_find(env, name)
    if env is None:
        raise SchemeEnvError(env)
    else:
        return env.bindings[name]


def env_extend(env: Environment, parameter: List[str], arguments: List[SchemeVal]):
    return Environment(dict(zip(parameter, arguments)), env)



'''
scheme value definitions

value and experssion are very similar in Scheme
for example, a list can be both an object and an expression
but we still differentitate them, giving them different base class, because
undef, procedure and primitive only appears in value, not in expression
expression need to store token for debugging, value doesn't have to

because of the differentiation, we have to implement quote
to convert expression to the "same" value

empty list is represented as special nil expression
non-empty list is represented as pairs
'''


class SymbolVal(SchemeVal):
    def __init__(self, value: str):
        self.value = value


class StringVal(SchemeVal):
    def __init__(self, value: str):
        self.value = value


class NumberVal(SchemeVal):
    def __init__(self, value: float):
        self.value = value


class BooleanVal(SchemeVal):
    def __init__(self, value: bool):
        self.value = value


class NilVal(SchemeVal):
    pass


class UndefVal(SchemeVal):
    pass


class PairVal(SchemeVal):
    def __init__(self, left: SchemeVal, right: SchemeVal):
        self.left = left
        self.right = right


class PrimVal(SchemeVal):
    def __init__(self, name: str, pos_arity: int, has_rest: bool, body: Callable[..., SchemeVal]):
        self.name = name
        self.pos_arity = pos_arity
        self.has_rest = has_rest
        self.body = body


class ProcVal(SchemeVal):
    def __init__(self, name: str, pos_paras: List[str], rest_para: Optional[str], env: Environment):
        self.name = name
        self.pos_paras = pos_paras
        self.rest_para = rest_para
        self.env = env


class ProcPlainVal(ProcVal):
    '''
    A simple implementation of procedure, later we will have another representation
    its string representation inherit ProcVal's

    in crafting interpreter, the function object directly store the definition expression
    we don't do that here, because our definition can be either DefineProcExpr or LambdaExpr
    handling both types here is chaotic
    '''

    def __init__(self, name: str, pos_paras: List[str], rest_para: Optional[str], body: SequenceExpr, env: Environment):
        super().__init__(name, pos_paras, rest_para, env)
        self.body = body


'''value stringifier'''

StringifyValueFuncType = Callable[[SchemeVal], str]

_stringify_value_rules: Dict[Type, StringifyValueFuncType] = {}


def update_stringify_value_rules(rules: Dict[Type, StringifyValueFuncType]):
    _stringify_value_rules.update(rules)


def stringify_value(sv: SchemeVal):
    t = find_type(type(sv), _stringify_value_rules)
    f = _stringify_value_rules[t]
    return f(sv)


StringifyValueRuleType = Union[
    Callable[[], SchemeVal],
    Callable[[GenericVal], str],
]


def stringify_value_rule_decorator(rule_func: StringifyValueRuleType):
    arity = len(inspect.getfullargspec(rule_func).args)

    def _stringify_value_rule_wrapped(sv: SchemeVal):
        args: List[Any] = [sv]
        return rule_func(*args[0:arity])
    return _stringify_value_rule_wrapped


@stringify_value_rule_decorator
def stringify_value_symbol(sv: SymbolVal):
    return sv.value


@stringify_value_rule_decorator
def stringify_value_string(sv: StringVal):
    return sv.value


@stringify_value_rule_decorator
def stringify_value_number(sv: NumberVal):
    return format_float(sv.value)


@stringify_value_rule_decorator
def stringify_value_boolean(sv: BooleanVal):
    return format_bool(sv.value)


@stringify_value_rule_decorator
def stringify_value_nil():
    return '()'


@stringify_value_rule_decorator
def stringify_value_undef():
    return '#<undef>'


@stringify_value_rule_decorator
def stringify_value_pair(sv: PairVal):
    left_str = stringify_value(sv.left)
    right_str = stringify_value(sv.right)
    if isinstance(sv.right, NilVal):
        return '(%s)' % left_str
    elif isinstance(sv.right, PairVal):
        # right_str strip off paranthesis
        return '(%s %s)' % (left_str, right_str[1:-1])
    else:
        return '(%s . %s)' % (left_str, right_str)


@stringify_value_rule_decorator
def stringify_value_procedure(sv: ProcVal):
    return '[procedure %s]' % sv.name


@stringify_value_rule_decorator
def stringify_value_primitive(sv: PrimVal):
    return '[primitive %s]' % sv.name


def install_stringify_value_rules():
    rules = {
        SymbolVal: stringify_value_symbol,
        StringVal: stringify_value_string,
        NumberVal: stringify_value_number,
        BooleanVal: stringify_value_boolean,
        NilVal: stringify_value_nil,
        UndefVal: stringify_value_undef,
        PairVal: stringify_value_pair,
        ProcVal: stringify_value_procedure,
        PrimVal: stringify_value_primitive,
    }
    update_stringify_value_rules(rules)


'''value equality checker'''

EqualityFuncType = Callable[[SchemeVal, SchemeVal], bool]

_is_equal_rules: Dict[Type, EqualityFuncType] = {}


def update_is_equal_rules(rules: Dict[Type, EqualityFuncType]):
    _is_equal_rules.update(rules)


def is_equal(x: SchemeVal, y: SchemeVal):
    if type(x) == type(y):
        t = find_type(type(x), _is_equal_rules)
        f = _is_equal_rules[t]
        return f(x, y)
    else:
        return False


IsEqualRuleType = Union[
    Callable[[], SchemeVal],
    Callable[[GenericVal, GenericVal], str],
]


def is_equal_rule_decorator(rule_func: IsEqualRuleType):
    arity = len(inspect.getfullargspec(rule_func).args)

    def _is_equal_rule_wrapped(x: SchemeVal, y: SchemeVal):
        args: List[Any] = [x, y]
        return rule_func(*args[0:arity])
    return _is_equal_rule_wrapped


@is_equal_rule_decorator
def is_equal_literal(x: Union[SymbolVal, StringVal, NumberVal, BooleanVal], y: Union[SymbolVal, StringVal, NumberVal, BooleanVal]):
    return x.value == y.value


@is_equal_rule_decorator
def is_equal_true():
    return True


@is_equal_rule_decorator
def is_equal_object(x: Union[PairVal, PrimVal, ProcVal], y: Union[PairVal, PrimVal, ProcVal]):
    return x == y


def install_is_equal_rules():
    rules = {
        SymbolVal: is_equal_literal,
        StringVal: is_equal_literal,
        NumberVal: is_equal_literal,
        BooleanVal: is_equal_literal,
        NilVal: is_equal_true,
        UndefVal: is_equal_true,
        PairVal: is_equal_object,
        ProcVal: is_equal_object,
        PrimVal: is_equal_object,
    }
    update_is_equal_rules(rules)


'''value equality checker'''


def is_truthy(sv: SchemeVal):
    '''
    in scheme, the only thing not truthy is #f
    except that everything is truthy, including 0, "", '(), <#undef>
    '''
    return type(sv) != BooleanVal or cast(BooleanVal, sv).value == True


'''utility functions for pair value'''


def pair_from_list(fronts: List[SchemeVal], last: SchemeVal):
    head: SchemeVal = last
    for i in range(len(fronts)-1, -1, -1):
        head = PairVal(fronts[i], head)
    return head


def pair_length(sv: PairVal):
    count = 0
    head: SchemeVal = sv
    while isinstance(head, PairVal):
        count += 1
        head = head.right
    return count


'''
quoter token combo to value
'''

_quote_token_combo_literal_rules: Dict[TokenTag, Callable[[Token], SchemeVal]] = {
    TokenTag.SYMBOL: lambda token: SymbolVal(token.literal),
    TokenTag.STRING: lambda token: StringVal(token.literal),
    TokenTag.NUMBER: lambda token: NumberVal(token.literal),
    TokenTag.BOOLEAN: lambda token: BooleanVal(token.literal),
}

def quote_token_combo(combo: TokenCombo):
    if isinstance(combo, TokenLiteral):
        assert combo.anchor.tag in _quote_token_combo_literal_rules
        f = _quote_token_combo_literal_rules[combo.anchor.tag]
        return f(combo.anchor)
    elif isinstance(combo, TokenQuote):
        subvals = [SymbolVal('quote'), quote_token_combo(combo.content)]
        return pair_from_list(subvals, NilVal())
    else:
        assert isinstance(combo, TokenList)
        if len(combo.contents) >= 2 and combo.contents[-2].anchor.tag == TokenTag.DOT:
            subvals = [quote_token_combo(subcomb) for subcomb in combo.contents[:-2]]
            lastval = quote_token_combo(combo.contents[-1])
            return pair_from_list(subvals, lastval)
        else:
            subvals = [quote_token_combo(subcomb) for subcomb in combo.contents]
            return pair_from_list(subvals, NilVal())


'''evaluator'''


class SchemePrimError(Exception):
    def __init__(self, message):
        self.message = message


class SchemeRuntimeError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self) -> str:
        return 'runtime error at %s in line %d: %s' % (stringify_token_full(self.token), self.token.line+1, self.message)


EvalRecurFuncType = Callable[[Expression, Environment], SchemeVal]
EvalFuncType = Callable[[Expression, Environment, EvalRecurFuncType], SchemeVal]

_eval_rules: Dict[Type, EvalFuncType] = {}


def update_eval_rules(rules: Dict[Type, EvalFuncType]):
    _eval_rules.update(rules)

def evaluate_expr(expr: SequenceExpr, env: Environment):
    def evaluate_recursive(expr: Expression, env: Environment) -> SchemeVal:
        t = find_type(type(expr), _eval_rules)
        f = _eval_rules[t]
        return f(expr, env, evaluate_recursive)

    try:
        res = evaluate_recursive(expr, env)
    except SchemeRuntimeError as err:
        scheme_panic(str(err))
    return res


'''
evaluator rule definitions
'''

EvalRuleType = Union[
    Callable[[], SchemeVal],
    Callable[[GenericExpr], SchemeVal],
    Callable[[GenericExpr, Environment], SchemeVal],
    Callable[[GenericExpr, Environment, EvalRecurFuncType], SchemeVal],
]


def eval_rule_decorator(rule_func: EvalRuleType):
    arity = len(inspect.getfullargspec(rule_func).args)

    def _eval_rule_wrapped(expr: Expression, env: Environment, evl: EvalRecurFuncType):
        args: List[Any] = [expr, env, evl]
        return rule_func(*args[0:arity])
    return _eval_rule_wrapped


@eval_rule_decorator
def eval_sequence(expr: SequenceExpr, env: Environment, evl: EvalRecurFuncType):
    '''return the last expression'''
    res: SchemeVal = UndefVal()
    for subexpr in expr.contents:
        res = evl(subexpr, env)
    return res


@eval_rule_decorator
def eval_symbol(expr: SymbolExpr, env: Environment):
    try:
        return env_lookup(env, expr.name.literal)
    except SchemeEnvError:
        raise SchemeRuntimeError(expr.name, 'symbol undefined')


def pure_eval_string(expr: StringExpr):
    return StringVal(expr.value.literal)


@eval_rule_decorator
def eval_string(expr: StringExpr):
    return pure_eval_string(expr)


def pure_eval_number(expr: NumberExpr):
    return NumberVal(expr.value.literal)


@eval_rule_decorator
def eval_number(expr: NumberExpr):
    return pure_eval_number(expr)


def pure_eval_boolean(expr: BooleanExpr):
    return BooleanVal(expr.value.literal)


@eval_rule_decorator
def eval_boolean(expr: BooleanExpr):
    return pure_eval_boolean(expr)


def pure_eval_nil():
    '''evaluating empty list expression () gives empty list value ()'''
    return NilVal()


@eval_rule_decorator
def eval_nil():
    return pure_eval_nil()


@eval_rule_decorator
def eval_quote(expr: QuoteExpr):
    return quote_token_combo(expr.content)


def pure_check_arity(expr: CallExpr, name: str, pos_arity: int, has_rest: bool, arg_count: int):
    if has_rest:
        if arg_count < pos_arity:
            raise SchemeRuntimeError(expr.paren, '%s expect at least %d arguments, only get %d' % (name, pos_arity, arg_count))
    else:
        if arg_count != pos_arity:
            raise SchemeRuntimeError(expr.paren, '%s expect exactly %d arguments, but get %d' % (name, pos_arity, arg_count))


def pure_check_prim_arity(expr: CallExpr, operator: PrimVal, operands: List[SchemeVal]):
    pure_check_arity(expr, operator.name, operator.pos_arity, operator.has_rest, len(operands))


def pure_eval_call_prim(expr: CallExpr, operator: PrimVal, operands: List[SchemeVal]):
    pure_check_prim_arity(expr, operator, operands)
    try:
        return operator.body(*operands)
    except SchemePrimError as err:
        raise SchemeRuntimeError(expr.paren, err.message)


def pure_check_proc_arity(expr: CallExpr, operator: ProcVal, operands: List[SchemeVal]):
    pure_check_arity(expr, operator.name, len(operator.pos_paras), operator.rest_para is not None, len(operands))


def pure_eval_call_proc_extend_env(operator: ProcVal, operands: List[SchemeVal]):
    if operator.rest_para is None:
        parameters = operator.pos_paras
        arguments = operands
    else:
        parameters = [*operator.pos_paras, operator.rest_para]
        arguments = [*operands[:len(operator.pos_paras)], pair_from_list(operands[len(operator.pos_paras):], NilVal())]
    return env_extend(operator.env, parameters, arguments)


def pure_eval_call_proc_plain(expr: CallExpr, operator: ProcPlainVal, operands: List[SchemeVal], evl: EvalRecurFuncType):
    pure_check_proc_arity(expr, operator, operands)
    new_env = pure_eval_call_proc_extend_env(operator, operands)
    return evl(operator.body, new_env)


def pure_eval_call_invalid(expr: CallExpr, operator: SchemeVal):
    raise SchemeRuntimeError(
        expr.paren, 'cannot call %s value' % type(operator).__name__)


@eval_rule_decorator
def eval_call(expr: CallExpr, env: Environment, evl: EvalRecurFuncType):
    operator = evl(expr.operator, env)
    operands = [evl(subexpr, env) for subexpr in expr.operands]
    if isinstance(operator, PrimVal):
        return pure_eval_call_prim(expr, operator, operands)
    elif isinstance(operator, ProcPlainVal):
        return pure_eval_call_proc_plain(expr, operator, operands, evl)
    else:
        return pure_eval_call_invalid(expr, operator)


def pure_eval_set(name: Token, initializer: SchemeVal, env: Environment):
    try:
        env_set(env, name.literal, initializer)
        return initializer
    except SchemeEnvError:
        raise SchemeRuntimeError(name, 'symbol undefined')


@eval_rule_decorator
def eval_set(expr: SetExpr, env: Environment, evl: EvalRecurFuncType):
    '''return the value just set'''
    initializer = evl(expr.initializer, env)
    return pure_eval_set(expr.name, initializer, env)


def pure_eval_define_var(name: Token, initializer: SchemeVal, env: Environment):
    env_define(env, name.literal, initializer)
    return SymbolVal(name.literal)


def pure_eval_define_proc_plain(expr: DefineProcExpr, env: Environment):
    proc_obj = ProcPlainVal(expr.name.literal, [p.literal for p in expr.pos_paras], expr.rest_para.literal if expr.rest_para is not None else None, expr.body, env)
    env_define(env, expr.name.literal, proc_obj)
    return SymbolVal(expr.name.literal)


@eval_rule_decorator
def eval_define_var(expr: DefineVarExpr, env: Environment, evl: EvalRecurFuncType):
    '''return the symbol defined'''
    initializer = evl(expr.initializer, env)
    return pure_eval_define_var(expr.name, initializer, env)


@eval_rule_decorator
def eval_define_proc(expr: DefineProcExpr, env: Environment):
    '''return the symbol defined'''
    return pure_eval_define_proc_plain(expr, env)


@eval_rule_decorator
def eval_if(expr: IfExpr, env: Environment, evl: EvalRecurFuncType):
    '''return the successful branch'''
    pred_val = evl(expr.pred, env)
    if is_truthy(pred_val):
        return evl(expr.then_branch, env)
    elif expr.else_branch is not None:
        return evl(expr.else_branch, env)
    else:
        return UndefVal()


def pure_eval_lambda_plain(expr: LambdaExpr, env: Environment):
    return ProcPlainVal('lambda', [p.literal for p in expr.pos_paras], expr.rest_para.literal if expr.rest_para is not None else None, expr.body, env)


@eval_rule_decorator
def eval_lambda(expr: LambdaExpr, env: Environment):
    '''return the procedure itself'''
    return pure_eval_lambda_plain(expr, env)


@eval_rule_decorator
def eval_and(expr: AndExpr, env: Environment, evl: EvalRecurFuncType):
    '''return the first false, otherwise the last'''
    for subexpr in expr.contents:
        res = evl(subexpr, env)
        if not is_truthy(res):
            return res
    return res


@eval_rule_decorator
def eval_or(expr: OrExpr, env: Environment, evl: EvalRecurFuncType):
    '''return the first true, otherwise the last'''
    for subexpr in expr.contents:
        res = evl(subexpr, env)
        if is_truthy(res):
            return res
    return res


@eval_rule_decorator
def eval_not(expr: NotExpr, env: Environment, evl: EvalRecurFuncType):
    res = evl(expr.content, env)
    return BooleanVal(not is_truthy(res))


def install_eval_rules():
    '''no list rule here'''
    rules = {
        SequenceExpr: eval_sequence,
        SymbolExpr: eval_symbol,
        StringExpr: eval_string,
        NumberExpr: eval_number,
        BooleanExpr: eval_boolean,
        NilExpr: eval_nil,
        QuoteExpr: eval_quote,
        CallExpr: eval_call,
        SetExpr: eval_set,
        DefineVarExpr: eval_define_var,
        DefineProcExpr: eval_define_proc,
        IfExpr: eval_if,
        LambdaExpr: eval_lambda,
        AndExpr: eval_and,
        OrExpr: eval_or,
        NotExpr: eval_not
    }
    update_eval_rules(rules)


'''primitive definitions'''

_primitives = {}


def update_primitives(prims: Dict[str, Callable]):
    _primitives.update(prims)


def make_global_env():
    glbenv = Environment({})
    register_primitives(glbenv, _primitives)
    return glbenv


def get_py_func_arity(py_func: Callable):
    rf = inspect.getfullargspec(py_func)
    return len(rf.args), rf.varargs is not None


def register_primitives(env: Environment, primitives: Dict[str, Callable]):
    '''add a batch of primitives to environment'''
    for name in primitives:
        py_func = primitives[name]
        pos_arity, has_rest = get_py_func_arity(py_func)
        primitive = PrimVal(name, pos_arity, has_rest, py_func)
        env_define(env, name, primitive)


def make_prim_num2_num(py_func: Callable[[float, float], float]):
    def _prim_num2_num(x: SchemeVal, y: SchemeVal) -> SchemeVal:
        if not isinstance(x, NumberVal) or not isinstance(y, NumberVal):
            raise SchemePrimError('%s requires both operators to be numbers, now %s and %s' % (
                py_func.__name__, type(x), type(y)))
        x = cast(NumberVal, x)
        y = cast(NumberVal, y)
        res = py_func(x.value, y.value)
        return NumberVal(res)
    return _prim_num2_num


prim_op_add = make_prim_num2_num(lambda a, b: a+b)
prim_op_sub = make_prim_num2_num(lambda a, b: a-b)
prim_op_mul = make_prim_num2_num(lambda a, b: a*b)
prim_op_div = make_prim_num2_num(lambda a, b: a/b)


def make_prim_num2_bool(py_func: Callable[[float, float], bool]):
    def _prim_num2_bool(x: SchemeVal, y: SchemeVal) -> SchemeVal:
        if not isinstance(x, NumberVal) or not isinstance(y, NumberVal):
            raise SchemePrimError('%s requires both operators to be numbers, now %s and %s' % (
                py_func.__name__, type(x), type(y)))
        x = cast(NumberVal, x)
        y = cast(NumberVal, y)
        res = py_func(x.value, y.value)
        return BooleanVal(res)
    return _prim_num2_bool


prim_op_eq = make_prim_num2_bool(lambda a, b: a == b)
prim_op_lt = make_prim_num2_bool(lambda a, b: a < b)
prim_op_gt = make_prim_num2_bool(lambda a, b: a > b)


def prim_equal(x: SchemeVal, y: SchemeVal):
    return BooleanVal(is_equal(x, y))


def make_prim_pair_any(py_func: Callable[[PairVal], SchemeVal]):
    def _prim_pair_any(x: SchemeVal) -> SchemeVal:
        if isinstance(x, PairVal):
            return py_func(x)
        else:
            raise SchemePrimError('not a pair')
    return _prim_pair_any


prim_length = make_prim_pair_any(lambda x: NumberVal(pair_length(x)))
prim_car = make_prim_pair_any(lambda x: x.left)
prim_cdr = make_prim_pair_any(lambda x: x.right)


def prim_cons(x: SchemeVal, y: SchemeVal):
    return PairVal(x, y)


def prim_list(*args: SchemeVal):
    return pair_from_list(list(args), NilVal())


def prim_pair(x: SchemeVal) -> BooleanVal:
    return BooleanVal(isinstance(x, PairVal))


def prim_null(x: SchemeVal) -> BooleanVal:
    return BooleanVal(isinstance(x, NilVal))


def prim_display(sv: SchemeVal):
    scheme_print(stringify_value(sv))
    return UndefVal()


def prim_newline():
    scheme_print('\n')
    return UndefVal()


def install_primitives():
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
    update_primitives(prims)


'''initialize test'''


def install_rules():
    install_parse_expr_rules()
    install_stringify_expr_rules()
    install_stringify_value_rules()
    install_is_equal_rules()
    install_eval_rules()
    install_primitives()


def test_one(source: str, **kargs: str):
    '''
    each test tries to execute the source code as much as possible
    capture the output, panic and result
    print them and compare to expected value
    '''

    # source
    source = source.strip()
    print('* source: %s' % source)
    try:
        # scan
        tokens = scan_source(source)
        token_str = ', '.join([stringify_token_full(t) for t in tokens])
        print('* tokens: %s' % token_str)
        if 'tokens' in kargs:
            assert token_str == kargs['tokens']

        # parse
        combos = parse_tokens(tokens)
        expr = parse_expr(combos)
        expr_str = stringify_expr(expr)
        print('* expression: %s' % expr_str)
        if 'expression' in kargs:
            assert expr_str == kargs['expression']

        # evaluate
        glbenv = make_global_env()
        result = evaluate_expr(expr, glbenv)
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


def test_scan():
    test_one(
        '(if #true 1 2)',
        panic='scanner error in line 1: invalid boolean: #true'
    )
    test_one(
        '(if #t 1 2)',
        tokens='LEFT_PAREN, SYMBOL:if, BOOLEAN:#t, NUMBER:1, NUMBER:2, RIGHT_PAREN'
    )
    test_one(
        '(display\n"abc)',
        panic='scanner error in line 2: unterminated string: "abc)'
    )
    test_one(
        '\' (1 2)',
        panic='scanner error in line 1: quote should not be followed by space'
    )
    test_one(
        '\'(1 . 2)',
        tokens='QUOTE, LEFT_PAREN, NUMBER:1, DOT, NUMBER:2, RIGHT_PAREN'
    )
    test_one(
        '\'(1 .2)',
        panic='scanner error in line 1: dot should be followed by space'
    )


def test_parse():
    test_one(
        '',
        tokens='',
        expression='(sequence)',
        result='#<undef>'
    )
    test_one(
        '(display\n"abc"',
        tokens='LEFT_PAREN, SYMBOL:display, STRING:abc',
        panic='parser error at LEFT_PAREN in line 1: list missing right parenthesis'
    )
    test_one(
        '(display\n"abc")',
        tokens='LEFT_PAREN, SYMBOL:display, STRING:abc, RIGHT_PAREN',
        expression='(sequence (call display "abc"))',
        output='abc',
        result='#<undef>'
    )
    test_one(
        '\'(a (b c))',
        tokens='QUOTE, LEFT_PAREN, SYMBOL:a, LEFT_PAREN, SYMBOL:b, SYMBOL:c, RIGHT_PAREN, RIGHT_PAREN',
        expression='(sequence (quote (a (b c))))',
        result='(a (b c))'
    )
    test_one(
        '(define a 1)\n(set! a 2)',
        expression='(sequence (define-var a 1) (set a 2))',
        result='2'
    )
    # list parsing
    test_one(
        '(begin)',
        panic='parser error at LEFT_PAREN in line 1: begin should have at least 2 expressions, now 1'
    )
    # list parsing
    test_one(
        '(if 0 1 2 3)',
        panic='parser error at LEFT_PAREN in line 1: if should have 3 or 4 expressions, now 5'
    )
    # list parsing
    test_one(
        '(define ("a" "b") 3)',
        panic='parser error at STRING:a in line 1: define procedure name should be symbol, now STRING'
    )
    # define proc
    test_one(
        '(define (f x) (+ x 1))',
        expression='(sequence (define-proc f (x) (sequence (call + x 1))))',
        result='f'
    )
    # define proc same parameter
    test_one(
        '(define (f x x) (+ x 1))',
        panic='parser error at SYMBOL:x in line 1: parameter show up twice'
    )
    # desugaring let
    test_one(
        '(let ((x 1) (y 2)) (+ x y))',
        expression='(sequence (call (lambda (x y) (sequence (call + x y))) 1 2))',
        result='3'
    )
    # desugaring let invalid syntax
    test_one(
        '(let ((x 1) (y 2 3)) (+ x y))',
        panic='parser error at LEFT_PAREN in line 1: let 2nd expression should be list of list of 2 expressions'
    )
    # dot
    test_one(
        '\'(a . b . c)',
        panic='parser error at DOT in line 1: one list can have at most one dot, now 2'
    )
    # dot
    test_one(
        '\'(a . )',
        panic='parser error at DOT in line 1: dot should be at -2 position of list'
    )
    # dot
    test_one(
        '\'(. a)',
        panic='parser error at DOT in line 1: cannot have free or header dot within quote'
    )
    # dot
    test_one(
        '(. a)',
        panic='parser error at DOT in line 1: list cannot start with DOT'
    )
    # dot
    test_one(
        '(a . b)',
        panic='parser error at DOT in line 1: unexpected token type'
    )
    # dot in parameter
    test_one(
        '(define (f a . b) b)',
        expression='(sequence (define-proc f (a . b) (sequence b)))',
        result='f'
    )


def test_env():
    test_one(
        '((lambda (a) (+ x 1)) 2)',
        panic='runtime error at SYMBOL:x in line 1: symbol undefined'
    )


def test_eval():
    # arithmetic
    test_one(
        '(+ (* 3 5) (- 10 6))',
        result='19'
    )
    # composition
    test_one(
        '''
        (define (square x) (* x x))
        (define (sum-of-squares x y) (+ (square x) (square y)))
        (sum-of-squares 3 4)
        ''',
        result='25'
    )
    # lambda and or
    test_one(
        '((lambda (x y) (or (> x y) (= x y))) 1 2)',
        result='#f'
    )
    # recursion
    test_one(
        '''
        (define (factorial n)
          (if (= n 1)
            1
            (* n (factorial (- n 1)))))
        (factorial 5)
        ''',
        result='120'
    )
    # if
    test_one(
        '''
        (define x (if #t 1 2))
        (if (= x 1) (display "a"))
        (if (= x 2) (display "b"))
        ''',
        output='a',
        result='#<undef>'
    )
    # iteration
    test_one(
        '''
        (define (factorial n)
          (define (fact-iter product counter)
            (if (> counter n)
               product
               (fact-iter (* counter product)
                 (+ counter 1))))
          (fact-iter 1 1))
        (factorial 5)
        ''',
        result='120'
    )
    # begin
    test_one(
        '(begin (+ 1 2) (* 3 4))',
        result='12'
    )
    # mutation
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
    # list
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
    # closure
    test_one(
        '''
        (define (f)
          (define x 1)
          (lambda () x))
        ((f))
        ''',
        result='1'
    )
    # list primitive
    test_one(
        '''
        (list (+ 1 2) (+ 3 4) (list 5 6))
        ''',
        result='(3 7 (5 6))'
    )
    # return lambda to test find_type in ValueStringifier
    test_one(
        '''
        (lambda () 1)
        ''',
        result='[procedure lambda]'
    )
    # scope conflict
    # should error when we have resolver
    test_one(
        '''
        (define x 1)
        (define (f)
          (define y x)
          (define x 2)
          y)
        (f)
        ''',
        result='1'
    )
    # another scope conflict
    # should error when we have resolver
    test_one(
        '''
        (define x 1)
        (define (f)
          (define x x)
          x)
        (f)
        ''',
        result='1'
    )
    # dot procedure
    test_one(
        '''
        (define (f . a) a)
        (f 1 2 3)
        ''',
        result='(1 2 3)'
    )
    # dot procedure
    test_one(
        '''
        (define (f a b . c) c)
        (f 1)
        ''',
        panic='runtime error at LEFT_PAREN in line 2: f expect at least 2 arguments, only get 1'
    )
    # dot in quote
    test_one(
        '''
        (define x '(a b . c))
        (cdr x)
        ''',
        result='(b . c)'
    )


def test():
    test_scan()
    test_parse()
    test_env()
    test_eval()


if __name__ == '__main__':
    install_rules()
    test()

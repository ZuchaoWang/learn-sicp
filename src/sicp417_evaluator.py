# the goal is to implement a simplified scheme language
# it's only a toy, which will not follow the language specification
# and only support a small proportion of the feautres
# no guarantee for performance, or even correctness (we have so few tests)
#
# the input of the language is a string, which will be transformed to tokens via Scanner
# then Parser transforms tokens to scheme lists
# followed by Analyzer making syntactic analysis on scheme lists to generate functions
# finally evaluator executes the functions

import sys
import enum
from typing import List, Optional


def panic(msg: str):
    print(msg, file=sys.stderr)
    exit(1)


def stringify_number(x: float):
    if (x == int(x)):
        return '%d' % x
    else:
        return '%.3f' % x

# scheme scanner: string -> tokens
# only support paranthesis, quote float, string, symbol
# string does not support backslash escaped string character
# we do not generate EOF token, because it seems unnecessary
# ref: https://craftinginterpreters.com/scanning.html


@enum.unique
class TokenType(enum.Enum):
    LEFT_PAREN = enum.auto()
    RIGHT_PAREN = enum.auto()
    QUOTE = enum.auto()
    SYMBOL = enum.auto()
    NUMBER = enum.auto()
    STRING = enum.auto()


class Token:
    def __init__(self, token_type: TokenType, lexeme: str, literal):
        self.token_type = token_type
        self.lexeme = lexeme
        self.literal = literal

    def stringify(self):
        if isinstance(self.literal, float):
            return '%s:%s' % (self.token_type.name, stringify_number(self.literal))
        elif isinstance(self.literal, str):
            return '%s:%s' % (self.token_type.name, self.literal)
        else:
            return self.token_type.name


class Scanner:
    def __init__(self, source: str):
        self.source = source
        self.start = 0
        self.current = 0
        self.tokens: List[Token] = []

    def scan(self):
        while(not self.is_at_end()):
            self.scan_one_token()
            self.start = self.current
        return self.tokens

    def scan_one_token(self):
        c = self.advance()
        if c == '(':
            self.add_token(TokenType.LEFT_PAREN)
        elif c == ')':
            self.add_token(TokenType.RIGHT_PAREN)
        elif c == '\'':
            self.scan_quote()
        elif c == '"':
            self.scan_string()
        elif not c.isspace():
            self.scan_nonstring()

    def is_at_end(self):
        return self.current >= len(self.source)

    def advance(self):
        c = self.source[self.current]
        self.current += 1
        return c

    def peek(self):
        return self.source[self.current]

    def add_token(self, token_type: TokenType, literal=None):
        lexeme = self.source[self.start:self.current]
        self.tokens.append(Token(token_type, lexeme, literal))

    def scan_quote(self):
        if self.is_at_end():
            panic('scanner: quote should not be at the end')
        elif self.peek().isspace():
            panic('scanner: quote should not be followed by space')
        else:
            self.add_token(TokenType.QUOTE)

    def scan_string(self):
        while not self.is_at_end() and self.peek() != '"':
            self.advance()

        if self.is_at_end():
            panic('scanner: unterminated string: %s' %
                  self.source[self.start:self.current])

        # consume ending "
        self.advance()

        # trim the surrounding quotes
        lexemem = self.source[self.start+1:self.current-1]
        self.add_token(TokenType.STRING, lexemem)

    def scan_nonstring(self):
        while not self.is_at_end() and not Scanner.can_terminate_nonstring(self.peek()):
            c = self.advance()
            if c == '\'' or c == '"':
                panic('scanner: invalid quote: %s' %
                      self.source[self.start:self.current])

        try:
            lexemem = float(self.source[self.start:self.current])
            self.add_token(TokenType.NUMBER, lexemem)
        except:
            lexemem = self.source[self.start:self.current]
            if lexemem[0].isnumeric():
                panic('scanner: symbol should not start with number: %s' % lexemem)
            self.add_token(TokenType.SYMBOL, lexemem)

    @staticmethod
    def can_terminate_nonstring(c: str):
        return c.isspace() or c == '(' or c == ')'


# scheme parser: tokens -> scheme lists
# empty list is represented as expression of type list but value none
# ref: https://craftinginterpreters.com/parsing-expressions.html

@enum.unique
class ExprType(enum.Enum):
    LIST = enum.auto()
    SYMBOL = enum.auto()
    NUMBER = enum.auto()
    STRING = enum.auto()


class Expression:
    def __init__(self, expr_type: ExprType, value):
        self.expr_type = expr_type
        self.value = value

    def stringify(self) -> str:
        if self.expr_type == ExprType.SYMBOL:
            return self.value
        elif self.expr_type == ExprType.NUMBER:
            return stringify_number(self.value)
        elif self.expr_type == ExprType.STRING:
            return '"%s"' % self.value
        else:
            substrs: List[str] = []
            head: Optional[LinkedList] = self.value
            while head is not None:
                substrs.append(head.value.stringify())
                head = head.next
            return "(%s)" % (" ".join(substrs))


class LinkedList:
    def __init__(self, value: Expression, next=None):
        self.value = value
        self.next = next

    @staticmethod
    def from_list(values: List[Expression]):
        head = None
        for i in range(len(values)-1, -1, -1):
            head = LinkedList(values[i], head)
        return head


class Parser:
    '''
    expression -> SYMBOL | STRING | NUMBER | quote | list;
    quote -> QUOTE expression;
    list -> LEFT_PAREN ( expression )* RIGHT_PAREN;
    '''

    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.current = 0
        self.lookup_table = {
            TokenType.SYMBOL: self.parse_symbol,
            TokenType.NUMBER: self.parse_number,
            TokenType.STRING: self.parse_string,
            TokenType.QUOTE: self.parse_quote,
            TokenType.LEFT_PAREN: self.parse_left_paren,
            TokenType.RIGHT_PAREN: self.parse_right_paren
        }

    def parse(self):
        if len(self.tokens) == 0:
            return None
        expr = self.parse_recursive()
        if not self.is_at_end():
            panic('parser: excessive tokens: %s' % self.tokens[self.current].stringify())
        return expr

    def parse_recursive(self) -> Expression:
        if self.is_at_end():
            panic('parser: recursive parse failed')
        token = self.advance()
        return self.lookup_table[token.token_type](token)

    def parse_symbol(self, token: Token):
        return Expression(ExprType.SYMBOL, token.literal)

    def parse_number(self, token: Token):
        return Expression(ExprType.NUMBER, token.literal)

    def parse_string(self, token: Token):
        return Expression(ExprType.STRING, token.literal)

    def parse_quote(self, _token: Token):
        values = []
        values.append(Expression(ExprType.SYMBOL, 'quote'))
        values.append(self.parse_recursive())
        return Expression(ExprType.LIST, LinkedList.from_list(values))

    def parse_left_paren(self, _token: Token):
        values = []
        while not self.is_at_end() and self.peek().token_type != TokenType.RIGHT_PAREN:
            values.append(self.parse_recursive())
        if self.is_at_end() or self.peek().token_type != TokenType.RIGHT_PAREN:
            panic('parser: list missing right parenthesis')
        self.advance()  # consume right parenthesis
        return Expression(ExprType.LIST, LinkedList.from_list(values))

    def parse_right_paren(self, _token: Token):
        panic('parser: unmatched right parenthesis')

    def is_at_end(self):
        return self.current >= len(self.tokens)

    def advance(self):
        tk = self.tokens[self.current]
        self.current += 1
        return tk

    def peek(self):
        return self.tokens[self.current]


def test_one(source: str, token_str_expect: Optional[str], expr_str_expect: Optional[str]):
    # source
    print('source: %s' % source)
    # scan
    scanner = Scanner(source)
    tokens = scanner.scan()
    token_str = ', '.join([t.stringify() for t in tokens])
    print('tokens: %s' % token_str)
    if token_str_expect is not None:
        assert token_str == token_str_expect
    # parse
    parser = Parser(tokens)
    expr = parser.parse()
    expr_str = expr.stringify() if expr else ''
    print('expression: %s' % expr_str)
    if expr_str_expect is not None:
        assert expr_str == expr_str_expect
    print('----------')


def test():
    test_one(
        '',
        '',
        ''
    )
    test_one(
        '(+ 1 2.5)',
        'LEFT_PAREN, SYMBOL:+, NUMBER:1, NUMBER:2.500, RIGHT_PAREN',
        '(+ 1 2.500)'
    )
    test_one(
        '\'(a (b c))',
        'QUOTE, LEFT_PAREN, SYMBOL:a, LEFT_PAREN, SYMBOL:b, SYMBOL:c, RIGHT_PAREN, RIGHT_PAREN',
        '(quote (a (b c)))'
    )
    test_one(
        '(display  "abc")',
        'LEFT_PAREN, SYMBOL:display, STRING:abc, RIGHT_PAREN',
        '(display "abc")'
    )


if __name__ == '__main__':
    test()

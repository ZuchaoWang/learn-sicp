import sys
import enum
from typing import List

# scheme scanner
# only support paranthesis, float, string, symbol
# string does not support backslash escape
# ref: https://craftinginterpreters.com/scanning.html


def panic(msg: str):
    print(msg, file=sys.stderr)
    exit(1)


@enum.unique
class TokenType(enum.Enum):
    LEFT_PAREN = enum.auto()
    RIGHT_PAREN = enum.auto()
    QUOTE = enum.auto()
    EOF = enum.auto()
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
            return '%s:%.3f' % (self.token_type.name, self.literal)
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

    def scan_tokens(self):
        while(not self.is_at_end()):
            self.scan_one_token()
            self.start = self.current
        self.add_token(TokenType.EOF)
        return self.tokens

    def scan_one_token(self):
        c = self.advance()
        if c == '(':
            self.add_token(TokenType.LEFT_PAREN)
        elif c == ')':
            self.add_token(TokenType.RIGHT_PAREN)
        elif c == '\'':
            self.add_token(TokenType.QUOTE)
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


def run(source: str):
    scanner = Scanner(source)
    tokens = scanner.scan_tokens()
    token_str = ', '.join([t.stringify() for t in tokens])
    return token_str


def test_one(source: str, token_str_expect: str):
    token_str = run(source)
    print(token_str)
    assert token_str == token_str_expect


def test():
    test_one(
        '',
        'EOF'
    )
    test_one(
        '(+ 1 2)',
        'LEFT_PAREN, SYMBOL:+, NUMBER:1.000, NUMBER:2.000, RIGHT_PAREN, EOF'
    )
    test_one(
        '\'(a (b c))',
        'QUOTE, LEFT_PAREN, SYMBOL:a, LEFT_PAREN, SYMBOL:b, SYMBOL:c, RIGHT_PAREN, RIGHT_PAREN, EOF'
    )
    test_one(
        '(display  "abc")',
        'LEFT_PAREN, SYMBOL:display, STRING:abc, RIGHT_PAREN, EOF'
    )


if __name__ == '__main__':
    test()

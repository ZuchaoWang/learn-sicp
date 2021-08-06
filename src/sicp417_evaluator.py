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
from typing import Callable, Dict, List, Optional


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


LEFT_PAREN = 'LEFT_PAREN'
RIGHT_PAREN = 'RIGHT_PAREN'
QUOTE = 'QUOTE'
SYMBOL = 'SYMBOL'
NUMBER = 'NUMBER'
STRING = 'STRING'


class Token:
    def __init__(self, typ: str, lexeme: str, literal):
        self.typ = typ
        self.lexeme = lexeme
        self.literal = literal


class TokenPrintier:
    def stringify(self, token: Token):
        if isinstance(token.literal, float):
            return '%s:%s' % (token.typ, stringify_number(token.literal))
        elif isinstance(token.literal, str):
            return '%s:%s' % (token.typ, token.literal)
        else:
            return token.typ


class Scanner:
    def __init__(self):
        self._restart('')

    def scan(self, source: str):
        self._restart(source)
        while(not self._is_at_end()):
            self._scan_one_token()
            self._start = self._current
        return self._tokens

    def _restart(self, source: str):
        self._source = source
        self._start = 0
        self._current = 0
        self._tokens: List[Token] = []

    def _scan_one_token(self):
        c = self._advance()
        if c == '(':
            self._add_token(LEFT_PAREN)
        elif c == ')':
            self._add_token(RIGHT_PAREN)
        elif c == '\'':
            self._scan_quote()
        elif c == '"':
            self._scan_string()
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

    def _add_token(self, typ: str, literal=None):
        lexeme = self._source[self._start:self._current]
        self._tokens.append(Token(typ, lexeme, literal))

    def _scan_quote(self):
        if self._is_at_end():
            panic('scanner: quote should not be at the end')
        elif self._peek().isspace():
            panic('scanner: quote should not be followed by space')
        else:
            self._add_token(QUOTE)

    def _scan_string(self):
        while not self._is_at_end() and self._peek() != '"':
            self._advance()

        if self._is_at_end():
            panic('scanner: unterminated string: %s' %
                  self._source[self._start:self._current])

        # consume ending "
        self._advance()

        # trim the surrounding quotes
        lexemem = self._source[self._start+1:self._current-1]
        self._add_token(STRING, lexemem)

    def _scan_nonstring(self):
        while not self._is_at_end() and not Scanner._can_terminate_nonstring(self._peek()):
            c = self._advance()
            if c == '\'' or c == '"':
                panic('scanner: invalid quote: %s' %
                      self._source[self._start:self._current])

        try:
            lexemem = float(self._source[self._start:self._current])
            self._add_token(NUMBER, lexemem)
        except:
            lexemem = self._source[self._start:self._current]
            if lexemem[0].isnumeric():
                panic('scanner: symbol should not start with number: %s' % lexemem)
            self._add_token(SYMBOL, lexemem)

    @staticmethod
    def _can_terminate_nonstring(c: str):
        return c.isspace() or c == '(' or c == ')'


# scheme parser: tokens -> scheme lists
# empty list is represented as expression of type list but value none
# ref: https://craftinginterpreters.com/parsing-expressions.html

LIST = 'LIST'

class Expression:
    def __init__(self, typ: str, value):
        self.typ = typ
        self.value = value


class ExprPrinter:
    def stringify(self, expr: Expression) -> str:
        if expr.typ == SYMBOL:
            return expr.value
        elif expr.typ == NUMBER:
            return stringify_number(expr.value)
        elif expr.typ == STRING:
            return '"%s"' % expr.value
        elif expr.typ == LIST:
            substrs: List[str] = []
            head: Optional[LinkedList] = expr.value
            while head is not None:
                substrs.append(self.stringify(head.expr))
                head = head.next
            return "(%s)" % (" ".join(substrs))
        else:
            panic('expr printer: unknown type = %s' % expr.typ)


class LinkedList:
    def __init__(self, expr: Expression, next: Optional["LinkedList"] = None):
        self.expr = expr
        self.next = next

    @staticmethod
    def from_list(expr_list: List[Expression]):
        head = None
        for i in range(len(expr_list)-1, -1, -1):
            head = LinkedList(expr_list[i], head)
        return head

    def length(self):
        count = 0
        head = self
        while head:
            count += 1
            head = head.next
        return count


class Parser:
    '''
    expression -> SYMBOL | STRING | NUMBER | quote | list;
    quote -> QUOTE expression;
    list -> LEFT_PAREN ( expression )* RIGHT_PAREN;
    '''

    def __init__(self):
        self.lookup_table = {
            SYMBOL: self._parse_simple,
            NUMBER: self._parse_simple,
            STRING: self._parse_simple,
            QUOTE: self._parse_quote,
            LEFT_PAREN: self._parse_left_paren,
            RIGHT_PAREN: self._parse_right_paren
        }
        self._restart([])
        self._token_printer = TokenPrintier()

    def parse(self, tokens: List[Token]):
        self._restart(tokens)
        if len(self.tokens) == 0:
            return None
        expr = self._parse_recursive()
        if not self._is_at_end():
            panic('parser: excessive tokens: %s' %
                  self._token_printer.stringify(self.tokens[self.current]))
        return expr

    def _restart(self, tokens: List[Token]):
        self.tokens = tokens
        self.current = 0

    def _parse_recursive(self) -> Expression:
        if self._is_at_end():
            panic('parser: recursive parse failed')
        token = self._advance()
        return self.lookup_table[token.typ](token)

    def _parse_simple(self, token: Token):
        return Expression(token.typ, token.literal)

    def _parse_quote(self, _token: Token):
        expr_list = []
        expr_list.append(Expression(SYMBOL, 'quote'))
        expr_list.append(self._parse_recursive())
        return Expression(LIST, LinkedList.from_list(expr_list))

    def _parse_left_paren(self, _token: Token):
        expr_list = []
        while not self._is_at_end() and self._peek().typ != RIGHT_PAREN:
            expr_list.append(self._parse_recursive())
        if self._is_at_end() or self._peek().typ != RIGHT_PAREN:
            panic('parser: list missing right parenthesis')
        self._advance()  # consume right parenthesis
        return Expression(LIST, LinkedList.from_list(expr_list))

    def _parse_right_paren(self, _token: Token):
        panic('parser: unmatched right parenthesis')

    def _is_at_end(self):
        return self.current >= len(self.tokens)

    def _advance(self):
        tk = self.tokens[self.current]
        self.current += 1
        return tk

    def _peek(self):
        return self.tokens[self.current]


# scheme analyzer
# we assume operator cannot be a procedure that evaluates to symbol
# see 4.1.7


class Analyzer:
    def __init__(self, special_forms: Dict[str, Callable], procedure: Callable, symbol: Callable):
        self._special_forms = special_forms
        self._procedure = procedure
        self._symbol = symbol

    def analyze(self, expr: Optional[Expression]):
        if expr is not None:
            if expr.typ == NUMBER or expr.typ == STRING:
                return lambda env: expr
            elif expr.typ == SYMBOL:
                return self.analyze_symbol(expr)
            else:  # must be list
                return self.analyze_list(expr)

    def analyze_symbol(self, expr: Expression):
        return self._symbol(expr, self.analyze)

    def analyze_list(self, expr: Expression):
        head: Optional[LinkedList] = expr.value
        if head is None:  # empty list
            panic('analyzer: cannot evaluate empty list')
        else:
            hexpr = head.expr
            if hexpr.typ == NUMBER:
                panic('analyzer: number cannot be operator or special form')
            if hexpr.typ == STRING:
                panic('analyzer: string cannot be operator or special form')
            if hexpr.typ == SYMBOL:
                f = self._special_forms.get(hexpr.value, None)
                if f is not None:
                    return f(expr, self.analyze)
            return self._procedure(expr, self.analyze)


class Procedure:
    def __init__(self, parameters: List[str], body: Callable):
        self.parameters = parameters
        self.body = body


def analyze_symbol(expr: Expression, _analyze: Callable):
    '''lookup variable'''
    name = expr.value
    return lambda env: env.lookup(name)


def analyze_quote(expr: Expression, _analyze: Callable):
    head: LinkedList = expr.value
    if head.length() == 2:
        quoted = head.next.expr
        return lambda env: quoted
    else:
        panic('analyze_quote: list length should be 2')


def analyze_set(expr: Expression, analyze: Callable):
    head: LinkedList = expr.value
    name: str = head.expr.value
    if head.length() == 2:
        get_value = analyze(head.next)
        return lambda env: env.set(name, get_value())
    else:
        panic('analyze_set: list length should be 2')
    

def analyze_define(expr: Expression, analyze: Callable):
    head: LinkedList = expr.value
    name: str = head.expr.value
    hl = head.length()
    if hl == 2:
        # define variable
        get_expr = analyze(head.next)
        return lambda env: env.define(name, get_expr())
    elif hl == 3:
        # define procedure
        if head.next.expr.typ != LIST:
            panic('analyze_define: procedure parameters must be a list')
        parameters: List[str] = []
        para_exprs: LinkedList = head.next.expr.value
        while para_exprs is not None:
            if para_exprs.expr.typ != SYMBOL:
                panic('analyze_define: procedure parameters must all be symbols')
            parameters.append(para_exprs.expr.value)
            para_exprs = para_exprs.next
        body = analyze(head.next.next.expr)
        proc = Procedure(parameters, body)
        return lambda env: env.define(name, proc)
    else:
        panic('analyze_define: list length should be 2')
    

def test_one(source: str, token_str_expect: Optional[str], expr_str_expect: Optional[str]):
    # source
    print('source: %s' % source)
    # scan
    scanner = Scanner()
    tokens = scanner.scan(source)
    token_stringifier = TokenPrintier()
    token_str = ', '.join([token_stringifier.stringify(t) for t in tokens])
    print('tokens: %s' % token_str)
    if token_str_expect is not None:
        assert token_str == token_str_expect
    # parse
    parser = Parser()
    expr = parser.parse(tokens)
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

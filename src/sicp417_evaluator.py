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
import inspect
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


# TODO: need a pair data structure, scheme list is build from pairs

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

# TODO: finish environment

class Environment:
    def __init__(self, bindings: Dict[str, Expression] = {}, enclosing: Optional["Environment"] = None):
        self._bindings = bindings
        self._enclosing = enclosing

    def define(self, name: str, expr: Expression):
        pass

    def set(self, name: str, expr: Expression):
        pass

    def lookup(self, name: str):
        pass

    def _find_env(self, name: str):
        env = self
        while env is not None:
            if name in env._bindings:
                return env
            else:
                env = env._enclosing
        return None

    def define_primitive(self, name: str, py_func: Callable):
        arity = len(inspect.getfullargspec(py_func).args)
        primitive = Primitive(PRIMITIVE, arity, py_func)
        self._bindings[name] = primitive
        return primitive

    def extend(self, parameter: List[str], arguments: List[Expression]):
        return Environment(dict(zip(parameter, arguments)), self)


AnalyzeRetType = Callable[[Environment], Expression]
AnalyzeType = Callable[[Optional[Expression]], AnalyzeRetType]
AnalyzeConfigType = Callable[[Environment, AnalyzeType], AnalyzeRetType]


class Analyzer:
    def __init__(self, special_forms: Dict[str, AnalyzeConfigType], application: AnalyzeConfigType, symbol: AnalyzeConfigType):
        self._special_forms = special_forms
        self._application = application
        self._symbol = symbol

    def analyze(self, expr: Optional[Expression]) -> AnalyzeRetType:
        if expr is not None:
            if expr.typ == NUMBER or expr.typ == STRING:
                return lambda _: expr
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
            return self._application(expr, self.analyze)


PROCEDURE = 'PROCEDURE'
PRIMITIVE = 'PRIMITIVE'


class Procedure:
    def __init__(self, parameters: List[str], body: Callable[[Environment], Expression]):
        self.parameters = parameters
        self.body = body


class Primitive:
    def __init__(self, arity: int, body: Callable[..., Expression]):
        self.arity = arity
        self.body = body


def analyze_symbol(expr: Expression, _analyze: AnalyzeType) -> AnalyzeRetType:
    '''lookup variable'''
    name = expr.value
    return lambda env: env.lookup(name)


def analyze_quote(expr: Expression, _analyze: AnalyzeType) -> AnalyzeRetType:
    head: LinkedList = expr.value
    if head.length() == 2:
        quoted = head.next.expr
        return lambda _: quoted
    else:
        panic('analyze_quote: list length should be 2')


def analyze_set(expr: Expression, analyze: AnalyzeType) -> AnalyzeRetType:
    head: LinkedList = expr.value
    name: str = head.expr.value
    if head.length() == 2:
        get_expr = analyze(head.next)
        return lambda env: env.set(name, get_expr())
    else:
        panic('analyze_set: list length should be 2')
    

def analyze_define(expr: Expression, analyze: AnalyzeType) -> AnalyzeRetType:
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
        proc = Expression(PROCEDURE, Procedure(parameters, body))
        return lambda env: env.define(name, proc)
    else:
        panic('analyze_define: list length should be 2')


def analyze_application(expr: Expression, analyze: AnalyzeType) -> AnalyzeRetType:
    head: LinkedList = expr.value        
    get_operator = analyze(head.expr)
    get_operands: List[AnalyzeRetType] = []
    op_expr = head.next
    while op_expr is not None:
        get_operands.append(analyze(op_expr))
        op_expr = op_expr.next
    def _analyze_application(env: Environment):
        operator = get_operator(env)
        operands = [get_op(env) for get_op in get_operands]
        if operator.typ == PRIMITIVE:
            primitive: Primitive = operator.value
            if len(operands) != primitive.arity:
                panic('analyze_application: primitive incorrect arity %d, should be %d' % (len(operands), primitive.arity))
            return primitive.body(*operands)
        elif operator.typ == PROCEDURE:
            procedure: Procedure = operator.value
            if len(operands) != len(procedure.parameters):
                panic('analyze_application: procedure incorrect arity %d, should be %d' % (len(operands), len(procedure.parameters)))
            new_env = env.extend(procedure.parameters, operands)
            return procedure.body(new_env)
        else:
            panic('analyze_application: expression of type %s cannot be used as operator' % operator.typ)
    return _analyze_application


def prim_op_number2(py_func: Callable[[float, float], float], x: Expression, y: Expression) -> Expression:
    if x.typ != NUMBER or y.typ != NUMBER:
        panic('%s: both operator should be number, now %s and %s' % (py_func.__name__, x.typ, y.typ))
    xval: float = x.value
    yval: float = y.value
    res = py_func(xval, yval)
    return Expression(NUMBER, res)


def prim_op_add(x: Expression, y: Expression) -> Expression:
    def _prim_op_add(a: float, b: float): return a+b
    return prim_op_number2(_prim_op_add, x, y)


# TODO: register display, equality, truthy


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

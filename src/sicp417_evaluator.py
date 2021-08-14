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
import enum
from typing import Callable, ClassVar, Dict, List, Optional, Set, Tuple, Type, Union


def panic(msg: str):
    print(msg, file=sys.stderr)
    exit(1)


def stringify_float(x: float):
    if (x == int(x)):
        return '%d' % x
    else:
        return '%.3f' % x

# scheme scanner: string -> tokens
# only support paranthesis, quote float, string, symbol
# string does not support backslash escaped string character
# we do not generate EOF token, because it seems unnecessary
# we do not support boolean, just use 0/1, or others via isTruthy
# ref: https://craftinginterpreters.com/scanning.html


@enum.unique
class TokenTag(enum.Enum):
    LEFT_PAREN = enum.auto()
    RIGHT_PAREN = enum.auto()
    QUOTE = enum.auto()
    SYMBOL = enum.auto()
    STRING = enum.auto()
    NUMBER = enum.auto()


class Token:
    def __init__(self, tag: TokenTag, lexeme: str, literal):
        self.tag = tag
        self.lexeme = lexeme
        self.literal = literal


class TokenPrinter:
    def __init__(self):
        self._rules: Dict[TokenTag, Callable[[Token], str]] = {
            TokenTag.LEFT_PAREN: self._stringify_other,
            TokenTag.RIGHT_PAREN: self._stringify_other,
            TokenTag.QUOTE: self._stringify_other,
            TokenTag.SYMBOL: self._stringify_string,
            TokenTag.STRING: self._stringify_string,
            TokenTag.NUMBER: self._stringify_number,
        }

    def stringify(self, tk: Token):
        f = self._rules[tk.tag]
        return f(tk)

    def _stringify_number(self, tk: Token):
        return '%s:%s' % (tk.tag, stringify_float(tk.literal))

    def _stringify_string(self, tk: Token):
        return '%s:%s' % (tk.tag, tk.literal)

    def _stringify_other(self, tk: Token):
        return tk.tag


class Scanner:
    # class vars
    _invalid_nonstring_chars: ClassVar[Set[str]] = set(
        ''.split('[]{}\"\',`;#|\\'))

    # instance vars
    _source: str
    _start: int
    _current: int
    _tokens: List[Token]

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
            self._add_token(TokenTag.LEFT_PAREN)
        elif c == ')':
            self._add_token(TokenTag.RIGHT_PAREN)
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

    def _add_token(self, tag: TokenTag, literal=None):
        lexeme = self._source[self._start:self._current]
        self._tokens.append(Token(tag, lexeme, literal))

    def _scan_quote(self):
        if self._is_at_end():
            panic('scanner: quote should not be at the end')
        elif self._peek().isspace():
            panic('scanner: quote should not be followed by space')
        else:
            self._add_token(TokenTag.QUOTE)

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
        self._add_token(TokenTag.STRING, lexemem)

    def _scan_nonstring(self):
        while not self._is_at_end() and not Scanner._can_terminate_nonstring(self._peek()):
            c = self._advance()
            if c in Scanner._invalid_nonstring_chars:
                panic('scanner: invalid nonstring: %s' %
                      self._source[self._start:self._current])

        try:
            lexemem = float(self._source[self._start:self._current])
            self._add_token(TokenTag.NUMBER, lexemem)
        except:
            lexemem = self._source[self._start:self._current]
            if lexemem[0].isnumeric():
                panic('scanner: symbol should not start with number: %s' % lexemem)
            self._add_token(TokenTag.SYMBOL, lexemem)

    @staticmethod
    def _can_terminate_nonstring(c: str):
        return c.isspace() or c == '(' or c == ')'

# expression and environment

class Expression:
    pass

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
                env = env._enclosing  # type: ignore
        return None

    def define_primitive(self, name: str, py_func: Callable):
        arity = len(inspect.getfullargspec(py_func).args)
        primitive = PrimExpr(name, arity, py_func)
        self._bindings[name] = primitive
        return primitive

    def extend(self, parameter: List[str], arguments: List[Expression]):
        return Environment(dict(zip(parameter, arguments)), self)

# define different types of expressions as difference classes for better type checking
# if we use tag to differentiate different types, typing does not allow specify tag as type
#
# we do not differentiate between object and experssion
# because they are so similar in Scheme 
#
# empty list is represented as special nil expression
# non-empty list is represented as pairs

class SymbolExpr(Expression):
    def __init__(self, literal: str):
        self.literal = literal


class StringExpr(Expression):
    def __init__(self, literal: str):
        self.literal = literal


class NumberExpr(Expression):
    def __init__(self, literal: float):
        self.literal = literal


class NilExpr(Expression):
    pass


class PairExpr(Expression):
    def __init__(self, left: Expression, right: Expression):
        self.left = left
        self.right = right


class ProcExpr(Expression):
    def __init__(self, name: str, parameters: List[str], body: Callable[[Environment], Expression]):
        self.name = name
        self.parameters = parameters
        self.body = body


class PrimExpr(Expression):
    def __init__(self, name: str, arity: int, body: Callable[..., Expression]):
        self.name = name
        self.arity = arity
        self.body = body


class ExprPrinter:

    # instance vars
    _rules: Dict[Type, Callable[[Expression], str]]

    def __init__(self):
        self._rules = {
            SymbolExpr: ExprPrinter._stringify_symbol,
            StringExpr: ExprPrinter._stringify_string,
            NumberExpr: ExprPrinter._stringify_number,
            NilExpr: ExprPrinter._stringify_nil,
            PairExpr: ExprPrinter._stringify_pair,
            ProcExpr: ExprPrinter._stringify_procedure,
            PrimExpr: ExprPrinter._stringify_primitive,
        }

    def stringify(self, expr: Expression):
        f = self._rules[type(expr)]
        return f(expr)

    def _stringify_symbol(self, expr: SymbolExpr):
        return expr.literal

    def _stringify_string(self, expr: StringExpr):
        return '"%s"' % expr.literal

    def _stringify_number(self, expr: NumberExpr):
        return stringify_float(expr.literal)

    def _stringify_nil(self, expr: NilExpr):
        return '()'

    def _stringify_pair(self, expr: PairExpr):
        left_str = self.stringify(expr.left)
        right_str = self.stringify(expr.right)
        if isinstance(expr.right, NilExpr):
            return '(%s)' % left_str
        elif isinstance(expr.right, PairExpr):
            # right_str strip off paranthesis
            return '(%s %s)' % (left_str, right_str[1:-1])
        else:
            return '(%s . %s)' % (left_str, right_str)

    def _stringify_procedure(self, expr: ProcExpr):
        return '[procedure %s]' % expr.name

    def _stringify_primitive(self, expr: PrimExpr):
        return '[primitive %s]' % expr.name


class ExprList:

    @staticmethod
    def make_list(expr_list: List[Expression]):
        head: Expression = NilExpr()
        for i in range(len(expr_list)-1, -1, -1):
            head = PairExpr(expr_list[i], head)
        return head

    @staticmethod
    def length(expr: Expression):
        count = 0
        head = expr
        while isinstance(head, PairExpr):
            count += 1
            head = head.right
        return count

# scheme parser: tokens -> scheme lists
# ref: https://craftinginterpreters.com/parsing-expressions.html

class Parser:
    '''
    expression -> SYMBOL | STRING | NUMBER | quote | list;
    quote -> QUOTE expression;
    list -> LEFT_PAREN ( expression )* RIGHT_PAREN;
    '''

    _rules: Dict[TokenTag, Callable[[Token], Expression]]
    _tokens: List[Token]
    _current: int
    _token_printer: TokenPrinter

    def __init__(self):
        self._rules = {
            TokenTag.SYMBOL: self._parse_symbol,
            TokenTag.NUMBER: self._parse_number,
            TokenTag.STRING: self._parse_string,
            TokenTag.QUOTE: self._parse_quote,
            TokenTag.LEFT_PAREN: self._parse_left_paren,
            TokenTag.RIGHT_PAREN: self._parse_right_paren
        }
        self._restart([])
        self._token_printer = TokenPrinter()

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
        return self._rules[token.tag](token)

    def _parse_symbol(self, token: Token):
        return SymbolExpr(token.literal)

    def _parse_string(self, token: Token):
        return StringExpr(token.literal)

    def _parse_number(self, token: Token):
        return NumberExpr(token.literal)

    def _parse_quote(self, _token: Token):
        expr_list: List[Expression] = []
        expr_list.append(SymbolExpr('quote'))
        expr_list.append(self._parse_recursive())
        return ExprList.make_list(expr_list)

    def _parse_left_paren(self, _token: Token):
        expr_list: List[Expression] = []
        while not self._is_at_end() and self._peek().tag != TokenTag.RIGHT_PAREN:
            expr_list.append(self._parse_recursive())
        if self._is_at_end() or self._peek().tag != TokenTag.RIGHT_PAREN:
            panic('parser: list missing right parenthesis')
        self._advance()  # consume right parenthesis
        return ExprList.make_list(expr_list)

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

# scheme resolver
# see 4.1.6
# TODO: add resolver


# scheme analyzer
# we assume operator cannot be a procedure that evaluates to symbol
# see 4.1.7


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
            if expr.tag == NUMBER or expr.tag == STRING:
                return lambda _: expr
            elif expr.tag == SYMBOL:
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
            if hexpr.tag == NUMBER:
                panic('analyzer: number cannot be operator or special form')
            if hexpr.tag == STRING:
                panic('analyzer: string cannot be operator or special form')
            if hexpr.tag == SYMBOL:
                f = self._special_forms.get(hexpr.value, None)
                if f is not None:
                    return f(expr, self.analyze)
            return self._application(expr, self.analyze)


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
        if head.next.expr.tag != LIST:
            panic('analyze_define: procedure parameters must be a list')
        parameters: List[str] = []
        para_exprs: LinkedList = head.next.expr.value
        while para_exprs is not None:
            if para_exprs.expr.tag != SYMBOL:
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
        if operator.tag == PRIMITIVE:
            primitive: Primitive = operator.value
            if len(operands) != primitive.arity:
                panic('analyze_application: primitive incorrect arity %d, should be %d' % (
                    len(operands), primitive.arity))
            return primitive.body(*operands)
        elif operator.tag == PROCEDURE:
            procedure: Procedure = operator.value
            if len(operands) != len(procedure.parameters):
                panic('analyze_application: procedure incorrect arity %d, should be %d' % (
                    len(operands), len(procedure.parameters)))
            new_env = env.extend(procedure.parameters, operands)
            return procedure.body(new_env)
        else:
            panic(
                'analyze_application: expression of type %s cannot be used as operator' % operator.tag)
    return _analyze_application


def prim_op_number2(py_func: Callable[[float, float], float], x: Expression, y: Expression) -> Expression:
    if x.tag != NUMBER or y.tag != NUMBER:
        panic('%s: both operator should be number, now %s and %s' %
              (py_func.__name__, x.tag, y.tag))
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
    token_printer = TokenPrinter()
    token_str = ', '.join([token_printer.stringify(t) for t in tokens])
    print('tokens: %s' % token_str)
    if token_str_expect is not None:
        assert token_str == token_str_expect
    # parse
    parser = Parser()
    expr = parser.parse(tokens)
    expr_printer = ExprPrinter()
    expr_str = expr_printer.stringify(expr) if expr else ''
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

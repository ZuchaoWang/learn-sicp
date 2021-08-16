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
from typing import Callable, ClassVar, Dict, List, Optional, Set, Tuple, Type, Union, cast


class PanicError(Exception):
    def __init__(self, message: str):
        self.message = message


def scheme_panic(message: str):
    raise PanicError(message)


scheme_buf: List[str] = []


def scheme_print(message: str):
    scheme_buf.append(message)


def scheme_flush():
    res = ''.join(scheme_buf)
    scheme_buf.clear()
    return res


def stringify_float(x: float):
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
class TokenTag(enum.Enum):
    LEFT_PAREN = enum.auto()
    RIGHT_PAREN = enum.auto()
    QUOTE = enum.auto()
    SYMBOL = enum.auto()
    STRING = enum.auto()
    NUMBER = enum.auto()
    BOOLEAN = enum.auto()


class Token:
    def __init__(self, tag: TokenTag, line: int, lexeme: str, literal):
        self.tag = tag
        self.line = line
        self.lexeme = lexeme
        self.literal = literal


class TokenStringifier:
    _rules: Dict[TokenTag, Callable[[Token], str]]

    def __init__(self):
        self._rules = {
            TokenTag.LEFT_PAREN: self._stringify_other,
            TokenTag.RIGHT_PAREN: self._stringify_other,
            TokenTag.QUOTE: self._stringify_other,
            TokenTag.SYMBOL: self._stringify_string,
            TokenTag.STRING: self._stringify_string,
            TokenTag.NUMBER: self._stringify_number,
            TokenTag.BOOLEAN: self._stringify_boolean,
        }

    def stringify(self, token: Token):
        f = self._rules[token.tag]
        return f(token)

    def _stringify_number(self, token: Token):
        return '%s:%s' % (token.tag.name, stringify_float(token.literal))

    def _stringify_string(self, token: Token):
        return '%s:%s' % (token.tag.name, token.literal)

    def _stringify_boolean(self, token: Token):
        return '%s:%s' % (token.tag.name, '#t' if token.literal else '#f')

    def _stringify_other(self, token: Token):
        return token.tag.name


token_stringifier = TokenStringifier()


def stringify_token(token: Token):
    return token_stringifier.stringify(token)


class ScannerError(Exception):
    def __init__(self, line: int, message: str):
        self.line = line
        self.message = message

    def __str__(self):
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
        except ScannerError as err:
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
            self._add_token(TokenTag.QUOTE)

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
        lexemem = self._source[self._start+1:self._current-1]
        self._add_token(TokenTag.STRING, lexemem)

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
                lexemem = float(substr)
                self._add_token(TokenTag.NUMBER, lexemem)
            except:
                # finally try symbol
                lexemem = substr
                if lexemem[0].isnumeric():
                    self._error(
                        'symbol should not start with number: %s' % lexemem)
                self._add_token(TokenTag.SYMBOL, lexemem)

    def _error(self, message: str):
        raise ScannerError(self._line, message)

    @staticmethod
    def _can_terminate_nonstring(c: str):
        return c.isspace() or c == '(' or c == ')'

# expression and environment


class Expression:
    pass


class EnvironmentError(Exception):
    def __init__(self, message: str):
        self.message = message


class Environment:
    def __init__(self, bindings: Dict[str, Expression] = {}, enclosing: Optional["Environment"] = None):
        self._bindings = bindings
        self._enclosing = enclosing

    def define(self, name: str, expr: Expression):
        self._bindings[name] = expr

    def set(self, name: str, expr: Expression):
        env = self._find_env(name)
        if env is None:
            self._error('%s not defined' % name)
        else:
            env._bindings[name] = expr

    def lookup(self, name: str):
        env = self._find_env(name)
        if env is None:
            self._error('%s not defined' % name)
        else:
            return env._bindings[name]

    def _find_env(self, name: str):
        env = self
        while True:
            if name in env._bindings:
                return env
            elif env._enclosing is not None:
                env = env._enclosing
            else:
                return None

    def set_at(self, distance: int, name: str, expr: Expression):
        env = self._ancestor(distance)
        env._bindings[name] = expr

    def lookup_at(self, distance: int, name: str):
        env = self._ancestor(distance)
        return env._bindings[name]

    def _ancestor(self, distance: int):
        env = self
        while distance > 0:
            if env._enclosing is None:
                self._error('no ancestor at distance %d' % distance)
            else:
                env = env._enclosing
                distance -= 1
        return env

    def define_primitive(self, name: str, py_func: Callable):
        arity = len(inspect.getfullargspec(py_func).args)
        primitive = PrimExpr(name, arity, py_func)
        self._bindings[name] = primitive
        return primitive

    def extend(self, parameter: List[str], arguments: List[Expression]):
        return Environment(dict(zip(parameter, arguments)), self)

    def _error(self, message: str):
        # this error will be handled in other classes
        raise EnvironmentError(message)

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


class BooleanExpr(Expression):
    def __init__(self, literal: bool):
        self.literal = literal


class NilExpr(Expression):
    pass


class UndefExpr(Expression):
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


class ExprStringifier:

    # instance vars
    _rules: Dict[Type, Callable[[Expression], str]]

    def __init__(self):
        self._rules = {
            SymbolExpr: self._stringify_symbol,
            StringExpr: self._stringify_string,
            NumberExpr: self._stringify_number,
            BooleanExpr: self._stringify_boolean,
            NilExpr: self._stringify_nil,
            UndefExpr: self._stringify_undef,
            PairExpr: self._stringify_pair,
            ProcExpr: self._stringify_procedure,
            PrimExpr: self._stringify_primitive,
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

    def _stringify_boolean(self, expr: BooleanExpr):
        return '#t' if expr.literal else '#f'

    def _stringify_nil(self, expr: NilExpr):
        return '()'

    def _stringify_undef(self, expr: UndefExpr):
        return '#<undef>'

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


expr_printer = ExprStringifier()


def stringify_expr(expr: Expression):
    return expr_printer.stringify(expr)


class ExprEqualityChecker:
    # instance vars
    _rules: Dict[Type, Callable[[Expression, Expression], bool]]

    def __init__(self):
        self._rules = {
            SymbolExpr: self._check_literal,
            StringExpr: self._check_literal,
            NumberExpr: self._check_literal,
            BooleanExpr: self._check_literal,
            NilExpr: self._check_true,
            UndefExpr: self._check_true,
            PairExpr: self._check_object,
            ProcExpr: self._check_object,
            PrimExpr: self._check_object,
        }

    def check(self, x: Expression, y: Expression):
        if type(x) == type(y):
            f = self._rules[type(x)]
            return f(x, y)
        else:
            return False

    def _check_literal(self, x: Union[SymbolExpr, StringExpr, NumberExpr, BooleanExpr], y: Union[SymbolExpr, StringExpr, NumberExpr, BooleanExpr]):
        return x.literal == y.literal

    def _check_true(self, x: Union[NilExpr, UndefExpr], y: Union[NilExpr, UndefExpr]):
        return True

    def _check_object(self, x: Union[PairExpr, PrimExpr, ProcExpr], y: Union[PairExpr, PrimExpr, ProcExpr]):
        return x == y


expr_equality_checker = ExprEqualityChecker()


def is_equal_expr(x: Expression, y: Expression):
    return expr_equality_checker.check(x, y)


def is_truthy_expr(expr: Expression):
    return type(expr) != BooleanExpr or cast(BooleanExpr, expr).literal == True


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


class ParserError(Exception):
    def __init__(self, token: Optional[Token], message: str):
        self.token = token
        self.message = message

    def __str__(self):
        if self.token is not None:
            return 'parser error at %s in line %d: %s' % (stringify_token(self.token), self.token.line+1, self.message)
        else:
            return 'parser error: %s' % self.message


class Parser:
    '''
    expression -> SYMBOL | STRING | NUMBER | quote | list;
    quote -> QUOTE expression;
    list -> LEFT_PAREN ( expression )* RIGHT_PAREN;
    '''

    _rules: Dict[TokenTag, Callable[[Token], Expression]]
    _tokens: List[Token]
    _current: int

    def __init__(self):
        self._rules = {
            TokenTag.SYMBOL: self._parse_symbol,
            TokenTag.NUMBER: self._parse_number,
            TokenTag.STRING: self._parse_string,
            TokenTag.BOOLEAN: self._parse_boolean,
            TokenTag.QUOTE: self._parse_quote,
            TokenTag.LEFT_PAREN: self._parse_left_paren,
            TokenTag.RIGHT_PAREN: self._parse_right_paren
        }
        self._restart([])

    def parse(self, tokens: List[Token]):
        self._restart(tokens)
        try:
            if self._is_at_end():
                self._error(None, 'no token')
            expr = self._parse_recursive()
            if not self._is_at_end():
                self._error(self.tokens[self.current], 'excessive tokens')
        except ParserError as err:
            scheme_panic(str(err))
        return expr

    def _restart(self, tokens: List[Token]):
        self.tokens = tokens
        self.current = 0

    def _parse_recursive(self) -> Expression:
        token = self._advance()
        return self._rules[token.tag](token)

    def _parse_symbol(self, token: Token):
        return SymbolExpr(token.literal)

    def _parse_string(self, token: Token):
        return StringExpr(token.literal)

    def _parse_number(self, token: Token):
        return NumberExpr(token.literal)

    def _parse_boolean(self, token: Token):
        return BooleanExpr(token.literal)

    def _parse_quote(self, token: Token):
        expr_list: List[Expression] = []
        expr_list.append(SymbolExpr('quote'))
        if self._is_at_end():
            self._error(token, 'quote cannot be at the end')
        expr_list.append(self._parse_recursive())
        return ExprList.make_list(expr_list)

    def _parse_left_paren(self, token: Token):
        expr_list: List[Expression] = []
        while not self._is_at_end() and self._peek().tag != TokenTag.RIGHT_PAREN:
            expr_list.append(self._parse_recursive())
        if self._is_at_end() or self._peek().tag != TokenTag.RIGHT_PAREN:
            self._error(token, 'list missing right parenthesis')
        self._advance()  # consume right parenthesis
        return ExprList.make_list(expr_list)

    def _parse_right_paren(self, token: Token):
        self._error(token, 'unmatched right parenthesis')

    def _is_at_end(self):
        return self.current >= len(self.tokens)

    def _advance(self):
        token = self.tokens[self.current]
        self.current += 1
        return token

    def _peek(self):
        return self.tokens[self.current]

    def _error(self, token: Optional[Token], message: str):
        raise ParserError(token, message)


class PrimError(Exception):
    def __init__(self, message):
        self.message = message


def make_prim_arithmetic(py_func: Callable[[float, float], float]):
    def _prim_arithmetic(x: Expression, y: Expression) -> Expression:
        if not isinstance(x, NumberExpr) or not isinstance(y, NumberExpr):
            raise PrimError('%s requires both operators to be numbers, now %s and %s' % (
                py_func.__name__, type(x), type(y)))
        x = cast(NumberExpr, x)
        y = cast(NumberExpr, y)
        res = py_func(x.literal, y.literal)
        return NumberExpr(res)
    return _prim_arithmetic


prim_op_add = make_prim_arithmetic(lambda a, b: a+b)
prim_op_sub = make_prim_arithmetic(lambda a, b: a-b)


def make_prim_compare(py_func: Callable[[float, float], bool]):
    def _prim_compare(x: Expression, y: Expression) -> Expression:
        if not isinstance(x, NumberExpr) or not isinstance(y, NumberExpr):
            raise PrimError('%s requires both operators to be numbers, now %s and %s' % (
                py_func.__name__, type(x), type(y)))
        x = cast(NumberExpr, x)
        y = cast(NumberExpr, y)
        res = py_func(x.literal, y.literal)
        return BooleanExpr(res)
    return _prim_compare


prim_op_eq = make_prim_compare(lambda a, b: a == b)
prim_op_lt = make_prim_compare(lambda a, b: a < b)
prim_op_gt = make_prim_compare(lambda a, b: a > b)


def prim_equal(x: Expression, y: Expression):
    return BooleanExpr(is_equal_expr(x, y))


def prim_display(expr: Expression):
    scheme_print(expr_printer.stringify(expr))
    return UndefExpr()


def prim_newline():
    scheme_print('\n')
    return UndefExpr()


class RuntimeError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self):
        return 'runtime error at %s in line %d: %s' % (stringify_token(self.token), self.token.line+1, self.message)


# TODO: evaluator


def test_one(source: str, **kargs: str):
    # source
    print('source: %s' % source)
    try:
        # scan
        scanner = Scanner()
        tokens = scanner.scan(source)
        token_str = ', '.join([stringify_token(t) for t in tokens])
        print('tokens: %s' % token_str)
        if 'tokens' in kargs:
            assert token_str == kargs['tokens']
        if len(tokens):
            # parse
            parser = Parser()
            expr = parser.parse(tokens)
            expr_str = stringify_expr(expr) if expr else ''
            print('expression: %s' % expr_str)
            if 'expression' in kargs:
                assert expr_str == kargs['expression']
    except PanicError as err:
        # any kind of panic
        print('panic: %s' % err.message)
        if 'panic' in kargs:
            assert err.message == kargs['panic']
    print('----------')


def test():
    test_one(
        '',
        tokens = ''
    )
    test_one(
        '#true',
        panic = 'scanner error in line 1: invalid boolean: #true'
    )
    test_one(
        '#t',
        tokens = 'BOOLEAN:#t'
    )
    test_one(
        '(display\n"abc)',
        panic = 'scanner error in line 2: unterminated string: "abc)'
    )
    test_one(
        '(display\n"abc"',
        tokens = 'LEFT_PAREN, SYMBOL:display, STRING:abc',
        panic = 'parser error at LEFT_PAREN in line 1: list missing right parenthesis'
    )
    test_one(
        '(display\n"abc")',
        tokens = 'LEFT_PAREN, SYMBOL:display, STRING:abc, RIGHT_PAREN',
        expression = '(display "abc")'
    )
    test_one(
        '(+ 1 2.5)',
        tokens = 'LEFT_PAREN, SYMBOL:+, NUMBER:1, NUMBER:2.500, RIGHT_PAREN',
        expression = '(+ 1 2.500)'
    )
    test_one(
        '\'(a (b c))',
        tokens = 'QUOTE, LEFT_PAREN, SYMBOL:a, LEFT_PAREN, SYMBOL:b, SYMBOL:c, RIGHT_PAREN, RIGHT_PAREN',
        expression = '(quote (a (b c)))'
    )


if __name__ == '__main__':
    test()

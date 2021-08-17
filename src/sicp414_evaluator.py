# the goal is to implement a simplified scheme language
# it's only a toy, which will not follow the language specification
# and only support a small proportion of the feautres
# no guarantee for performance, or even correctness (we have so few tests)
#
# the input of the language is a string, which will be transformed to tokens via Scanner
# then Parser transforms tokens to scheme expression tree
# finally the express tree is evaluated directly

import sys
import inspect
import enum
from typing import Any, Callable, ClassVar, Dict, List, Optional, Set, Type, Union, cast


# utilities

def stringify_float(x: float):
    if (x == int(x)):
        return '%d' % x
    else:
        return '%.3f' % x


def stringify_bool(x: bool):
    return '#t' if x else '#f'


# global config
# 
# with suppress_panic being True
# error will not exit process directly
# instead error is turned into panic, handled by test_one
#
# with suppress_print being True
# print will not go to console directly
# instead it is buffer, and later explicitly dumps as string
#
# both make test easier


scheme_config = {
    'suppress_panic': True,
    'suppress_print': True
}

class PanicError(Exception):
    def __init__(self, message: str):
        self.message = message


def scheme_panic(message: str):
    if scheme_config['suppress_panic']:
        raise PanicError(message)
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


# scheme scanner: string -> tokens
# only support paranthesis, quote, symbol, string, number, boolean
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
            self._add_token(TokenTag.QUOTE, 'quote')

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
        raise ScannerError(self._line, message)

    @staticmethod
    def _can_terminate_nonstring(c: str):
        return c.isspace() or c == '(' or c == ')'


# convert token into string

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
        return '%s:%s' % (token.tag.name, stringify_bool(token.literal))

    def _stringify_other(self, token: Token):
        return token.tag.name


# we only need one TokenStringifier
# so let's declare its instance
# and wrap it in stringify_token

_token_stringifier = TokenStringifier()

def stringify_token(token: Token):
    return _token_stringifier.stringify(token)


# expression and schemeval
# will specified as various classes, and this helps static type checking
# if we represent it as single class with different tag (like token), we won't have type checking with python's typing

class Expression:
    pass


class SchemeVal:
    pass


# environment
# see chap 4.1.3 and https://craftinginterpreters.com/statements-and-state.html
# it supports set_at and lookup_at, which will be used in resolver
# ref: https://craftinginterpreters.com/resolving-and-binding.html

class EnvironmentError(Exception):
    def __init__(self, message: str):
        self.message = message


class Environment:
    def __init__(self, bindings: Dict[str, SchemeVal] = {}, enclosing: Optional["Environment"] = None):
        self._bindings = bindings
        self._enclosing = enclosing

    def define(self, name: str, value: SchemeVal):
        self._bindings[name] = value

    def set(self, name: str, value: SchemeVal):
        env = self._find_env(name)
        if env is None:
            self._error('%s not defined' % name)
        else:
            env._bindings[name] = value

    def lookup(self, name: str):
        env = self._find_env(name)
        if env is None:
            self._error('%s not defined' % name)
        else:
            return env._bindings[name]

    def _find_env(self, name: str):
        env: Optional[Environment] = self
        while env is not None:
            if name in env._bindings:
                return env
            env = env._enclosing
        return None

    def set_at(self, distance: int, name: str, value: SchemeVal):
        env = self._ancestor(distance)
        env._bindings[name] = value

    def lookup_at(self, distance: int, name: str):
        env = self._ancestor(distance)
        return env._bindings[name]

    def _ancestor(self, distance: int):
        # TODO
        env = self
        while distance > 0:
            if env._enclosing is None:
                self._error('no ancestor at distance %d' % distance)
            else:
                env = env._enclosing
                distance -= 1
        return env

    # def define_primitive(self, name: str, py_func: Callable):
    #     arity = len(inspect.getfullargspec(py_func).args)
    #     primitive = PrimExpr(name, arity, py_func)
    #     self._bindings[name] = primitive
    #     return primitive

    def extend(self, parameter: List[str], arguments: List[SchemeVal]):
        return Environment(dict(zip(parameter, arguments)), self)

    def _error(self, message: str):
        # this error will be handled in other classes
        raise EnvironmentError(message)


# define different types of expressions as difference classes for better type checking
#
# we do not differentiate between object and experssion
# because they are so similar in Scheme
# in fact, a list can be both an object and an expression
#
# empty list is represented as special nil expression
# non-empty list is represented as pairs
#
# conplex syntax are just represented as list, e.g. if, define, begin
# see chap 4.1.2
#
# we also have undef


class SymbolExpr(Expression):
    def __init__(self, token: Token):
        self.token = token


class StringExpr(Expression):
    def __init__(self, token: Token):
        self.token = token


class NumberExpr(Expression):
    def __init__(self, token: Token):
        self.token = token


class BooleanExpr(Expression):
    def __init__(self, token: Token):
        self.token = token


class ListExpr(Expression):
    def __init__(self, token: Token, expressions: List[Expression]):
        self.token = token # left paranthesis
        self.expressions = expressions


# convert expression into string

class ExprStringifier:

    # instance vars
    _rules: Dict[Type, Callable[[Expression], str]]

    def __init__(self):
        self._rules = {
            SymbolExpr: self._stringify_symbol,
            StringExpr: self._stringify_string,
            NumberExpr: self._stringify_number,
            BooleanExpr: self._stringify_boolean,
            ListExpr: self._stringify_list,
        }

    def stringify(self, expr: Expression):
        f = self._rules[type(expr)]
        return f(expr)

    def _stringify_symbol(self, expr: SymbolExpr):
        return expr.token.literal

    def _stringify_string(self, expr: StringExpr):
        return '"%s"' % expr.token.literal

    def _stringify_number(self, expr: NumberExpr):
        return stringify_float(expr.token.literal)

    def _stringify_boolean(self, expr: BooleanExpr):
        return stringify_bool(expr.token.literal)

    def _stringify_list(self, expr: ListExpr):
        substrs = [self.stringify(subexpr) for subexpr in expr.expressions]
        return '(%s)' % (' '.join(substrs))


# we only need one ExprStringifier
# so let's declare its instance
# and wrap it in stringify_expr

_expr_stringifier = ExprStringifier()


def stringify_expr(expr: Expression):
    return _expr_stringifier.stringify(expr)


# scheme parser: tokens -> scheme lists
# very simple recusive descent, see how _parse_quote and _parse_left_paren call _parse_recursive
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
        return SymbolExpr(token)

    def _parse_string(self, token: Token):
        return StringExpr(token)

    def _parse_number(self, token: Token):
        return NumberExpr(token)

    def _parse_boolean(self, token: Token):
        return BooleanExpr(token)

    def _parse_quote(self, token: Token):
        expr_list: List[Expression] = []
        expr_list.append(SymbolExpr(token))
        if self._is_at_end():
            self._error(token, 'quote cannot be at the end')
        expr_list.append(self._parse_recursive())
        return ListExpr(token, expr_list)

    def _parse_left_paren(self, token: Token):
        expr_list: List[Expression] = []
        while not self._is_at_end() and self._peek().tag != TokenTag.RIGHT_PAREN:
            expr_list.append(self._parse_recursive())
        if self._is_at_end() or self._peek().tag != TokenTag.RIGHT_PAREN:
            self._error(token, 'list missing right parenthesis')
        self._advance()  # consume right parenthesis
        return ListExpr(token, expr_list)

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

# scheme value definitions

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
        self.token: Optional[Token] = None


class ProcVal(SchemeVal):
    def __init__(self, name: str, parameters: List[str], body: Callable[[Environment], SchemeVal]):
        self.name = name
        self.parameters = parameters
        self.body = body


class PrimVal(SchemeVal):
    def __init__(self, name: str, arity: int, body: Callable[..., SchemeVal]):
        self.name = name
        self.arity = arity
        self.body = body

# stringify value

class ValueStringifier:

    # instance vars
    _rules: Dict[Type, Callable[[SchemeVal], str]]

    def __init__(self):
        self._rules = {
            SymbolVal: self._stringify_symbol,
            StringVal: self._stringify_string,
            NumberVal: self._stringify_number,
            BooleanVal: self._stringify_boolean,
            NilVal: self._stringify_nil,
            UndefVal: self._stringify_undef,
            PairVal: self._stringify_pair,
            ProcVal: self._stringify_procedure,
            PrimVal: self._stringify_primitive,
        }

    def stringify(self, sv: SchemeVal):
        f = self._rules[type(sv)]
        return f(sv)

    def _stringify_symbol(self, sv: SymbolVal):
        return sv.value

    def _stringify_string(self, sv: StringVal):
        return '"%s"' % sv.value

    def _stringify_number(self, sv: NumberVal):
        return stringify_float(sv.value)

    def _stringify_boolean(self, sv: BooleanVal):
        return '#t' if sv.value else '#f'

    def _stringify_nil(self, sv: NilVal):
        return '()'

    def _stringify_undef(self, sv: UndefVal):
        return '#<undef>'

    def _stringify_pair(self, sv: PairVal):
        left_str = self.stringify(sv.left)
        right_str = self.stringify(sv.right)
        if isinstance(sv.right, NilVal):
            return '(%s)' % left_str
        elif isinstance(sv.right, PairVal):
            # right_str strip off paranthesis
            return '(%s %s)' % (left_str, right_str[1:-1])
        else:
            return '(%s . %s)' % (left_str, right_str)

    def _stringify_procedure(self, sv: ProcVal):
        return '[procedure %s]' % sv.name

    def _stringify_primitive(self, sv: PrimVal):
        return '[primitive %s]' % sv.name

# we only need one ValueStringifier
# so let's declare its instance
# and wrap it in stringify_value

_value_stringifier = ValueStringifier()


def stringify_value(sv: SchemeVal):
    return _value_stringifier.stringify(sv)

# check whether two values are equal
# defined according to scheme's equal? procedure

class EqualityChecker:
    # instance vars
    _rules: Dict[Type, Callable[[SchemeVal, SchemeVal], bool]]

    def __init__(self):
        self._rules = {
            SymbolVal: self._check_literal,
            StringVal: self._check_literal,
            NumberVal: self._check_literal,
            BooleanVal: self._check_literal,
            NilVal: self._check_true,
            UndefVal: self._check_true,
            PairVal: self._check_object,
            ProcVal: self._check_object,
            PrimVal: self._check_object,
        }

    def check(self, x: SchemeVal, y: SchemeVal):
        if type(x) == type(y):
            f = self._rules[type(x)]
            return f(x, y)
        else:
            return False

    def _check_literal(self, x: Union[SymbolVal, StringVal, NumberVal, BooleanVal], y: Union[SymbolVal, StringVal, NumberVal, BooleanVal]):
        return x.value == y.value

    def _check_true(self, x: Union[NilVal, UndefVal], y: Union[NilVal, UndefVal]):
        return True

    def _check_object(self, x: Union[PairVal, PrimVal, ProcVal], y: Union[PairVal, PrimVal, ProcVal]):
        return x == y


_equality_checker = EqualityChecker()


def is_equal_expr(x: SchemeVal, y: SchemeVal):
    return _equality_checker.check(x, y)

# in scheme, the only thing not truthy is #f
# except that everything is truthy, including 0, "", '(), <#undef>

def is_truthy_expr(sv: SchemeVal):
    return type(sv) != BooleanVal or cast(BooleanVal, sv).value == True

# utility functions for pair value

def pair_from_list(val_list: List[SchemeVal]):
    head: SchemeVal = NilVal()
    for i in range(len(val_list)-1, -1, -1):
        head = PairVal(val_list[i], head)
    return head

def pair_length(sv: PairVal):
    count = 0
    head: SchemeVal = sv
    while isinstance(head, PairVal):
        count += 1
        head = head.right
    return count


# scheme evaluator
# correspond to chap 4.1.1

class PrimError(Exception):
    def __init__(self, message):
        self.message = message

class RuntimeError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self):
        return 'runtime error at %s in line %d: %s' % (stringify_token(self.token), self.token.line+1, self.message)


EvalFuncType = Callable[[Expression, Environment], Expression]


class Evaluator:
    _rules: Dict[str, Callable[[Expression, Environment, EvalFuncType], Expression]]
    _type_rules: Dict[Type, EvalFuncType]

    def __init__(self, rules: Dict[str, Callable[[Expression, Environment, EvalFuncType], Expression]]):
        self._rules = rules
        self._type_rules = {
      Val: self._eval_symbol, # type: ignore
            StringExpr: self._eval_pass, # type: ignore
            NumberExpr: self._eval_pass, # type: ignore
            BooleanExpr: self._eval_pass, # type: ignore
            NilExpr: self._eval_pass, # type: ignore
            UndefExpr: self._eval_pass, # type: ignore
            PairExpr: self._eval_pair, # type: ignore
        }

    def evaluate(self, expr: Expression, env: Environment) -> Expression:
        try:
            res = self._evaluate_recursive(expr, env)
        except RuntimeError as err:
            scheme_panic(str(err))
        return res

    def _evaluate_recursive(self, expr: Expression, env: Environment) -> Expression:
        f = self._type_rules[type(expr)]
        return f(expr, env)

    def _eval_symbol(self, expr: SymbolExpr, env: Environment) -> Expression:
        return self._rules['symbol'](expr, env, self._evaluate_recursive)

    def _eval_pass(self, expr: Union[StringExpr, NumberExpr, BooleanExpr, NilExpr, UndefExpr], env: Environment) -> Expression:
        return expr

    def _eval_pair(self, expr: PairExpr, env: Environment) -> Expression:
        if type(expr.left) == SymbolExpr:
            symbol_name = cast(SymbolExpr, expr.left).literal
            if symbol_name in self._rules:
                return self._rules[symbol_name](expr, env, self._evaluate_recursive)
        return self._rules['call'](expr, env, self._evaluate_recursive)


# evaluator rule definitions


def eval_symbol(expr: SymbolExpr, env: Environment, eval: EvalFuncType) -> Expression:
    try:
        return env.lookup(expr.literal)
    except EnvironmentError as err:
        raise RuntimeError(expr.token, err.message)


# primitive definitions


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
    scheme_print(stringify_expr(expr))
    return UndefExpr()


def prim_newline():
    scheme_print('\n')
    return UndefExpr()


def test_one(source: str, **kargs: str):
    # source
    print('* source: %s' % source)
    try:
        # scan
        scanner = Scanner()
        tokens = scanner.scan(source)
        token_str = ', '.join([stringify_token(t) for t in tokens])
        print('* tokens: %s' % token_str)
        if 'tokens' in kargs:
            assert token_str == kargs['tokens']
        if len(tokens):
            # parse
            parser = Parser()
            expr = parser.parse(tokens)
            expr_str = stringify_expr(expr) if expr else ''
            print('* expression: %s' % expr_str)
            if 'expression' in kargs:
                assert expr_str == kargs['expression']
    except PanicError as err:
        # any kind of panic
        print('* panic: %s' % err.message)
        if 'panic' in kargs:
            assert err.message == kargs['panic']
    print('----------')


def test():
    test_one(
        '',
        tokens = ''
    )
    test_one(
        '(if #true 1 2)',
        panic = 'scanner error in line 1: invalid boolean: #true'
    )
    test_one(
        '(if #t 1 2)',
        tokens = 'LEFT_PAREN, SYMBOL:if, BOOLEAN:#t, NUMBER:1, NUMBER:2, RIGHT_PAREN'
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

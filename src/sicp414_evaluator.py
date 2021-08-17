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
from typing import Any, Callable, ClassVar, Dict, List, Optional, Set, Tuple, Type, Union, cast


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

    def define(self, name: str, sv: SchemeVal):
        self._bindings[name] = sv

    def set(self, name: str, sv: SchemeVal):
        env = self._find_env(name)
        if env is None:
            self._error('%s not defined' % name)
        else:
            env._bindings[name] = sv

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

    # def set_at(self, distance: int, name: str, sv: SchemeVal):
    #     env = self._ancestor(distance)
    #     env._bindings[name] = sv

    # def lookup_at(self, distance: int, name: str):
    #     env = self._ancestor(distance)
    #     return env._bindings[name]

    # def _ancestor(self, distance: int):
    #     env = self
    #     while distance > 0:
    #         if env._enclosing is None:
    #             self._error('no ancestor at distance %d' % distance)
    #         else:
    #             env = env._enclosing
    #             distance -= 1
    #     return env

    def extend(self, parameter: List[str], arguments: List[SchemeVal]):
        return Environment(dict(zip(parameter, arguments)), self)

    def _error(self, message: str):
        # this error will be handled in other classes
        raise EnvironmentError(message)


# define different types of expressions as difference classes for better type checking
# conplex syntax are just represented as list, e.g. if, define, begin
# see chap 4.1.2


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
        self.token = token  # left paranthesis
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
#
# value and experssion are very similar in Scheme
# for example, a list can be both an object and an expression
# but we still differentitate them, giving them different base class, because
# undef, procedure and primitive only appears in value, not in expression
# expression need to store token for debugging, value doesn't have to
#
# because of the differentiation, we have to implement quote
# to convert expression to the "same" value
#
# empty list is represented as special nil expression
# non-empty list is represented as pairs


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


class PrimVal(SchemeVal):
    def __init__(self, name: str, arity: int, body: Callable[..., SchemeVal]):
        self.name = name
        self.arity = arity
        self.body = body


class ProcVal(SchemeVal):
    def __init__(self, name: str, parameters: List[str]):
        self.name = name
        self.parameters = parameters


class ProcPlainVal(ProcVal):
    def __init__(self, name: str, parameters: List[str], body: Expression):
        ProcVal.__init__(self, name, parameters)
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


def is_equal(x: SchemeVal, y: SchemeVal):
    return _equality_checker.check(x, y)

# in scheme, the only thing not truthy is #f
# except that everything is truthy, including 0, "", '(), <#undef>


def is_truthy(sv: SchemeVal):
    return type(sv) != BooleanVal or cast(BooleanVal, sv).value == True

# utility functions for pair value


def pair_from_list(sv_list: List[SchemeVal]):
    head: SchemeVal = NilVal()
    for i in range(len(sv_list)-1, -1, -1):
        head = PairVal(sv_list[i], head)
    return head


def pair_length(sv: PairVal):
    count = 0
    head: SchemeVal = sv
    while isinstance(head, PairVal):
        count += 1
        head = head.right
    return count

# quote expression to value


class ExprQuoter:

    # instance vars
    _rules: Dict[Type, Callable[[Expression], SchemeVal]]

    def __init__(self):
        self._rules = {
            SymbolExpr: self._quote_symbol,
            StringExpr: self._quote_string,
            NumberExpr: self._quote_number,
            BooleanExpr: self._quote_boolean,
            ListExpr: self._quote_list,
        }

    def quote(self, expr: Expression):
        f = self._rules[type(expr)]
        return f(expr)

    def _quote_symbol(self, expr: SymbolExpr):
        return SymbolVal(expr.token.literal)

    def _quote_string(self, expr: StringExpr):
        return StringVal(expr.token.literal)

    def _quote_number(self, expr: NumberExpr):
        return NumberVal(expr.token.literal)

    def _quote_boolean(self, expr: BooleanExpr):
        return BooleanVal(expr.token.literal)

    def _quote_list(self, expr: ListExpr):
        subvals = [self.quote(subexpr) for subexpr in expr.expressions]
        return pair_from_list(subvals)


_expr_quoter = ExprQuoter()


def quote_expr(expr: Expression):
    return _expr_quoter.quote(expr)


# scheme evaluator
# correspond to chap 4.1.1

class PrimError(Exception):
    def __init__(self, message):
        self.message = message


class ReparseError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message


class RuntimeError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self):
        return 'runtime error at %s in line %d: %s' % (stringify_token(self.token), self.token.line+1, self.message)


EvalFuncType = Callable[[Expression, Environment], SchemeVal]


class Evaluator:
    _list_rules: Dict[str, Callable[[Expression,
                                     Environment, EvalFuncType], SchemeVal]]
    _type_rules: Dict[Type, EvalFuncType]

    def __init__(self, list_rules: Dict[str, Callable[[Expression, Environment, EvalFuncType], SchemeVal]]):
        self._list_rules = list_rules
        self._type_rules = {
            SymbolExpr: self._eval_symbol,  # type: ignore
            StringExpr: self._eval_string,  # type: ignore
            NumberExpr: self._eval_number,  # type: ignore
            BooleanExpr: self._eval_boolean,  # type: ignore
            ListExpr: self._eval_list,  # type: ignore
        }

    def evaluate(self, expr: Expression, env: Environment) -> SchemeVal:
        try:
            res = self._eval_recursive(expr, env)
        except RuntimeError as err:
            scheme_panic(str(err))
        return res

    def _eval_recursive(self, expr: Expression, env: Environment) -> SchemeVal:
        f = self._type_rules[type(expr)]
        return f(expr, env)

    def _eval_rule(self, rule_name: str, expr: Expression, env: Environment) -> SchemeVal:
        try:
            f = self._list_rules[rule_name]
            res = f(expr, env, self._eval_recursive)
        except ReparseError as err:
            raise RuntimeError(err.token, err.message)
        return res

    def _eval_symbol(self, expr: SymbolExpr, env: Environment):
        try:
            return env.lookup(expr.token.literal)
        except EnvironmentError as err:
            raise RuntimeError(expr.token, err.message)

    def _eval_string(self, expr: StringExpr, env: Environment):
        return StringVal(expr.token.literal)

    def _eval_number(self, expr: NumberExpr, env: Environment):
        return NumberVal(expr.token.literal)

    def _eval_boolean(self, expr: BooleanExpr, env: Environment):
        return BooleanVal(expr.token.literal)

    def _eval_list(self, expr: ListExpr, env: Environment):
        if len(expr.expressions) == 0:
            return NilVal()
        elif type(expr.expressions[0]) == SymbolExpr:
            symbol_name = cast(SymbolExpr, expr.expressions[0]).token.literal
            if symbol_name in self._list_rules:
                return self._eval_rule(symbol_name, expr, env)
        return self._eval_rule('call', expr, env)


# evaluator rule definitions
# we use reparse to extract information from list, see chap4.1.2
# then use eval to calculate values


def reparse_quote(expr: ListExpr):
    if len(expr.expressions) != 2:
        raise ReparseError(
            expr.token, 'quote should have 2 expressions, now %d' % len(expr.expressions))
    return expr.expressions[1]


def eval_quote(expr: ListExpr, env: Environment, eval: EvalFuncType):
    content = reparse_quote(expr)
    return quote_expr(content)


def reparse_call(expr: ListExpr):
    if len(expr.expressions) == 0:
        raise ReparseError(expr.token, 'call should not be empty')
    operator_expr = expr.expressions[0]
    operands_expr = expr.expressions[1:]
    return operator_expr, operands_expr


def eval_call(expr: ListExpr, env: Environment, eval: EvalFuncType):
    operator_expr, operands_expr = reparse_call(expr)
    operator = eval(operator_expr, env)
    operands = [eval(subexpr, env) for subexpr in operands_expr]
    if isinstance(operator, PrimVal):
        if operator.arity != len(operands):
            raise RuntimeError(expr.token, '%s expect %d arguments, get %d' % (
                operator.name, operator.arity, len(operands)))
        try:
            return operator.body(*operands)
        except PrimError as err:
            raise RuntimeError(expr.token, err.message)
    elif isinstance(operator, ProcPlainVal):
        if len(operator.parameters) != len(operands):
            raise RuntimeError(expr.token, '%s expect %d arguments, get %d' % (
                operator.name, len(operator.parameters), len(operands)))
        new_env = env.extend(operator.parameters, operands)
        return eval(operator.body, new_env)
    else:
        raise RuntimeError(
            expr.token, 'cannot call %s expression' % type(expr).__name__)


def reparse_set(expr: ListExpr):
    if len(expr.expressions) != 3:
        raise ReparseError(
            expr.token, 'set should have 3 expressions, now %d' % len(expr.expressions))
    symbol_name = cast(SymbolExpr, expr.expressions[1])
    initializer_expr = expr.expressions[2]
    return symbol_name, initializer_expr


def eval_set(expr: ListExpr, env: Environment, eval: EvalFuncType):
    # return the value just set
    symbol_name, initializer_expr = reparse_set(expr)
    intializer = eval(initializer_expr, env)
    try:
        env.set(symbol_name.token.literal, intializer)
        return intializer
    except EnvironmentError as err:
        raise RuntimeError(expr.token, err.message)


def reparse_define(expr: ListExpr):
    if len(expr.expressions) != 3:
        raise ReparseError(
            expr.token, 'define should have 3 expressions, now %d' % len(expr.expressions))
    expr1 = expr.expressions[1]
    expr2 = expr.expressions[2]
    if isinstance(expr1, SymbolExpr):  # define variable
        var_name = expr1
        return var_name, expr.expressions[2]
    elif isinstance(expr1, ListExpr):  # define procedure
        if len(expr1.expressions) == 0:
            raise ReparseError(
                expr.token, 'define procedure should provide name')
        expr10 = expr1.expressions[0]
        if isinstance(expr10, SymbolExpr):
            proc_name = expr10
            proc_para = expr1.expressions[1:]
            proc_body = expr2
            if all([isinstance(p, SymbolExpr) for p in proc_para]):
                return proc_name, cast(List[SymbolExpr], proc_para), proc_body
            else:
                raise ReparseError(
                    expr.token, 'define procedure should use symbolic parameters')
        else:
            raise ReparseError(
                expr.token, 'define procedure should use symbolic name, now %s' % type(expr10).__name__)
    else:
        raise ReparseError(
            expr.token, 'define 2nd expression should be symbol or list, now %s' % type(expr1).__name__)


def eval_define(expr: ListExpr, env: Environment, eval: EvalFuncType):
    # return the symbol defined
    reparsed = reparse_define(expr)
    if len(reparsed) == 2:  # define variable
        var_name, initializer_expr = cast(
            Tuple[SymbolExpr, Expression], reparsed)
        intializer = eval(initializer_expr, env)
        env.define(var_name.token.literal, intializer)
        return SymbolVal(var_name.token.literal)
    else:  # define procedure
        proc_name, proc_para, proc_body = cast(
            Tuple[SymbolExpr, List[SymbolExpr], Expression], reparsed)
        proc_obj = ProcPlainVal(proc_name.token.literal, [
                                p.token.literal for p in proc_para], proc_body)
        env.define(proc_name.token.literal, proc_obj)
        return SymbolVal(proc_name.token.literal)


def reparse_if(expr: ListExpr):
    if len(expr.expressions) != 4:
        raise ReparseError(
            expr.token, 'if should have 4 expressions, now %d' % len(expr.expressions))
    pred_expr = expr.expressions[1]
    then_expr = expr.expressions[2]
    else_expr = expr.expressions[3]
    return pred_expr, then_expr, else_expr


def eval_if(expr: ListExpr, env: Environment, eval: EvalFuncType):
    # return the successful branch
    pred_expr, then_expr, else_expr = reparse_if(expr)
    pred_val = eval(pred_expr, env)
    if is_truthy(pred_val):
        return eval(then_expr, env)
    else:
        return eval(else_expr, env)


def reparse_begin(expr: ListExpr):
    if len(expr.expressions) < 2:
        raise ReparseError(
            expr.token, 'begin should have at least 2 expressions, now %d' % len(expr.expressions))
    return expr.expressions[1:]


def eval_begin(expr: ListExpr, env: Environment, eval: EvalFuncType):
    # return the last expression
    subexprs = reparse_begin(expr)
    for subexpr in subexprs[:-1]:
        eval(subexpr, env)
    return eval(subexprs[-1], env)


def reparse_lambda(expr: ListExpr):
    if len(expr.expressions) != 3:
        raise ReparseError(
            expr.token, 'lambda should have 3 expressions, now %d' % len(expr.expressions))
    expr1 = expr.expressions[1]
    expr2 = expr.expressions[2]
    if isinstance(expr1, ListExpr):
        proc_para = expr1.expressions
        proc_body = expr2
        if all([isinstance(p, SymbolExpr) for p in proc_para]):
            return cast(List[SymbolExpr], proc_para), proc_body
        else:
            raise ReparseError(
                expr.token, 'lambda should use symbolic parameters')
    else:
        raise ReparseError(
            expr.token, 'lambda 2nd expression should be list, now %s' % type(expr1).__name__)


def eval_lambda(expr: ListExpr, env: Environment, eval: EvalFuncType):
    # return the procedure itself
    proc_para, proc_body = reparse_lambda(expr)
    return ProcPlainVal('lambda', [p.token.literal for p in proc_para], proc_body)


# primitive definitions

def register_primitive(env: Environment, name: str, py_func: Callable):
    arity = len(inspect.getfullargspec(py_func).args)
    primitive = PrimVal(name, arity, py_func)
    env.define(name, primitive)


def make_prim_num2_num(py_func: Callable[[float, float], float]):
    def _prim_num2_num(x: SchemeVal, y: SchemeVal) -> SchemeVal:
        if not isinstance(x, NumberVal) or not isinstance(y, NumberVal):
            raise PrimError('%s requires both operators to be numbers, now %s and %s' % (
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
            raise PrimError('%s requires both operators to be numbers, now %s and %s' % (
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
            raise PrimError('not a pair')
    return _prim_pair_any


prim_length = make_prim_pair_any(lambda x: NumberVal(pair_length(x)))
prim_car = make_prim_pair_any(lambda x: x.left)
prim_cdr = make_prim_pair_any(lambda x: x.right)


def prim_cons(x: SchemeVal, y: SchemeVal):
    return PairVal(x, y)


def prim_pair(x: SchemeVal):
    return isinstance(x, PairVal)


def prim_null(x: SchemeVal):
    return isinstance(x, NilVal)


def prim_display(sv: SchemeVal):
    scheme_print(stringify_value(sv))
    return UndefVal()


def prim_newline():
    scheme_print('\n')
    return UndefVal()


# create out custom environment and evaluator

def make_global_env():
    glbenv = Environment()
    register_primitive(glbenv, '+', prim_op_add)
    register_primitive(glbenv, '-', prim_op_sub)
    register_primitive(glbenv, '*', prim_op_mul)
    register_primitive(glbenv, '/', prim_op_div)
    register_primitive(glbenv, '=', prim_op_eq)
    register_primitive(glbenv, '<', prim_op_lt)
    register_primitive(glbenv, '>', prim_op_gt)
    register_primitive(glbenv, '>', prim_op_gt)
    register_primitive(glbenv, 'equal?', prim_equal)
    register_primitive(glbenv, 'length', prim_length)
    register_primitive(glbenv, 'car', prim_car)
    register_primitive(glbenv, 'cdr', prim_cdr)
    register_primitive(glbenv, 'cons', prim_cons)
    register_primitive(glbenv, 'pair?', prim_pair)
    register_primitive(glbenv, 'null?', prim_null)
    register_primitive(glbenv, 'display', prim_display)
    register_primitive(glbenv, 'newline', prim_newline)
    return glbenv


def make_evaluator():
    list_rules = {
        'quote': eval_quote,
        'call': eval_call,
        'set!': eval_set,
        'define': eval_define,
        'if': eval_if,
        'begin': eval_begin,
        'lambda': eval_lambda
    }
    evaluator = Evaluator(list_rules)
    return evaluator

# each test tries to execute the source code as much as possible
# capture the output, panic and result
# print them and compare to expected value


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
            # evaluate
            glbenv = make_global_env()
            evaluator = make_evaluator()
            result = evaluator.evaluate(expr, glbenv)
            result_str = stringify_value(result)
            output_str = scheme_flush()
            if len(output_str):
                print('* output: %s' % output_str)
            if 'output' in kargs:
                assert output_str == kargs['output']
            print('* result: %s' % result_str)
            if 'result' in kargs:
                assert result_str == kargs['result']
    except PanicError as err:
        # any kind of panic
        print('* panic: %s' % err.message)
        if 'panic' in kargs:
            assert err.message == kargs['panic']
    print('----------')


def test_scan():
    test_one(
        '',
        tokens=''
    )
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


def test_parse():
    test_one(
        '(display\n"abc"',
        tokens='LEFT_PAREN, SYMBOL:display, STRING:abc',
        panic='parser error at LEFT_PAREN in line 1: list missing right parenthesis'
    )
    test_one(
        '(display\n"abc")',
        tokens='LEFT_PAREN, SYMBOL:display, STRING:abc, RIGHT_PAREN',
        expression='(display "abc")',
        output='"abc"',
        result='#<undef>'
    )
    test_one(
        '(+ 1 2.5)',
        tokens='LEFT_PAREN, SYMBOL:+, NUMBER:1, NUMBER:2.500, RIGHT_PAREN',
        expression='(+ 1 2.500)',
        result='3.500'
    )
    test_one(
        '\'(a (b c))',
        tokens='QUOTE, LEFT_PAREN, SYMBOL:a, LEFT_PAREN, SYMBOL:b, SYMBOL:c, RIGHT_PAREN, RIGHT_PAREN',
        expression='(quote (a (b c)))',
        result='(a (b c))'
    )


def test():
    test_scan()
    test_parse()


if __name__ == '__main__':
    test()

'''
the goal is to implement a simplified scheme language
it's only a toy, which will not follow the language specification
and only support a small proportion of the feautres
no guarantee for performance, or even correctness (we have so few tests)

the input of the language is a string, which will be transformed to tokens via Scanner
then Parser transforms tokens to a list of scheme expression trees
finally all expression trees in the list are evaluated directly
'''

import sys
import inspect
import enum
from typing import Any, Callable, ClassVar, Dict, List, Optional, Set, Tuple, Type, Union, cast


'''basic formatting'''


def format_float(x: float):
    if (x == int(x)):
        return '%d' % x
    else:
        return '%.3f' % x


def format_bool(x: bool):
    return '#t' if x else '#f'


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


class SchemeScannerError(Exception):
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
        raise SchemeScannerError(self._line, message)

    @staticmethod
    def _can_terminate_nonstring(c: str):
        return c.isspace() or c == '(' or c == ')'


class TokenStringifier:
    '''convert token into string'''

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
        return '%s:%s' % (token.tag.name, format_float(token.literal))

    def _stringify_string(self, token: Token):
        return '%s:%s' % (token.tag.name, token.literal)

    def _stringify_boolean(self, token: Token):
        return '%s:%s' % (token.tag.name, format_bool(token.literal))

    def _stringify_other(self, token: Token):
        return token.tag.name


'''
we only need one TokenStringifier
so let's declare its instance
and wrap it in stringify_token
'''

_token_stringifier = TokenStringifier()


def stringify_token(token: Token):
    return _token_stringifier.stringify(token)


'''
expression and schemeval
will specified as various classes, and this helps static type checking
if we represent it as single class with different tag (like token), we won't have type checking with python's typing
'''


class Expression:
    pass


class SchemeVal:
    pass


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
define different types of expressions as difference classes for better type checking
conplex syntax are just represented as list, e.g. if, define, begin
see chap 4.1.2
'''


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


class ExprStringifier:
    '''convert expression into string'''

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
        return format_float(expr.token.literal)

    def _stringify_boolean(self, expr: BooleanExpr):
        return format_bool(expr.token.literal)

    def _stringify_list(self, expr: ListExpr):
        substrs = [self.stringify(subexpr) for subexpr in expr.expressions]
        return '(%s)' % (' '.join(substrs))


'''
we only need one ExprStringifier
so let's declare its instance
and wrap it in stringify_expr
'''

_expr_stringifier = ExprStringifier()


def stringify_expr(expr: Expression):
    return _expr_stringifier.stringify(expr)


class SchemeParserError(Exception):
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
    scheme parser: tokens -> scheme lists
    very simple recursive descent, see how _parse_quote and _parse_left_paren call _parse_recursive
    ref: https://craftinginterpreters.com/parsing-expressions.html

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
        expr_list: List[Expression] = []
        try:
            while not self._is_at_end():
                expr = self._parse_recursive()
                expr_list.append(expr)
        except SchemeParserError as err:
            scheme_panic(str(err))
        return expr_list

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
        raise SchemeParserError(token, message)


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
        self.token: Optional[Token] = None


class PrimVal(SchemeVal):
    def __init__(self, name: str, arity: int, body: Callable[..., SchemeVal]):
        self.name = name
        self.arity = arity
        self.body = body


class ProcVal(SchemeVal):
    def __init__(self, name: str, parameters: List[str], env: Environment):
        self.name = name
        self.parameters = parameters
        self.env = env


class ProcPlainVal(ProcVal):
    '''A simple implementation of procedure, later we will have another representation'''

    def __init__(self, name: str, parameters: List[str], body: List[Expression], env: Environment):
        ProcVal.__init__(self, name, parameters, env)
        self.body = body


class ValueStringifier:
    '''convert value to string'''

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
        return sv.value

    def _stringify_number(self, sv: NumberVal):
        return format_float(sv.value)

    def _stringify_boolean(self, sv: BooleanVal):
        return format_bool(sv.value)

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


'''
we only need one ValueStringifier
so let's declare its instance
and wrap it in stringify_value
'''


_value_stringifier = ValueStringifier()


def stringify_value(sv: SchemeVal):
    return _value_stringifier.stringify(sv)


class EqualityChecker:
    '''
    check whether two values are equal
    defined according to scheme's equal? procedure
    '''

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


'''
in scheme, the only thing not truthy is #f
except that everything is truthy, including 0, "", '(), <#undef>
'''


def is_truthy(sv: SchemeVal):
    return type(sv) != BooleanVal or cast(BooleanVal, sv).value == True


'''utility functions for pair value'''


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


class ExprQuoter:
    '''quote convert expression to value'''

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


class SchemePrimError(Exception):
    def __init__(self, message):
        self.message = message


class SchemeReparseError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message


class SchemeRuntimeError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self):
        return 'runtime error at %s in line %d: %s' % (stringify_token(self.token), self.token.line+1, self.message)


EvalFuncType = Callable[[Expression, Environment], SchemeVal]


class Evaluator:
    '''scheme evaluator, correspond to chap 4.1.1'''

    _list_rules: Dict[str, Callable[[ListExpr,
                                     Environment, EvalFuncType], SchemeVal]]
    _type_rules: Dict[Type, EvalFuncType]

    def __init__(self, list_rules: Dict[str, Callable[[ListExpr, Environment, EvalFuncType], SchemeVal]]):
        self._list_rules = list_rules
        self._type_rules = {
            SymbolExpr: self._eval_symbol,  # type: ignore
            StringExpr: self._eval_string,  # type: ignore
            NumberExpr: self._eval_number,  # type: ignore
            BooleanExpr: self._eval_boolean,  # type: ignore
            ListExpr: self._eval_list,  # type: ignore
        }

    def evaluate(self, expr_list: List[Expression], env: Environment) -> SchemeVal:
        try:
            res: SchemeVal = UndefVal()
            for expr in expr_list:
                res = self._eval_recursive(expr, env)
        except SchemeRuntimeError as err:
            scheme_panic(str(err))
        return res

    def _eval_recursive(self, expr: Expression, env: Environment) -> SchemeVal:
        f = self._type_rules[type(expr)]
        return f(expr, env)

    def _eval_symbol(self, expr: SymbolExpr, env: Environment):
        try:
            return env_lookup(env, expr.token.literal)
        except SchemeEnvError:
            raise SchemeRuntimeError(expr.token, 'symbol undefined')

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
                return self._eval_list_rule(symbol_name, expr, env)
        return self._eval_list_rule('call', expr, env)

    def _eval_list_rule(self, rule_name: str, expr: ListExpr, env: Environment) -> SchemeVal:
        try:
            f = self._list_rules[rule_name]
            res = f(expr, env, self._eval_recursive)
        except SchemeReparseError as err:
            raise SchemeRuntimeError(err.token, err.message)
        return res

'''
evaluator rule definitions
we use reparse to extract information from list, see chap4.1.2
then use eval to calculate values
'''


def reparse_quote(expr: ListExpr):
    if len(expr.expressions) != 2:
        raise SchemeReparseError(
            expr.token, 'quote should have 2 expressions, now %d' % len(expr.expressions))
    return expr.expressions[1]


def eval_quote(expr: ListExpr, env: Environment, evl: EvalFuncType):
    content = reparse_quote(expr)
    return quote_expr(content)


def reparse_call(expr: ListExpr):
    if len(expr.expressions) == 0:
        raise SchemeReparseError(expr.token, 'call should not be empty')
    operator_expr = expr.expressions[0]
    operand_exprs = expr.expressions[1:]
    return operator_expr, operand_exprs


def pure_eval_call_prim(expr: ListExpr, operator: PrimVal, operands: List[SchemeVal]):
    if operator.arity != len(operands):
        raise SchemeRuntimeError(expr.token, '%s expect %d arguments, get %d' % (
            operator.name, operator.arity, len(operands)))
    try:
        return operator.body(*operands)
    except SchemePrimError as err:
        raise SchemeRuntimeError(expr.token, err.message)

def pure_eval_call_proc_plain(expr: ListExpr, operator: ProcPlainVal, operands: List[SchemeVal], evl: EvalFuncType):
    if len(operator.parameters) != len(operands):
        raise SchemeRuntimeError(expr.token, '%s expect %d arguments, get %d' % (
            operator.name, len(operator.parameters), len(operands)))
    new_env = env_extend(operator.env, operator.parameters, operands)
    for body_expr in operator.body:
        res = evl(body_expr, new_env)
    return res

def pure_eval_call_invalid(expr: ListExpr, operator: SchemeVal):
    raise SchemeRuntimeError(
        expr.token, 'cannot call %s value' % type(operator).__name__) 


def eval_call(expr: ListExpr, env: Environment, evl: EvalFuncType):
    operator_expr, operand_exprs = reparse_call(expr)
    operator = evl(operator_expr, env)
    operands = [evl(subexpr, env) for subexpr in operand_exprs]
    if isinstance(operator, PrimVal):
        return pure_eval_call_prim(expr, operator, operands)
    elif isinstance(operator, ProcPlainVal):
        return pure_eval_call_proc_plain(expr, operator, operands, evl)
    else:
        return pure_eval_call_invalid(expr, operator)


def reparse_set(expr: ListExpr):
    if len(expr.expressions) != 3:
        raise SchemeReparseError(
            expr.token, 'set should have 3 expressions, now %d' % len(expr.expressions))
    name_expr = cast(SymbolExpr, expr.expressions[1])
    initializer_expr = expr.expressions[2]
    return name_expr, initializer_expr


def eval_set(expr: ListExpr, env: Environment, evl: EvalFuncType):
    '''return the value just set'''
    name_expr, initializer_expr = reparse_set(expr)
    intializer = evl(initializer_expr, env)
    try:
        env_set(env, name_expr.token.literal, intializer)
        return intializer
    except SchemeEnvError:
        raise SchemeRuntimeError(expr.token, 'symbol undefined')


def reparse_define(expr: ListExpr):
    if len(expr.expressions) < 3:
        raise SchemeReparseError(
            expr.token, 'define should have at least 3 expressions, now %d' % len(expr.expressions))
    expr1 = expr.expressions[1]
    if isinstance(expr1, SymbolExpr):  # define variable
        name_expr = expr1
        if len(expr.expressions) != 3:
            raise SchemeReparseError(
                expr.token, 'define variable should have 3 expressions, now %d' % len(expr.expressions))
        return name_expr, expr.expressions[2]
    elif isinstance(expr1, ListExpr):  # define procedure
        if len(expr1.expressions) == 0:
            raise SchemeReparseError(
                expr.token, 'define procedure should provide name')
        expr10 = expr1.expressions[0]
        if isinstance(expr10, SymbolExpr):
            name_expr = expr10
            para_exprs = expr1.expressions[1:]
            body_exprs = expr.expressions[2:]
            if all([isinstance(p, SymbolExpr) for p in para_exprs]):
                return name_expr, cast(List[SymbolExpr], para_exprs), body_exprs
            else:
                raise SchemeReparseError(
                    expr.token, 'define procedure should use symbolic parameters')
        else:
            raise SchemeReparseError(
                expr.token, 'define procedure should use symbolic name, now %s' % type(expr10).__name__)
    else:
        raise SchemeReparseError(
            expr.token, 'define 2nd expression should be symbol or list, now %s' % type(expr1).__name__)


def eval_define(expr: ListExpr, env: Environment, evl: EvalFuncType):
    '''return the symbol defined'''
    reparsed = reparse_define(expr)
    if len(reparsed) == 2:  # define variable
        name_expr, initializer_expr = cast(
            Tuple[SymbolExpr, Expression], reparsed)
        intializer = evl(initializer_expr, env)
        env_define(env, name_expr.token.literal, intializer)
        return SymbolVal(name_expr.token.literal)
    else:  # define procedure
        name_expr, para_exprs, body_exprs = cast(
            Tuple[SymbolExpr, List[SymbolExpr], List[Expression]], reparsed)
        proc_obj = ProcPlainVal(name_expr.token.literal, [
                                p.token.literal for p in para_exprs], body_exprs, env)
        env_define(env, name_expr.token.literal, proc_obj)
        return SymbolVal(name_expr.token.literal)


def reparse_if(expr: ListExpr):
    if len(expr.expressions) != 4:
        raise SchemeReparseError(
            expr.token, 'if should have 4 expressions, now %d' % len(expr.expressions))
    pred_expr = expr.expressions[1]
    then_expr = expr.expressions[2]
    else_expr = expr.expressions[3]
    return pred_expr, then_expr, else_expr


def eval_if(expr: ListExpr, env: Environment, evl: EvalFuncType):
    '''return the successful branch'''
    pred_expr, then_expr, else_expr = reparse_if(expr)
    pred_val = evl(pred_expr, env)
    if is_truthy(pred_val):
        return evl(then_expr, env)
    else:
        return evl(else_expr, env)


def reparse_begin(expr: ListExpr):
    if len(expr.expressions) < 2:
        raise SchemeReparseError(
            expr.token, 'begin should have at least 2 expressions, now %d' % len(expr.expressions))
    return expr.expressions[1:]


def eval_begin(expr: ListExpr, env: Environment, evl: EvalFuncType):
    '''return the last expression'''
    subexprs = reparse_begin(expr)
    for subexpr in subexprs[:-1]:
        evl(subexpr, env)
    return evl(subexprs[-1], env)


def reparse_lambda(expr: ListExpr):
    if len(expr.expressions) < 3:
        raise SchemeReparseError(
            expr.token, 'lambda should have at least 3 expressions, now %d' % len(expr.expressions))
    expr1 = expr.expressions[1]
    if isinstance(expr1, ListExpr):
        para_exprs = expr1.expressions
        body_exprs = expr.expressions[2:]
        if all([isinstance(p, SymbolExpr) for p in para_exprs]):
            return cast(List[SymbolExpr], para_exprs), body_exprs
        else:
            raise SchemeReparseError(
                expr.token, 'lambda should use symbolic parameters')
    else:
        raise SchemeReparseError(
            expr.token, 'lambda 2nd expression should be list, now %s' % type(expr1).__name__)


def eval_lambda(expr: ListExpr, env: Environment, evl: EvalFuncType):
    '''return the procedure itself'''
    para_exprs, body_exprs = reparse_lambda(expr)
    return ProcPlainVal('lambda', [p.token.literal for p in para_exprs], body_exprs, env)


def reparse_and(expr: ListExpr):
    if len(expr.expressions) < 3:
        raise SchemeReparseError(
            expr.token, 'and should have at least 3 expressions, now %d' % len(expr.expressions))
    return expr.expressions[1:]


def eval_and(expr: ListExpr, env: Environment, evl: EvalFuncType):
    '''return the first false, otherwise the last'''
    subexprs = reparse_and(expr)
    for subexpr in subexprs:
        res = evl(subexpr, env)
        if not is_truthy(res):
            return res
    return res


def reparse_or(expr: ListExpr):
    if len(expr.expressions) < 3:
        raise SchemeReparseError(
            expr.token, 'or should have at least 3 expressions, now %d' % len(expr.expressions))
    return expr.expressions[1:]


def eval_or(expr: ListExpr, env: Environment, evl: EvalFuncType):
    '''return the first true, otherwise the last'''
    subexprs = reparse_or(expr)
    for subexpr in subexprs:
        res = evl(subexpr, env)
        if is_truthy(res):
            return res
    return res


def reparse_not(expr: ListExpr):
    if len(expr.expressions) != 2:
        raise SchemeReparseError(
            expr.token, 'not should have 2 expressions, now %d' % len(expr.expressions))
    return expr.expressions[1]


def eval_not(expr: ListExpr, env: Environment, evl: EvalFuncType):
    subexpr = reparse_not(expr)
    res = evl(subexpr, env)
    return BooleanVal(False) if is_truthy(res) else BooleanVal(True)


'''primitive definitions'''


def register_primitive(env: Environment, name: str, py_func: Callable):
    '''add primitive to environment'''
    arity = len(inspect.getfullargspec(py_func).args)
    primitive = PrimVal(name, arity, py_func)
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


'''create our custom environment and evaluator'''


def make_global_env():
    glbenv = Environment({})
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
        'lambda': eval_lambda,
        'and': eval_and,
        'or': eval_or,
        'not': eval_not
    }
    evaluator = Evaluator(list_rules)
    return evaluator


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
        scanner = Scanner()
        tokens = scanner.scan(source)
        token_str = ', '.join([stringify_token(t) for t in tokens])
        print('* tokens: %s' % token_str)
        if 'tokens' in kargs:
            assert token_str == kargs['tokens']

        # parse
        parser = Parser()
        expr_list = parser.parse(tokens)
        expr_str = ' '.join([stringify_expr(expr) for expr in expr_list])
        print('* expression: %s' % expr_str)
        if 'expression' in kargs:
            assert expr_str == kargs['expression']

        # evaluate
        glbenv = make_global_env()
        evaluator = make_evaluator()
        result = evaluator.evaluate(expr_list, glbenv)
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


def test_parse():
    test_one(
        '',
        tokens='',
        expression=''
    )
    test_one(
        '(display\n"abc"',
        tokens='LEFT_PAREN, SYMBOL:display, STRING:abc',
        panic='parser error at LEFT_PAREN in line 1: list missing right parenthesis'
    )
    test_one(
        '(display\n"abc")',
        tokens='LEFT_PAREN, SYMBOL:display, STRING:abc, RIGHT_PAREN',
        expression='(display "abc")',
        output='abc',
        result='#<undef>'
    )
    test_one(
        '\'(a (b c))',
        tokens='QUOTE, LEFT_PAREN, SYMBOL:a, LEFT_PAREN, SYMBOL:b, SYMBOL:c, RIGHT_PAREN, RIGHT_PAREN',
        expression='(quote (a (b c)))',
        result='(a (b c))'
    )
    test_one(
        '(define a 1)\n(set! a 2)',
        expression='(define a 1) (set! a 2)',
        result='2'
    )


def test_reparse():
    test_one(
        '(begin)',
        panic='runtime error at LEFT_PAREN in line 1: begin should have at least 2 expressions, now 1'
    )
    test_one(
        '(if 0 1 2 3)',
        panic='runtime error at LEFT_PAREN in line 1: if should have 4 expressions, now 5'
    )
    test_one(
        '(define ("a" "b") 3)',
        panic='runtime error at LEFT_PAREN in line 1: define procedure should use symbolic name, now StringExpr'
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


def test():
    test_scan()
    test_parse()
    test_reparse()
    test_env()
    test_eval()


if __name__ == '__main__':
    test()

'''
the goal is to implement a simplified scheme language
it's only a toy, which will not follow the language specification
and only support a small proportion of the feautres
no guarantee for performance, or even correctness (we have so few tests)

the input of the language is a string, which will be transformed to tokens via Scanner
then Parser transforms tokens to a scheme expression tree
we do not stop parsing at list level, instead we further parse list into call, if, define_var
the root of the resultant tree is a body expression, emcompassing all top level expressions
finally this expression tree is evaluated directly

we use simple class to represent token, expression, value
token is so simple and not likely to change, so we use single class for it, and add stringify method directly as __str__
expression and value are extensible, so we use more complex strategy
we use different derived class for different types, to facilitate static type checking
we implement operations (stringify, is_equal, quote, evaluate) as functions outside class

this functions are extensible by rules, and the rules are defined in global variable to defer configuration
e.g. we can define eval_quote() based on quote_expr(), then update_quote_rules() later 
  if we were to recreate the rules every time, we have to first define quote_expr() with rules, then define eval_quote() with quote_expr()
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
    SYMBOL = enum.auto()
    STRING = enum.auto()
    NUMBER = enum.auto()
    BOOLEAN = enum.auto()


class Token:
    '''token is simple and relatively fixed, we won't use different classes'''

    def __init__(self, tag: TokenTag, line: int, lexeme: str, literal):
        self.tag = tag
        self.line = line
        self.lexeme = lexeme
        self.literal = literal

    def __str__(self) -> str:
        if self.tag == TokenTag.NUMBER:
            return '%s:%s' % (self.tag.name, format_float(self.literal))
        elif self.tag == TokenTag.STRING or self.tag == TokenTag.SYMBOL:
            return '%s:%s' % (self.tag.name, self.literal)
        elif self.tag == TokenTag.BOOLEAN:
            return '%s:%s' % (self.tag.name, format_bool(self.literal))
        else:
            return self.tag.name


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


_scanner = Scanner()


def scan_source(source: str):
    return _scanner.scan(source)


'''
expression and schemeval
will specified as various classes, and this helps static type checking
if we represent it as single class with different tag (like token), we won't have type checking with python's typing
'''


class Expression:
    pass


'''GenericExpr seem to equivalent to Any, maybe later implementation will fix this'''
GenericExpr = TypeVar('GenericExpr', bound=Expression)


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
define different types of expressions as difference classes for better type checking
conplex syntax are just represented as list, e.g. if, define, begin
see chap 4.1.2

only a few expressions need to store token, to be used to show error location in resolution/runtime error
SymbolExpr need to store the SYMBOL token, because it needs to check if symbol defined or initialized legally
CallExpr need to store the LEFT_PAREN token, because it needs to check parameter arity

according to https://craftinginterpreters.com/appendix-ii.html
DefineVarExpr and DefineProcExpr may store the name SYMBOL token
DefineProcExpr and LambdaExpr may store parameters SYMBOL token
but these tokens are not used in our code
other expressions don't need to store token

we don't store token for every expression, because that prevent us from desugaring
that's because desugaring may create expression from nowhere, so it's difficult to assign token for them
'''


class SymbolExpr(Expression):
    def __init__(self, token: Token):
        self.token = token


class StringExpr(Expression):
    def __init__(self, value: str):
        self.value = value


class NumberExpr(Expression):
    def __init__(self, value: float):
        self.value = value


class BooleanExpr(Expression):
    def __init__(self, value: bool):
        self.value = value


class ListExpr(Expression):
    def __init__(self, tag: str, expressions: List[Expression]):
        '''
        this is the base class for many expressions, it exist to simplify printing
        it will be printed as (tag *expressions):
        tag can be sequence, call, if, ...
        where should exclude the tag
        '''
        self.tag = tag
        self.expressions = expressions


class SequenceExpr(ListExpr):
    '''can be all top-level code, or a begin expression'''

    def __init__(self, expressions: List[Expression]):
        super().__init__("sequence", expressions)


class SchemeParserError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self) -> str:
        return 'parser error at %s in line %d: %s' % (str(self.token), self.token.line+1, self.message)


ParserTokenFuncType = Callable[[Token], Expression]
ParserListFuncType = Callable[[Token, List[Expression]], Expression]


class Parser:
    '''
    scheme parser: tokens -> scheme lists
    very simple recursive descent, see how _parse_quote and _parse_left_paren call _parse_recursive
    ref: https://craftinginterpreters.com/parsing-expressions.html

    expression -> SYMBOL | STRING | NUMBER | quote | list;
    quote -> QUOTE expression;
    list -> LEFT_PAREN ( expression )* RIGHT_PAREN;
    '''

    _token_rules: Dict[TokenTag, ParserTokenFuncType]
    _list_rules: Dict[str, ParserListFuncType]
    _tokens: List[Token]
    _current: int

    def __init__(self):
        self._token_rules = {
            TokenTag.SYMBOL: self._parse_symbol,
            TokenTag.NUMBER: self._parse_number,
            TokenTag.STRING: self._parse_string,
            TokenTag.BOOLEAN: self._parse_boolean,
            TokenTag.QUOTE: self._parse_quote,
            TokenTag.LEFT_PAREN: self._parse_left_paren,
            TokenTag.RIGHT_PAREN: self._parse_right_paren
        }
        self._list_rules = {}
        self._restart([])

    def update_list_rules(self, rules: Dict[str, ParserListFuncType]):
        self._list_rules.update(rules)

    def parse(self, tokens: List[Token]):
        self._restart(tokens)
        expr_list: List[Expression] = []
        try:
            while not self._is_at_end():
                expr = self._parse_recursive()
                expr_list.append(expr)
        except SchemeParserError as err:
            scheme_panic(str(err))
        return SequenceExpr(expr_list)

    def _restart(self, tokens: List[Token]):
        self.tokens = tokens
        self.current = 0

    def _parse_recursive(self) -> Expression:
        token = self._advance()
        return self._token_rules[token.tag](token)

    def _parse_symbol(self, token: Token):
        return SymbolExpr(token)

    def _parse_string(self, token: Token):
        return StringExpr(token.literal)

    def _parse_number(self, token: Token):
        return NumberExpr(token.literal)

    def _parse_boolean(self, token: Token):
        return BooleanExpr(token.literal)

    def _parse_quote(self, token: Token):
        expr_list: List[Expression] = []
        expr_list.append(SymbolExpr(token))
        if self._is_at_end():
            raise SchemeParserError(token, 'quote cannot be at the end')
        expr_list.append(self._parse_recursive())
        return self._parse_list(token, expr_list)

    def _parse_left_paren(self, token: Token):
        expr_list: List[Expression] = []
        while not self._is_at_end() and self._peek().tag != TokenTag.RIGHT_PAREN:
            expr_list.append(self._parse_recursive())
        if self._is_at_end() or self._peek().tag != TokenTag.RIGHT_PAREN:
            raise SchemeParserError(token, 'list missing right parenthesis')
        self._advance()  # consume right parenthesis
        return self._parse_list(token, expr_list)

    def _parse_right_paren(self, token: Token):
        raise SchemeParserError(token, 'unmatched right parenthesis')

    def _parse_list(self, token: Token, expr_list: List[Expression]):
        '''
        token is left paranthesis, it used to shown parser error position of all list-like expressions
        it also show resolution/runtime error position for some list-like expressions
        expr_list are expressions within the paranthesis pair
        '''
        if len(expr_list) == 0:
            return self._list_rules['#nil'](token, expr_list)
        elif type(expr_list[0]) == SymbolExpr:
            symbol_name = cast(SymbolExpr, expr_list[0]).token.literal
            if symbol_name in self._list_rules:
                return self._list_rules[symbol_name](token, expr_list)
        return self._list_rules['#call'](token, expr_list)

    def _is_at_end(self):
        return self.current >= len(self.tokens)

    def _advance(self):
        token = self.tokens[self.current]
        self.current += 1
        return token

    def _peek(self):
        return self.tokens[self.current]


_parser = Parser()


def parse_tokens(tokens: List[Token]):
    return _parser.parse(tokens)


def update_parser_list_rules(rules: Dict[str, ParserListFuncType]):
    _parser.update_list_rules(rules)


'''
list parsing rules
we extract information from list statically
converting list into different kinds of expressions
so no need to parse list at runtime, as in chap 4.1.2
'''


class NilExpr(ListExpr):
    def __init__(self):
        super().__init__('nil', [])


def parse_nil(token: Token, expressions: List[Expression]):
    return NilExpr()


class CallExpr(ListExpr):
    def __init__(self, token: Token, operator: Expression, operands: List[Expression]):
        super().__init__('call', [operator, *operands])
        self.operator = operator
        self.operands = operands


def parse_call(token: Token, expressions: List[Expression]):
    if len(expressions) == 0:
        raise SchemeParserError(token, 'call should not be empty')
    operator_expr = expressions[0]
    operand_exprs = expressions[1:]
    return CallExpr(token, operator_expr, operand_exprs)


class QuoteExpr(ListExpr):
    def __init__(self, content: Expression):
        super().__init__('quote', [content])
        self.content = content


def parse_quote(token: Token, expressions: List[Expression]):
    if len(expressions) != 2:
        raise SchemeParserError(token, 'quote should have 2 expressions, now %d' % len(expressions))
    return QuoteExpr(expressions[1])


class SetExpr(ListExpr):
    def __init__(self, name: SymbolExpr, initializer: Expression):
        super().__init__('set', [name, initializer])
        self.name = name
        self.initializer = initializer


def parse_set(token: Token, expressions: List[Expression]):
    if len(expressions) != 3:
        raise SchemeParserError(
            token, 'set should have 3 expressions, now %d' % len(expressions))
    name_expr = cast(SymbolExpr, expressions[1])
    initializer_expr = expressions[2]
    return SetExpr(name_expr, initializer_expr)


class DefineVarExpr(ListExpr):
    def __init__(self, name: SymbolExpr, initializer: Expression):
        super().__init__('define-var', [name, initializer])
        self.name = name
        self.initializer = initializer


class DefineProcExpr(ListExpr):
    def __init__(self, name: SymbolExpr, parameters: List[SymbolExpr], body: SequenceExpr):
        super().__init__('define-proc', [name, *parameters, body])
        self.name = name
        self.parameters = parameters
        self.body = body


def parse_define(token: Token, expressions: List[Expression]):
    if len(expressions) < 3:
        raise SchemeParserError(
            token, 'define should have at least 3 expressions, now %d' % len(expressions))
    expr1 = expressions[1]
    if isinstance(expr1, SymbolExpr):  # define variable
        name_expr = expr1
        if len(expressions) != 3:
            raise SchemeParserError(
                token, 'define variable should have 3 expressions, now %d' % len(expressions))
        return DefineVarExpr(name_expr, expressions[2])
    elif isinstance(expr1, ListExpr):  # define procedure
        if len(expr1.expressions) == 0:
            raise SchemeParserError(
                token, 'define procedure should provide name')
        expr10 = expr1.expressions[0]
        if isinstance(expr10, SymbolExpr):
            name_expr = expr10
            para_exprs = expr1.expressions[1:]
            body_exprs = SequenceExpr(expressions[2:])
            if all([isinstance(p, SymbolExpr) for p in para_exprs]):
                return DefineProcExpr(name_expr, cast(List[SymbolExpr], para_exprs), body_exprs)
            else:
                raise SchemeParserError(
                    token, 'define procedure should use symbolic parameters')
        else:
            raise SchemeParserError(
                token, 'define procedure should use symbolic name, now %s' % type(expr10).__name__)
    else:
        raise SchemeParserError(
            token, 'define 2nd expression should be symbol or list, now %s' % type(expr1).__name__)


class IfExpr(ListExpr):
    def __init__(self, expr: ListExpr, pred: Expression, then_branch: Expression, else_branch: Optional[Expression]):
        super().__init__(expr.token, expr.expressions)
        self.pred = pred
        self.then_branch = then_branch
        self.else_branch = else_branch


def parse_if(expr: ListExpr):
    if len(expr.expressions) != 3 and len(expr.expressions) != 4:
        raise SchemeParserError(
            expr.token, 'if should have 3 or 4 expressions, now %d' % len(expr.expressions))
    pred_expr = expr.expressions[1]
    then_expr = expr.expressions[2]
    else_expr = None
    if len(expr.expressions) == 4:
        else_expr = expr.expressions[3]
    return IfExpr(expr, pred_expr, then_expr, else_expr)


class BeginExpr(ListExpr):
    def __init__(self, expr: ListExpr, contents: List[Expression]):
        super().__init__(expr.token, expr.expressions)
        self.contents = contents


def parse_begin(expr: ListExpr):
    if len(expr.expressions) < 2:
        raise SchemeParserError(
            expr.token, 'begin should have at least 2 expressions, now %d' % len(expr.expressions))
    return BeginExpr(expr, expr.expressions[1:])


class LambdaExpr(ListExpr):
    def __init__(self, expr: ListExpr, parameters: List[SymbolExpr], body: List[Expression]):
        super().__init__(expr.token, expr.expressions)
        self.parameters = parameters
        self.body = body


def parse_lambda(expr: ListExpr):
    if len(expr.expressions) < 3:
        raise SchemeParserError(
            expr.token, 'lambda should have at least 3 expressions, now %d' % len(expr.expressions))
    expr1 = expr.expressions[1]
    if isinstance(expr1, ListExpr):
        para_exprs = expr1.expressions
        body_exprs = expr.expressions[2:]
        if all([isinstance(p, SymbolExpr) for p in para_exprs]):
            return LambdaExpr(expr, cast(List[SymbolExpr], para_exprs), body_exprs)
        else:
            raise SchemeParserError(
                expr.token, 'lambda should use symbolic parameters')
    else:
        raise SchemeParserError(
            expr.token, 'lambda 2nd expression should be list, now %s' % type(expr1).__name__)


class AndExpr(ListExpr):
    def __init__(self, expr: ListExpr, contents: List[Expression]):
        super().__init__(expr.token, expr.expressions)
        self.contents = contents


def parse_and(expr: ListExpr):
    if len(expr.expressions) < 3:
        raise SchemeParserError(
            expr.token, 'and should have at least 3 expressions, now %d' % len(expr.expressions))
    return AndExpr(expr, expr.expressions[1:])


class OrExpr(ListExpr):
    def __init__(self, expr: ListExpr, contents: List[Expression]):
        super().__init__(expr.token, expr.expressions)
        self.contents = contents


def parse_or(expr: ListExpr):
    if len(expr.expressions) < 3:
        raise SchemeParserError(
            expr.token, 'or should have at least 3 expressions, now %d' % len(expr.expressions))
    return OrExpr(expr, expr.expressions[1:])


class NotExpr(ListExpr):
    def __init__(self, expr: ListExpr, content: Expression):
        super().__init__(expr.token, expr.expressions)
        self.content = content


def parse_not(expr: ListExpr):
    if len(expr.expressions) != 2:
        raise SchemeParserError(
            expr.token, 'not should have 2 expressions, now %d' % len(expr.expressions))
    return NotExpr(expr, expr.expressions[1])


def install_parser_list_rules():
    '''
    we use #nil instead of nil, #call instead of call
    because #nil and #call are both invalid tokens
    this forbids the syntax of (#nill blabla) and (#call blabla)
    '''
    rules = {
        '#nil': parse_nil,
        '#call': parse_call,
        'quote': parse_quote,
        'set!': parse_set,
        'define': parse_define,
        'if': parse_if,
        'begin': parse_begin,
        'lambda': parse_lambda,
        'and': parse_and,
        'or': parse_or,
        'not': parse_not
    }
    update_parser_list_rules(rules)


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
    Callable[[], SchemeVal],
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
    return expr.token.literal


@stringify_expr_rule_decorator
def stringify_expr_string(expr: StringExpr):
    return '"%s"' % expr.token.literal


@stringify_expr_rule_decorator
def stringify_expr_number(expr: NumberExpr):
    return format_float(expr.token.literal)


@stringify_expr_rule_decorator
def stringify_expr_boolean(expr: BooleanExpr):
    return format_bool(expr.token.literal)


@stringify_expr_rule_decorator
def stringify_expr_list(expr: ListExpr):
    substrs = [stringify_expr(subexpr) for subexpr in expr.expressions]
    return '(%s)' % (' '.join(substrs))


@stringify_expr_rule_decorator
def stringify_expr_body(expr: BodyExpr):
    '''very similar to stringify_expr_list, just without outer ()'''
    substrs = [stringify_expr(subexpr) for subexpr in expr.expressions]
    return ' '.join(substrs)


def install_stringify_expr_rules():
    rules = {
        SymbolExpr: stringify_expr_symbol,
        StringExpr: stringify_expr_string,
        NumberExpr: stringify_expr_number,
        BooleanExpr: stringify_expr_boolean,
        ListExpr: stringify_expr_list,
        BodyExpr: stringify_expr_body
    }
    update_stringify_expr_rules(rules)


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
    '''
    A simple implementation of procedure, later we will have another representation
    its string representation inherit ProcVal's
    '''

    def __init__(self, name: str, parameters: List[str], body: List[Expression], env: Environment):
        super().__init__(name, parameters, env)
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


'''
quoter expression to value
'''

QuoteFuncType = Callable[[Expression], SchemeVal]

_quote_rules: Dict[Type, QuoteFuncType] = {}


def update_quote_rules(rules: Dict[Type, QuoteFuncType]):
    _quote_rules.update(rules)


def quote_expr(expr: Expression):
    t = find_type(type(expr), _quote_rules)
    f = _quote_rules[t]
    return f(expr)


QuoteRuleType = Union[
    Callable[[], SchemeVal],
    Callable[[GenericExpr], SchemeVal],
]


def quote_rule_decorator(rule_func: QuoteRuleType):
    arity = len(inspect.getfullargspec(rule_func).args)

    def _quote_rule_wrapped(expr: Expression):
        args: List[Any] = [expr]
        return rule_func(*args[0:arity])
    return _quote_rule_wrapped


@quote_rule_decorator
def quote_symbol(expr: SymbolExpr):
    return SymbolVal(expr.token.literal)


@quote_rule_decorator
def quote_string(expr: StringExpr):
    return StringVal(expr.token.literal)


@quote_rule_decorator
def quote_number(expr: NumberExpr):
    return NumberVal(expr.token.literal)


@quote_rule_decorator
def quote_boolean(expr: BooleanExpr):
    return BooleanVal(expr.token.literal)


@quote_rule_decorator
def quote_list(expr: ListExpr):
    subvals = [quote_expr(subexpr) for subexpr in expr.expressions]
    return pair_from_list(subvals)


def install_quote_rules():
    rules = {
        SymbolExpr: quote_symbol,
        StringExpr: quote_string,
        NumberExpr: quote_number,
        BooleanExpr: quote_boolean,
        ListExpr: quote_list,
    }
    update_quote_rules(rules)


'''evaluator'''


class SchemePrimError(Exception):
    def __init__(self, message):
        self.message = message


class SchemeRuntimeError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self) -> str:
        return 'runtime error at %s in line %d: %s' % (str(self.token), self.token.line+1, self.message)


EvalRecurFuncType = Callable[[Expression, Environment], SchemeVal]
EvalFuncType = Callable[[Expression, Environment, EvalRecurFuncType], SchemeVal]

_eval_rules: Dict[Type, EvalFuncType] = {}


def update_eval_rules(rules: Dict[Type, EvalFuncType]):
    _eval_rules.update(rules)

def evaluate_expr(expr: BodyExpr, env: Environment):
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


def pure_eval_sequence(expr_list: List[Expression], env: Environment, evl: EvalRecurFuncType):
    res: SchemeVal = UndefVal()
    for expr in expr_list:
        res = evl(expr, env)
    return res

@eval_rule_decorator
def eval_contents(expr: Union[BodyExpr, BeginExpr], env: Environment, evl: EvalRecurFuncType):
    '''return the last expression'''
    return pure_eval_sequence(expr.contents, env, evl)


@eval_rule_decorator
def eval_symbol(expr: SymbolExpr, env: Environment):
    try:
        return env_lookup(env, expr.token.literal)
    except SchemeEnvError:
        raise SchemeRuntimeError(expr.token, 'symbol undefined')


@eval_rule_decorator
def eval_string(expr: StringExpr):
    return StringVal(expr.token.literal)


@eval_rule_decorator
def eval_number(expr: NumberExpr):
    return NumberVal(expr.token.literal)


@eval_rule_decorator
def eval_boolean(expr: BooleanExpr):
    return BooleanVal(expr.token.literal)


@eval_rule_decorator
def eval_nil():
    '''evaluating empty list expression () gives empty list value ()'''
    return NilVal()


@eval_rule_decorator
def eval_quote(expr: QuoteExpr):
    return quote_expr(expr.content)


def pure_eval_call_prim(expr: CallExpr, operator: PrimVal, operands: List[SchemeVal]):
    if operator.arity != len(operands):
        raise SchemeRuntimeError(expr.token, '%s expect %d arguments, get %d' % (
            operator.name, operator.arity, len(operands)))
    try:
        return operator.body(*operands)
    except SchemePrimError as err:
        raise SchemeRuntimeError(expr.token, err.message)


def pure_eval_call_proc_plain(expr: CallExpr, operator: ProcPlainVal, operands: List[SchemeVal], evl: EvalRecurFuncType):
    if len(operator.parameters) != len(operands):
        raise SchemeRuntimeError(expr.token, '%s expect %d arguments, get %d' % (
            operator.name, len(operator.parameters), len(operands)))
    new_env = env_extend(operator.env, operator.parameters, operands)
    return pure_eval_sequence(operator.body, new_env, evl)


def pure_eval_call_invalid(expr: CallExpr, operator: SchemeVal):
    raise SchemeRuntimeError(
        expr.token, 'cannot call %s value' % type(operator).__name__)


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


def pure_eval_set(name_expr: SymbolExpr, initializer: SchemeVal, env: Environment):
    try:
        env_set(env, name_expr.token.literal, initializer)
        return initializer
    except SchemeEnvError:
        raise SchemeRuntimeError(name_expr.token, 'symbol undefined')


@eval_rule_decorator
def eval_set(expr: SetExpr, env: Environment, evl: EvalRecurFuncType):
    '''return the value just set'''
    initializer = evl(expr.initializer, env)
    return pure_eval_set(expr.name, initializer, env)


def pure_eval_define_var(name_expr: SymbolExpr, initializer: SchemeVal, env: Environment):
    env_define(env, name_expr.token.literal, initializer)
    return SymbolVal(name_expr.token.literal)


def pure_eval_define_proc_plain(name_expr: SymbolExpr, para_exprs: List[SymbolExpr], body_exprs: List[Expression], env: Environment):
    proc_obj = ProcPlainVal(name_expr.token.literal, [
                            p.token.literal for p in para_exprs], body_exprs, env)
    env_define(env, name_expr.token.literal, proc_obj)
    return SymbolVal(name_expr.token.literal)


@eval_rule_decorator
def eval_define_var(expr: DefineVarExpr, env: Environment, evl: EvalRecurFuncType):
    '''return the symbol defined'''
    initializer = evl(expr.initializer, env)
    return pure_eval_define_var(expr.name, initializer, env)


@eval_rule_decorator
def eval_define_proc(expr: DefineProcExpr, env: Environment):
    '''return the symbol defined'''
    return pure_eval_define_proc_plain(expr.name, expr.parameters, expr.body, env)


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


@eval_rule_decorator
def eval_lambda(expr: LambdaExpr, env: Environment):
    '''return the procedure itself'''
    return ProcPlainVal('lambda', [p.token.literal for p in expr.parameters], expr.body, env)


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
    return BooleanVal(False) if is_truthy(res) else BooleanVal(True)


def install_eval_rules():
    rules = {
        BodyExpr: eval_contents,
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
        BeginExpr: eval_contents,
        LambdaExpr: eval_lambda,
        AndExpr: eval_and,
        OrExpr: eval_or,
        NotExpr: eval_not
    }
    update_eval_rules(rules)


'''primitive definitions'''


def register_primitives(env: Environment, primitives: Dict[str, Callable]):
    '''add a batch of primitives to environment'''
    for name in primitives:
        py_func = primitives[name]
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


def make_primitives():
    return {
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
        'pair?': prim_pair,
        'null?': prim_null,
        'display': prim_display,
        'newline': prim_newline,
    }


'''initialize test'''


def install_rules():
    install_parser_list_rules()
    install_stringify_expr_rules()
    install_stringify_value_rules()
    install_is_equal_rules()
    install_quote_rules()
    install_eval_rules()


def make_global_env():
    glbenv = Environment({})
    primitives = make_primitives()
    register_primitives(glbenv, primitives)
    return glbenv


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
        token_str = ', '.join([str(t) for t in tokens])
        print('* tokens: %s' % token_str)
        if 'tokens' in kargs:
            assert token_str == kargs['tokens']

        # parse
        expr = parse_tokens(tokens)
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


def test_parse():
    test_one(
        '',
        tokens='',
        expression='',
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
        panic='parser error at LEFT_PAREN in line 1: define procedure should use symbolic name, now StringExpr'
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


def test():
    test_scan()
    test_parse()
    test_env()
    test_eval()


if __name__ == '__main__':
    install_rules()
    test()

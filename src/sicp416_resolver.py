'''
the motivation is to solve internal definition
instead of moving all internal definitions to the front of procedure body, setting them to *unassigned*, then check at runtime
we discover some bad internal definitions at compile time, using static analysis, following https://craftinginterpreters.com/resolving-and-binding.html

during the static analysis we also resolve the scope for each symbol, record them as distance, i.e. link_count of environment chain
to use the distance information, we extend environment supports: env_set_at and env_lookup_at
we also modify evaluator to use env_set_at and env_lookup_at, for symbol expression and set! expression

static analysis detects "symbol usage before definition" error, only when usage and definition is in the same local scope
it also detects "symbol redefinition" in the same local scope

if "symbol usage before definition" happens in global scope, or usage and definition are in different scope
we choose not to detect it in static analysis, and we instead detect it at runtime with distance information
this is to allow "symbol used in function body before definition" in all scopes, for example:
(define (f)
  (define a (cons 1 (lambda () a)))
  (car ((cdr a))))
(f)
specifically we allow "mutual recursion" in all scopes, for example:
(define (f)
  (define (even n) (if (= n 0) #t (odd (- n 1))))
  (define (odd n) (if (= n 0) #f (even (- n 1))))
  (even 5))
(f)

besides, we allow "symbol redefinition" in global scope, to facilitate REPL
we do not move definition to front of scope, such as JavaScript's hoisting
'''


import inspect
from typing import Any, Callable, Dict, List, Tuple, Type, Union, cast

# cannot use relative import: from .sicp414_evaluator import blablabla ...
# but can use absolute import below

from sicp414_evaluator import BooleanExpr, BooleanVal, Environment, EvalFuncType, Expression, \
    ListExpr, NilVal, NumberExpr, NumberVal, Parser, SchemeEnvError, SchemePanic, SchemeReparseError, SchemeRuntimeError, \
    Scanner, SchemeVal, StringExpr, StringVal, SymbolExpr, Token, UndefVal, \
    eval_and, eval_begin, eval_call, eval_define, eval_if, eval_lambda, eval_not, eval_or, eval_quote, make_global_env, \
    reparse_and, reparse_begin, reparse_call, reparse_define, reparse_if, reparse_lambda, reparse_not, reparse_or, reparse_set, \
    scheme_flush, scheme_panic, stringify_token, stringify_value


class SchemeResError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self):
        return 'resolution error at %s in line %d: %s' % (stringify_token(self.token), self.token.line+1, self.message)


ResolveFuncType = Callable[[Expression, bool], None]
ResolveStackType = List[Expression]
ResolveBindingsType = Dict[Expression, Dict[str, bool]]
ResolveDistancesType = Dict[SymbolExpr, int]


def resolve_symbol_distance(expr: SymbolExpr, stack: ResolveStackType, bindings: ResolveBindingsType):
    symbol_name: str = expr.token.literal
    for i in range(len(stack)-1, -1, -1):
        scope_expr = stack[i]
        scope_bindings = bindings[scope_expr]
        # in some local scope
        if symbol_name in scope_bindings:
            if scope_bindings[symbol_name] == False and i == len(stack)-1:
                # if usage before initialization and in current local scope, generate error
                raise SchemeResError(
                    expr.token, 'local symbol used before initialization')
            else:
                # either absolutely ok with True, or to be checked at runtime with i < len(stack)-1
                # skip static check to allow "symbol used in function body before definition" and "mutual recursion"
                return len(stack)-1-i
    # if not in any local scope, we assume it's in global scope
    # whether it's indeed in global scope should be checked at runtime
    return len(stack)


class Resolver:
    '''
    resolution need to traverse the scopes
    we notice each scope is associated with an expression, so we store expressions in the _expr_stack
    the scoped bindings for each expression is stored in _expr_bindings
    the final output is the distance for each expression, stored in _distances

    resolution comes in two phases
    the first phase has phase=False, the second has phase=True

    in the first phase, we collect definitions in each local scope
    on entering a local scope, we push the expression to _expr_stack, creating a new scope in _expr_bindings
    within the local scope, we only check definitions and add bindings to _expr_bindings accordingly, setting boolean value to False
    when we see redefinition in local scope, we will trigger ResolutionError

    in the second phase, we check if variables are used only after they are defined in local scope
    on entering a local scope, we still push the expression to _expr_stack
    but instead of creating a new scope in _expr_bindings, we reuse the scope in the first phase, which should all be False
    within the local scope, we still check definitions, and modify the boolean to True
    we also check symbol usage, either calculate distance or trigger error
    if the symbol name is in current or parent local scope, we record its distance
    we further check the value, if True, that's so good, it's used after definition
    but if False, it's used before definition, we trigger SchemeResError if usage and definition are in the same scope, 
    we ignore the problem if they are in different scope, to allow "symbol used in function body before definition" and "mutual recursion"
    such case will be further checked at runtime
    if it's not in any local scope, we assume it's in global scope, we record the distance as link_count to global scope
    this also need to be further checked at runtime
    '''

    _type_rules: Dict[Type, ResolveFuncType]
    _list_rules: Dict[str, Callable[[ListExpr, bool, ResolveFuncType,
                                     ResolveStackType, ResolveBindingsType, ResolveDistancesType], None]]

    _expr_stack: ResolveStackType
    _expr_bindings: ResolveBindingsType
    _distances: ResolveDistancesType

    def __init__(self, list_rules):
        self._type_rules = {
            SymbolExpr: self._resolve_symbol,
            StringExpr: self._resolve_pass,
            NumberExpr: self._resolve_pass,
            BooleanExpr: self._resolve_pass,
            ListExpr: self._resolve_list,
        }
        self._list_rules = list_rules
        self._restart()

    def _restart(self):
        self._expr_stack = []
        self._expr_bindings = {}
        self._distances = {}

    def resolve(self, expr_list: List[Expression]):
        self._restart()
        try:
            for expr in expr_list:
                self._resolve_recursive(expr, False)  # define phase
                self._resolve_recursive(expr, True)  # resolve phase
        except SchemeResError as err:
            scheme_panic(str(err))
        return self._distances

    def _resolve_recursive(self, expr: Expression, phase: bool):
        f = self._type_rules[type(expr)]
        f(expr, phase)

    def _resolve_symbol(self, expr: SymbolExpr, phase: bool):
        if phase:  # only work in phase 2
            self._distances[expr] = resolve_symbol_distance(
                expr, self._expr_stack, self._expr_bindings)

    def _resolve_pass(self, expr: Union[StringExpr, NumberExpr, BooleanExpr], phase: bool):
        pass  # do nothing

    def _resolve_list(self, expr: ListExpr, phase: bool):
        # do the same, no matter which phase; just pass phase down
        if len(expr.expressions) == 0:
            pass
        elif type(expr.expressions[0]) == SymbolExpr:
            symbol_name = cast(SymbolExpr, expr.expressions[0]).token.literal
            if symbol_name in self._list_rules:
                self._resolve_list_rule(symbol_name, expr, phase)
                return
        self._resolve_list_rule('call', expr, phase)

    def _resolve_list_rule(self, rule_name: str, expr: ListExpr, phase: bool):
        try:
            f = self._list_rules[rule_name]
            # we have to pass all internal states to rule function
            # this is ugly, but seems to be the cost of extensibility
            f(expr, phase, self._resolve_recursive,
              self._expr_stack, self._expr_bindings, self._distances)
        except SchemeReparseError as err:
            raise SchemeResError(err.token, err.message)


'''resolution list rule definitions'''

ResolveListRuleFunc = Union[
    Callable[[], None],
    Callable[[ListExpr], None],
    Callable[[ListExpr, bool], None],
    Callable[[ListExpr, bool, ResolveFuncType], None],
    Callable[[ListExpr, bool, ResolveFuncType, ResolveStackType], None],
    Callable[[ListExpr, bool, ResolveFuncType,
              ResolveStackType, ResolveBindingsType], None],
    Callable[[ListExpr, bool, ResolveFuncType, ResolveStackType,
              ResolveBindingsType, ResolveDistancesType], None],
]


def resolve_list_rule_decorator(rule_func: ResolveListRuleFunc):
    arity = len(inspect.getfullargspec(rule_func).args)

    def _resolve_list_rule_wrapped(expr: ListExpr, phase: bool, resolve: ResolveFuncType,
                                   stack: ResolveStackType, bindings: ResolveBindingsType, distances: ResolveDistancesType):
        args: List[Any] = [expr, phase, resolve, stack, bindings, distances]
        rule_func(*args[0:arity])
    return _resolve_list_rule_wrapped


@resolve_list_rule_decorator
def resolve_quote():
    pass


@resolve_list_rule_decorator
def resolve_call(expr: ListExpr, phase: bool, resolve: ResolveFuncType):
    '''
    procedure body is resolved at definition time, not call time
    this is different from evaluator
    '''
    operator_expr, operand_exprs = reparse_call(expr)
    resolve(operator_expr, phase)
    for subexpr in operand_exprs:
        resolve(subexpr, phase)


@resolve_list_rule_decorator
def resolve_set(expr: ListExpr, phase: bool, resolve: ResolveFuncType, stack: ResolveStackType,
                bindings: ResolveBindingsType, distances: ResolveDistancesType):
    '''the distance is on the name_expr, although we could alternatively store it on the list_expr'''
    name_expr, initializer_expr = reparse_set(expr)
    resolve(initializer_expr, phase)
    if phase:  # only work in phase 2
        distances[name_expr] = resolve_symbol_distance(
            name_expr, stack, bindings)


def resolve_symbol_define(expr: SymbolExpr, phase: bool, stack: ResolveStackType, bindings: ResolveBindingsType):
    if len(stack) > 0:  # skip global scope
        scope_expr = stack[-1]  # only cares local scope
        scope_bindings = bindings[scope_expr]
        symbol_name: str = expr.token.literal
        if not phase:  # phase 1 check redefinition
            if symbol_name in scope_bindings:
                raise SchemeResError(expr.token, 'local symbol redefinition')
        scope_bindings[symbol_name] = phase


def resolve_proc_define(proc_expr: ListExpr, para_exprs: List[SymbolExpr], body_exprs: List[Expression], phase: bool,
                        resolve: ResolveFuncType, stack: ResolveStackType, bindings: ResolveBindingsType):
    stack.append(proc_expr)
    if not phase:  # create local scope only in phase 1
        bindings[proc_expr] = {}
    # resolve parameters
    local_scope = bindings[proc_expr]
    for p in para_exprs:
        local_scope[p.token.literal] = phase
    # resolve body recursively
    for b in body_exprs:
        resolve(b, phase)
    stack.pop()


@resolve_list_rule_decorator
def resolve_define(expr: ListExpr, phase: bool, resolve: ResolveFuncType, stack: ResolveStackType, bindings: ResolveBindingsType):
    reparsed = reparse_define(expr)
    if len(reparsed) == 2:  # define variable
        name_expr, initializer_expr = cast(
            Tuple[SymbolExpr, Expression], reparsed)
        resolve(initializer_expr, phase)
        resolve_symbol_define(name_expr, phase, stack, bindings)
    else:  # define procedure
        name_expr, para_exprs, body_exprs = cast(
            Tuple[SymbolExpr, List[SymbolExpr], List[Expression]], reparsed)
        # resolve procedure parameters and body at definition time
        # define procedure name eagerly, so that it can be used inside procedure body
        resolve_symbol_define(name_expr, phase, stack, bindings)
        resolve_proc_define(expr, para_exprs, body_exprs,
                            phase, resolve, stack, bindings)


@resolve_list_rule_decorator
def resolve_if(expr: ListExpr, phase: bool, resolve: ResolveFuncType):
    pred_expr, then_expr, else_expr = reparse_if(expr)
    resolve(pred_expr, phase)
    resolve(then_expr, phase)
    resolve(else_expr, phase)


@resolve_list_rule_decorator
def resolve_begin(expr: ListExpr, phase: bool, resolve: ResolveFuncType):
    subexprs = reparse_begin(expr)
    for subexpr in subexprs:
        resolve(subexpr, phase)


@resolve_list_rule_decorator
def resolve_lambda(expr: ListExpr, phase: bool, resolve: ResolveFuncType, stack: ResolveStackType, bindings: ResolveBindingsType):
    para_exprs, body_exprs = reparse_lambda(expr)
    # resolve procedure parameters and body at definition time
    resolve_proc_define(expr, para_exprs, body_exprs,
                        phase, resolve, stack, bindings)


@resolve_list_rule_decorator
def resolve_and(expr: ListExpr, phase: bool, resolve: ResolveFuncType):
    subexprs = reparse_and(expr)
    for subexpr in subexprs:
        resolve(subexpr, phase)


@resolve_list_rule_decorator
def resolve_or(expr: ListExpr, phase: bool, resolve: ResolveFuncType):
    subexprs = reparse_or(expr)
    for subexpr in subexprs:
        resolve(subexpr, phase)


@resolve_list_rule_decorator
def resolve_not(expr: ListExpr, phase: bool, resolve: ResolveFuncType):
    subexpr = reparse_not(expr)
    resolve(subexpr, phase)


def make_resolver():
    '''make custom resolver, using list rules'''
    list_rules = {
        'quote': resolve_quote,
        'call': resolve_call,
        'set!': resolve_set,
        'define': resolve_define,
        'if': resolve_if,
        'begin': resolve_begin,
        'lambda': resolve_lambda,
        'and': resolve_and,
        'or': resolve_or,
        'not': resolve_not
    }
    resolver = Resolver(list_rules)
    return resolver


'''extending environment to support distance'''


def _env_ancestor(env: Environment, distance: int):
    cur = env
    while distance > 0:
        # we trust the distance provided by resolver
        cur = cast(Environment, cur.enclosing)
        distance -= 1
    return cur


def env_set_at(env: Environment, distance: int, name: str, sv: SchemeVal):
    cur = _env_ancestor(env, distance)
    if name in cur.bindings:
        cur.bindings[name] = sv
    else:
        raise SchemeEnvError(cur)


def env_lookup_at(env: Environment, distance: int, name: str):
    cur = _env_ancestor(env, distance)
    if name in cur.bindings:
        return cur.bindings[name]
    else:
        raise SchemeEnvError(cur)


def pure_resolved_eval_env_error(expr: SymbolExpr, env: Environment):
    message = 'local symbol used before initialization' if env.enclosing else 'global symbol undefined'
    raise SchemeRuntimeError(expr.token, message)


def pure_resolved_eval_symbol(expr: SymbolExpr, env: Environment, distances: ResolveDistancesType):
    try:
        return env_lookup_at(env, distances[expr], expr.token.literal)
    except SchemeEnvError as err:
        pure_resolved_eval_env_error(expr, err.env)


class ResolvedEvaluator:
    '''
    redefined scheme evaluator that takes resolution distance

    only changed a few places:
    add distances parameter to some functions
    and use env_lookup_at in _eval_symbol, to replace env_lookup

    unfortunately have to rewrite the whole class
    '''

    _list_rules: Dict[str, Callable[[ListExpr, Environment,
                                     EvalFuncType, ResolveDistancesType], SchemeVal]]
    _type_rules: Dict[Type, EvalFuncType]
    _distances: ResolveDistancesType

    def __init__(self, list_rules: Dict[str, Callable[[ListExpr, Environment, EvalFuncType, ResolveDistancesType], SchemeVal]]):
        self._list_rules = list_rules
        self._type_rules = {
            SymbolExpr: self._eval_symbol,  # type: ignore
            StringExpr: self._eval_string,  # type: ignore
            NumberExpr: self._eval_number,  # type: ignore
            BooleanExpr: self._eval_boolean,  # type: ignore
            ListExpr: self._eval_list,  # type: ignore
        }
        self._distances = {}

    def evaluate(self, expr_list: List[Expression], env: Environment, distances: ResolveDistancesType) -> SchemeVal:
        self._distances = distances
        try:
            res: SchemeVal = UndefVal()
            for expr in expr_list:
                res = self._eval_recursive(expr, env)
        except SchemeRuntimeError as err:
            scheme_panic(str(err))
        self._distances = {}
        return res

    def _eval_recursive(self, expr: Expression, env: Environment):
        f = self._type_rules[type(expr)]
        return f(expr, env)

    def _eval_symbol(self, expr: SymbolExpr, env: Environment):
        return pure_resolved_eval_symbol(expr, env, self._distances)

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

    def _eval_list_rule(self, rule_name: str, expr: ListExpr, env: Environment):
        try:
            f = self._list_rules[rule_name]
            res = f(expr, env, self._eval_recursive, self._distances)
        except SchemeReparseError as err:
            raise SchemeRuntimeError(err.token, err.message)
        return res


'''resolved evaluator list rule definitions'''

ResolvedEvalListRuleFunc = Union[
    Callable[[ListExpr, Environment, EvalFuncType], SchemeVal],
    Callable[[ListExpr, Environment, EvalFuncType,
              ResolveDistancesType], SchemeVal],
]


def resolved_eval_list_rule_decorator(rule_func: ResolvedEvalListRuleFunc):
    arity = len(inspect.getfullargspec(rule_func).args)

    def _resolved_eval_list_rule_wrapped(expr: ListExpr, env: Environment, evl: EvalFuncType, distances: ResolveDistancesType):
        args: List[Any] = [expr, env, evl, distances]
        return rule_func(*args[0:arity])
    return _resolved_eval_list_rule_wrapped


resolved_eval_quote = resolved_eval_list_rule_decorator(eval_quote)
resolved_eval_call = resolved_eval_list_rule_decorator(eval_call)
resolved_eval_define = resolved_eval_list_rule_decorator(eval_define)
resolved_eval_if = resolved_eval_list_rule_decorator(eval_if)
resolved_eval_begin = resolved_eval_list_rule_decorator(eval_begin)
resolved_eval_lambda = resolved_eval_list_rule_decorator(eval_lambda)
resolved_eval_and = resolved_eval_list_rule_decorator(eval_and)
resolved_eval_or = resolved_eval_list_rule_decorator(eval_or)
resolved_eval_not = resolved_eval_list_rule_decorator(eval_not)


def pure_resolved_eval_set(name_expr: SymbolExpr, initializer: SchemeVal, env: Environment, distances: ResolveDistancesType):
    try:
        env_set_at(env, distances[name_expr],
                   name_expr.token.literal, initializer)
        return initializer
    except SchemeEnvError as err:
        pure_resolved_eval_env_error(name_expr, err.env)


@resolved_eval_list_rule_decorator
def resolved_eval_set(expr: ListExpr, env: Environment, eval: EvalFuncType, distances: ResolveDistancesType):
    '''return the value just set'''
    name_expr, initializer_expr = reparse_set(expr)
    initializer = eval(initializer_expr, env)
    return pure_resolved_eval_set(name_expr, initializer, env, distances)


def make_resolved_evaluator():
    '''make custom resolved evaluator, using list rules'''
    list_rules = {
        'quote': resolved_eval_quote,
        'call': resolved_eval_call,
        'set!': resolved_eval_set,
        'define': resolved_eval_define,
        'if': resolved_eval_if,
        'begin': resolved_eval_begin,
        'lambda': resolved_eval_lambda,
        'and': resolved_eval_and,
        'or': resolved_eval_or,
        'not': resolved_eval_not
    }
    evaluator = ResolvedEvaluator(list_rules)
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

        # parse
        parser = Parser()
        expr_list = parser.parse(tokens)

        # resolve
        resolver = make_resolver()
        distances = resolver.resolve(expr_list)
        resolve_str = ' '.join(
            ['(%d:%s %d)' % (expr.token.line+1, expr.token.literal, distances[expr]) for expr in distances])
        if len(resolve_str):
            print('* resolve: %s' % resolve_str)
        if 'resolve' in kargs:
            assert resolve_str == kargs['resolve']

        # evaluate
        glbenv = make_global_env()
        evaluator = make_resolved_evaluator()
        result = evaluator.evaluate(expr_list, glbenv, distances)
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


def test():
    # use before intialization in the same scope forbidden
    test_one(
        '''
        (define x 1)
        (define (f)
          (define y x)
          (define x 2)
          y)
        (f)
        ''',
        panic='resolution error at SYMBOL:x in line 3: local symbol used before initialization'
    )
    # use before intialization in different scopes pass resolution
    test_one(
        '''
        (define (f)
          (define a (cons 1 (lambda () a)))
          (car ((cdr a))))
        (f)
        ''',
        resolve='(2:cons 1) (2:a 1) (3:car 1) (3:cdr 1) (3:a 0) (4:f 0)',
        result='1'
    )
    # use before intialization in different scopes pass resolution
    test_one(
        '''
        (define (f)
          (define (g) x)
          (define x 1)
          (g))
        (f)
        ''',
        resolve='(2:x 1) (4:g 0) (5:f 0)',
        result='1'
    )
    # use before intialization in different scopes fail at runtime
    test_one(
        '''
        (define (f)
          (define (g) x)
          (g)
          (define x 1))
        (f)
        ''',
        panic='runtime error at SYMBOL:x in line 2: local symbol used before initialization'
    )
    # self initialization forbidden
    test_one(
        '''
        (define x 1)
        (define (f)
          (define x x)
          x)
        (f)
        ''',
        panic='resolution error at SYMBOL:x in line 3: local symbol used before initialization'
    )
    # undefined global variable pass resolution
    test_one(
        '''
        (define x 1)
        (+ x x)
        (f)
        ''',
        resolve='(2:+ 0) (2:x 0) (2:x 0) (3:f 0)',
        panic='runtime error at SYMBOL:f in line 3: global symbol undefined'
    )
    # local redefinition forbidden
    test_one(
        '''
        (define (f)
          (define x 1)
          (define x 2)
          x)
        (f)
        ''',
        panic='resolution error at SYMBOL:x in line 3: local symbol redefinition'
    )
    # global redefinition ok
    test_one(
        '''
        (define x 1)
        (define x 2)
        x
        ''',
        resolve='(3:x 0)',
        result='2'
    )
    # local variable shadows outer definitions
    test_one(
        '''
        (define x 1)
        (define (f)
          (define x 2)
          x)
        (f)
        ''',
        resolve='(4:x 0) (5:f 0)',
        result='2'
    )
    # two level scopes, lambda and set
    test_one(
        '''
        (define x 1)
        (define (f)
          (define y 2)
          (lambda ()
            (define z 4)
            (set! x 8)
            (+ x (+ y z))))
        ((f))
        ''',
        resolve='(6:x 2) (7:+ 2) (7:x 2) (7:+ 2) (7:y 1) (7:z 0) (8:f 0)',
        result='14'
    )
    # if, begin and set
    test_one(
        '''
        (define x 1)
        (define (f)
          (if (= x 1) (begin (set! x 2) x) (x)))
        (f)
        ''',
        resolve='(3:= 1) (3:x 1) (3:x 1) (3:x 1) (3:x 1) (4:f 0)',
        result='2'
    )
    # single recursion ok, due to eager procedure definition
    test_one(
        '''
        (define (run)
          (define (factorial n)
            (if (= n 1)
              1
              (* n (factorial (- n 1)))))
          (factorial 5))
        (run)
        ''',
        resolve='(3:= 2) (3:n 0) (5:* 2) (5:n 0) (5:factorial 1) (5:- 2) (5:n 0) (6:factorial 0) (7:run 0)',
        result='120'
    )
    # mutual recursion ok, even in local scope
    test_one(
        '''
        (define (f)
          (define (even n) (if (= n 0) #t (odd (- n 1))))
          (define (odd n) (if (= n 0) #f (even (- n 1))))
          (even 5))
        (f)
        ''',
        result='#f'
    )
    # half mutual recursion error detected at runtime
    test_one(
        '''
        (define (f)
          (define (even n) (if (= n 0) #t (odd (- n 1))))
          (even 5))
        (f)
        ''',
        panic='runtime error at SYMBOL:odd in line 2: global symbol undefined'
    )


if __name__ == '__main__':
    test()

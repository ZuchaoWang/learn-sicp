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
from typing import Any, Callable, Dict, List, Type, Union, cast

# cannot use relative import: from .sicp414_evaluator import blablabla ...
# but can use absolute import below

from sicp414_evaluator import AndExpr, SequenceExpr, BooleanExpr, CallExpr, DefineProcExpr, DefineVarExpr, Environment, \
    EvalRecurFuncType, Expression, GenericExpr, IfExpr, LambdaExpr, ListExpr, NilExpr, NotExpr, NumberExpr, OrExpr, QuoteExpr, \
    SchemeEnvError, SchemePanic, SchemeRuntimeError, SchemeVal, SetExpr, StringExpr, SymbolExpr, Token, \
    eval_and, eval_boolean, eval_call, eval_sequence, eval_define_proc, eval_define_var, eval_if, \
    eval_lambda, eval_nil, eval_not, eval_number, eval_or, eval_quote, eval_string, find_type, \
    install_is_equal_rules, install_parser_rules, install_primitives, install_quote_rules, install_stringify_expr_rules, \
    install_stringify_value_rules, make_global_env, parse_tokens, scan_source, scheme_flush, scheme_panic, stringify_value


class SchemeResError(Exception):
    def __init__(self, token: Token, message: str):
        self.token = token
        self.message = message

    def __str__(self):
        return 'resolution error at %s in line %d: %s' % (str(self.token), self.token.line+1, self.message)


ResStackType = List[Expression]
ResBindingsType = Dict[Expression, Dict[str, bool]]
ResDistancesType = Dict[Union[SymbolExpr, SetExpr], int]
ResRecurFuncType = Callable[[Expression, bool], None]
ResFuncType = Callable[[Expression, bool, ResRecurFuncType, ResStackType,
                        ResBindingsType, ResDistancesType], None]


_resolver_rules: Dict[Type, ResFuncType] = {}


def update_resolver_rules(rules: Dict[Type, ResFuncType]):
    _resolver_rules.update(rules)


def resolve_expr(expr: SequenceExpr):
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
    expr_stack: ResStackType = []
    expr_bindings: ResBindingsType = {}
    distances: ResDistancesType = {}

    def resolve_recursive(expr: Expression, phase: bool):
        '''
        nested definition saves the mess to pass down expr_stack, expr_bindings, distances
        it also makes the function type irrelavant to the 3 state parameters
        '''
        t = find_type(type(expr), _resolver_rules)
        f = _resolver_rules[t]
        f(expr, phase, resolve_recursive, expr_stack, expr_bindings, distances)

    try:
        resolve_recursive(expr, False)  # define phase
        resolve_recursive(expr, True)  # resolve phase
    except SchemeResError as err:
        scheme_panic(str(err))
    return distances


'''resolution rule definitions'''

ResolverRuleType = Union[
    Callable[[], None],
    Callable[[GenericExpr], None],
    Callable[[GenericExpr, bool], None],
    Callable[[GenericExpr, bool, ResRecurFuncType], None],
    Callable[[GenericExpr, bool, ResRecurFuncType, ResStackType], None],
    Callable[[GenericExpr, bool, ResRecurFuncType,
              ResStackType, ResBindingsType], None],
    Callable[[GenericExpr, bool, ResRecurFuncType, ResStackType,
              ResBindingsType, ResDistancesType], None],
]


def resolver_rule_decorator(rule_func: ResolverRuleType):
    arity = len(inspect.getfullargspec(rule_func).args)

    def _resolver_rule_wrapped(expr: Expression, phase: bool, resolve: ResRecurFuncType,
                               stack: ResStackType, bindings: ResBindingsType, distances: ResDistancesType):
        args: List[Any] = [expr, phase, resolve, stack, bindings, distances]
        rule_func(*args[0:arity])
    return _resolver_rule_wrapped


def resolve_symbol_distance(name: Token, stack: ResStackType, bindings: ResBindingsType):
    for i in range(len(stack)-1, -1, -1):
        scope_expr = stack[i]
        scope_bindings = bindings[scope_expr]
        # in some local scope
        if name.literal in scope_bindings:
            if scope_bindings[name.literal] == False and i == len(stack)-1:
                # if usage before initialization and in current local scope, generate error
                raise SchemeResError(
                    name, 'local symbol used before initialization')
            else:
                # either absolutely ok with True, or to be checked at runtime with i < len(stack)-1
                # skip static check to allow "symbol used in function body before definition" and "mutual recursion"
                return len(stack)-1-i
    # if not in any local scope, we assume it's in global scope
    # whether it's indeed in global scope should be checked at runtime
    return len(stack)


@resolver_rule_decorator
def resolve_symbol(expr: SymbolExpr, phase: bool, resolve: ResRecurFuncType, stack: ResStackType,
                   bindings: ResBindingsType, distances: ResDistancesType):
    if phase:  # only work in phase 2
        distances[expr] = resolve_symbol_distance(expr.name, stack, bindings)


@resolver_rule_decorator
def resolve_pass():
    pass  # do nothing


@resolver_rule_decorator
def resolve_contents(expr: Union[SequenceExpr, AndExpr, OrExpr], phase: bool, resolve: ResRecurFuncType):
    for subexpr in expr.contents:
        resolve(subexpr, phase)


@resolver_rule_decorator
def resolve_call(expr: CallExpr, phase: bool, resolve: ResRecurFuncType):
    '''
    procedure body is resolved at definition time, not call time
    this is different from evaluator
    '''
    resolve(expr.operator, phase)
    for subexpr in expr.operands:
        resolve(subexpr, phase)


@resolver_rule_decorator
def resolve_set(expr: SetExpr, phase: bool, resolve: ResRecurFuncType, stack: ResStackType,
                bindings: ResBindingsType, distances: ResDistancesType):
    '''the distance is on the name_expr, although we could alternatively store it on the list_expr'''
    resolve(expr.initializer, phase)
    if phase:  # only work in phase 2
        distances[expr] = resolve_symbol_distance(
            expr.name, stack, bindings)


def resolve_define_symbol_name(name: Token, phase: bool, resolve: ResRecurFuncType,
                               stack: ResStackType, bindings: ResBindingsType):
    if len(stack) > 0:  # skip global scope
        scope_expr = stack[-1]  # only cares local scope
        scope_bindings = bindings[scope_expr]
        if not phase:  # phase 1 check redefinition
            if name.literal in scope_bindings:
                raise SchemeResError(name, 'local symbol redefinition')
        scope_bindings[name.literal] = phase


@resolver_rule_decorator
def resolve_define_var(expr: DefineVarExpr, phase: bool, resolve: ResRecurFuncType, stack: ResStackType, bindings: ResBindingsType):
    resolve(expr.initializer, phase)
    resolve_define_symbol_name(expr.name, phase, resolve, stack, bindings)


def resolve_define_proc_value(expr: Union[DefineProcExpr, LambdaExpr], phase: bool, resolve: ResRecurFuncType,
                              stack: ResStackType, bindings: ResBindingsType):
    stack.append(expr)
    if not phase:  # create local scope only in phase 1
        bindings[expr] = {}
    # resolve parameters
    local_scope = bindings[expr]
    for p in expr.parameters:
        local_scope[p.literal] = phase
    # resolve body recursively
    resolve(expr.body, phase)
    stack.pop()


@resolver_rule_decorator
def resolve_define_proc(expr: DefineProcExpr, phase: bool, resolve: ResRecurFuncType, stack: ResStackType, bindings: ResBindingsType):
    # resolve procedure parameters and body at definition time
    # define procedure name eagerly, so that it can be used inside procedure body
    resolve_define_symbol_name(expr.name, phase, resolve, stack, bindings)
    resolve_define_proc_value(expr, phase, resolve, stack, bindings)


@resolver_rule_decorator
def resolve_if(expr: IfExpr, phase: bool, resolve: ResRecurFuncType):
    resolve(expr.pred, phase)
    resolve(expr.then_branch, phase)
    if expr.else_branch is not None:
        resolve(expr.else_branch, phase)


@resolver_rule_decorator
def resolve_lambda(expr: LambdaExpr, phase: bool, resolve: ResRecurFuncType, stack: ResStackType, bindings: ResBindingsType):
    # resolve procedure parameters and body at definition time
    resolve_define_proc_value(expr, phase, resolve, stack, bindings)


@resolver_rule_decorator
def resolve_not(expr: NotExpr, phase: bool, resolve: ResRecurFuncType):
    resolve(expr.content, phase)


def install_resolver_rules():
    rules = {
        SequenceExpr: resolve_contents,
        SymbolExpr: resolve_symbol,
        StringExpr: resolve_pass,
        NumberExpr: resolve_pass,
        BooleanExpr: resolve_pass,
        NilExpr: resolve_pass,
        QuoteExpr: resolve_pass,
        CallExpr: resolve_call,
        SetExpr: resolve_set,
        DefineVarExpr: resolve_define_var,
        DefineProcExpr: resolve_define_proc,
        IfExpr: resolve_if,
        LambdaExpr: resolve_lambda,
        AndExpr: resolve_contents,
        OrExpr: resolve_contents,
        NotExpr: resolve_not
    }
    update_resolver_rules(rules)


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


'''resolved evaluator'''


ResolvedEvalFuncType = Callable[[
    Expression, Environment, EvalRecurFuncType, ResDistancesType], SchemeVal]

_resolved_eval_rules: Dict[Type, ResolvedEvalFuncType] = {}


def update_resolved_eval_rules(rules: Dict[Type, ResolvedEvalFuncType]):
    _resolved_eval_rules.update(rules)


def resolved_evaluate_expr(expr: SequenceExpr, env: Environment, distances: ResDistancesType):
    '''similar to evaluator, just need to use distances information'''
    def resolved_evaluate_recursive(expr: Expression, env: Environment):
        t = find_type(type(expr), _resolved_eval_rules)
        f = _resolved_eval_rules[t]
        return f(expr, env, resolved_evaluate_recursive, distances)

    try:
        res = resolved_evaluate_recursive(expr, env)
    except SchemeRuntimeError as err:
        scheme_panic(str(err))
    return res


'''
resovled evaluator rule definitions
'''

ResolvedEvalRuleType = Union[
    Callable[[], SchemeVal],
    Callable[[GenericExpr], SchemeVal],
    Callable[[GenericExpr, Environment], SchemeVal],
    Callable[[GenericExpr, Environment, EvalRecurFuncType], SchemeVal],
    Callable[[GenericExpr, Environment, EvalRecurFuncType,
              ResDistancesType], SchemeVal],
]


def resolved_eval_rule_decorator(rule_func: ResolvedEvalRuleType):
    arity = len(inspect.getfullargspec(rule_func).args)

    def _resolved_eval_list_rule_wrapped(expr: ListExpr, env: Environment, evl: EvalRecurFuncType, distances: ResDistancesType):
        args: List[Any] = [expr, env, evl, distances]
        return rule_func(*args[0:arity])
    return _resolved_eval_list_rule_wrapped


def pure_resolved_eval_env_error(name: Token, env: Environment):
    message = 'local symbol used before initialization' if env.enclosing else 'global symbol undefined'
    raise SchemeRuntimeError(name, message)


def pure_resolved_eval_symbol(expr: SymbolExpr, env: Environment, distances: ResDistancesType):
    try:
        return env_lookup_at(env, distances[expr], expr.name.literal)
    except SchemeEnvError as err:
        pure_resolved_eval_env_error(expr.name, err.env)


@resolved_eval_rule_decorator
def resolved_eval_symbol(expr: SymbolExpr, env: Environment, evl: EvalRecurFuncType, distances: ResDistancesType):
    return pure_resolved_eval_symbol(expr, env, distances)


def pure_resolved_eval_set(expr: SetExpr, initializer: SchemeVal, env: Environment, distances: ResDistancesType):
    try:
        env_set_at(env, distances[expr],
                   expr.name.literal, initializer)
        return initializer
    except SchemeEnvError as err:
        pure_resolved_eval_env_error(expr.name, err.env)


@resolved_eval_rule_decorator
def resolved_eval_set(expr: SetExpr, env: Environment, evl: EvalRecurFuncType, distances: ResDistancesType):
    '''return the value just set'''
    initializer = evl(expr.initializer, env)
    return pure_resolved_eval_set(expr, initializer, env, distances)


resolved_eval_sequence = resolved_eval_rule_decorator(eval_sequence)
resolved_eval_string = resolved_eval_rule_decorator(eval_string)
resolved_eval_number = resolved_eval_rule_decorator(eval_number)
resolved_eval_boolean = resolved_eval_rule_decorator(eval_boolean)
resolved_eval_nil = resolved_eval_rule_decorator(eval_nil)
resolved_eval_quote = resolved_eval_rule_decorator(eval_quote)
resolved_eval_call = resolved_eval_rule_decorator(eval_call)
resolved_eval_define_var = resolved_eval_rule_decorator(eval_define_var)
resolved_eval_define_proc = resolved_eval_rule_decorator(eval_define_proc)
resolved_eval_if = resolved_eval_rule_decorator(eval_if)
resolved_eval_lambda = resolved_eval_rule_decorator(eval_lambda)
resolved_eval_and = resolved_eval_rule_decorator(eval_and)
resolved_eval_or = resolved_eval_rule_decorator(eval_or)
resolved_eval_not = resolved_eval_rule_decorator(eval_not)


def install_resolved_eval_rules():
    rules = {
        SequenceExpr: resolved_eval_sequence,
        SymbolExpr: resolved_eval_symbol,
        StringExpr: resolved_eval_string,
        NumberExpr: resolved_eval_number,
        BooleanExpr: resolved_eval_boolean,
        NilExpr: resolved_eval_nil,
        QuoteExpr: resolved_eval_quote,
        CallExpr: resolved_eval_call,
        SetExpr: resolved_eval_set,
        DefineVarExpr: resolved_eval_define_var,
        DefineProcExpr: resolved_eval_define_proc,
        IfExpr: resolved_eval_if,
        LambdaExpr: resolved_eval_lambda,
        AndExpr: resolved_eval_and,
        OrExpr: resolved_eval_or,
        NotExpr: resolved_eval_not
    }
    update_resolved_eval_rules(rules)


def install_rules():
    install_parser_rules()
    install_stringify_expr_rules()
    install_stringify_value_rules()
    install_is_equal_rules()
    install_quote_rules()
    install_resolver_rules()
    install_resolved_eval_rules()
    install_primitives()


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

        # parse
        expr = parse_tokens(tokens)

        # resolve
        distances = resolve_expr(expr)
        resolve_str = ' '.join(
            ['(%d:%s %d)' % (expr.name.line+1, expr.name.literal, distances[expr]) for expr in distances])
        if len(resolve_str):
            print('* resolve: %s' % resolve_str)
        if 'resolve' in kargs:
            assert resolve_str == kargs['resolve']

        # evaluate
        glbenv = make_global_env()
        result = resolved_evaluate_expr(expr, glbenv, distances)
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
    install_rules()
    test()

'''
explicit control evaluator
build a machine that can evaluate any scheme program
we skip the parsing part, instead we reuse parser in sicp414_evaluator to generate expressions
we feed our machine with expressions and resolved distances

we allocate a special register "dist" to hold resolved distances
this register will stay constant after initialization
we also have two more temporary registers "unev2" and "unev3"
mainly because we use python list instead of scheme linked list
and traversing the python list need more local variables

our ec evalutor is written in machine language code, see ec_eval_code
we also skip parsing, so our code is written in instruction structures
we lack the mechanism to write the evaluator in a modular way in machine language
unless we generate the code using python, but that will make the code hard to read

we use a lot of high level operations, making it less similar to assembly
we should consider them as specialized hardware
but some are just selector, which we may just use python getattr
for environment related operations, we tend to use simple ones like env_set, instead of pure_eval_set
this is to be consistent with our compiler, which should not use any operation involving expression

error reporting is achieved by special return value
for those operations that can fail, instead of purely returning result, we return pair(error, result)
then we extract "error" via car, test/branch on it
to print error message, we need token to get its position in source code
we acquire the token from the expression itself using get_var_name_token and get_paren_token
then we concatenate token and "error", put it in a special register err, and goto error-handler label
notice we only use "err" register to store final concatenated error message as input to error-handler
we don't store intermediate un-tokened message here, nor any other information

in recursion test, factorial iteration use constant max stack depth (16)
this shows our tail recursion support is correctly implemented
to support that we need to ensure the last operation in procedure/primitive call is recursive expression evaluation
no more restore or assignment should come after that

from the result we can see running a factorial using ec evaluator needs 100x more instructions
than handcrafted machine in sicp524_monitor, excessive work includes:
operator and every operands is a expression, requiring evaluation; in sicp524_monitor they are just constant;
all operands need to form a list and put into argl; in sicp524_monitor they are fed directly;
stack operations, error checking for arity and primitive also consumes lots of instructions
'''

from typing import Callable, List, Tuple, Union
from sicp414_evaluator import AndExpr, BooleanVal, CallExpr, DefineProcExpr, DefineVarExpr, Environment, \
    GenericExpr, GenericVal, IfExpr, NotExpr, NumberVal, OrExpr, PairVal, PrimVal, ProcPlainVal, ProcVal, \
    SchemeEnvError, SchemePanic, SchemePrimError, SchemeRuntimeError, SchemeVal, SequenceExpr, SetExpr, \
    StringVal, SymbolExpr, SymbolVal, Token, UndefVal, env_define, env_extend, install_is_equal_rules, \
    install_parse_expr_rules, install_primitives, install_stringify_expr_rules, install_stringify_value_rules, \
    is_truthy, make_global_env, parse_expr, parse_tokens, pure_eval_boolean, pure_eval_define_proc_plain_value, \
    pure_eval_define_var, pure_eval_lambda_plain, pure_eval_nil, pure_eval_number, pure_eval_quote, pure_eval_string, \
    pure_get_proc_arguments, pure_get_proc_parameters, scan_source, scheme_flush, scheme_panic, stringify_value
from sicp416_resolver import ResDistancesType, env_lookup_at, env_set_at, install_resolver_rules, resolve_expr
from sicp523_simulator import AssignMstmt, BranchMstmt, ConstMxpr, GotoMstmt, LabelMstmt, LabelMxpr, OpMxpr, \
    PerformMstmt, RegMxpr, RestoreMstmt, SaveMstmt, TestMstmt, get_operations, init_machine_pc, \
    install_assemble_mstmt_rules, install_assemble_mxpr_rules, install_operations, \
    make_machine, make_run_machine, update_operations
from sicp524_monitor import MachineStatistic, monitor_statistics

# fmt: off
ec_eval_code = [
  LabelMstmt('main'),
    AssignMstmt('continue', LabelMxpr('done')),

  LabelMstmt('eval-dispatch'),
    # unev stores the type name of expr
    AssignMstmt('unev', OpMxpr('get_expr_type', [RegMxpr('expr')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('SequenceExpr'))])),
    BranchMstmt(LabelMxpr('ev-sequence')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('SymbolExpr'))])),
    BranchMstmt(LabelMxpr('ev-symbol')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('StringExpr'))])),
    BranchMstmt(LabelMxpr('ev-string')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('NumberExpr'))])),
    BranchMstmt(LabelMxpr('ev-number')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('BooleanExpr'))])),
    BranchMstmt(LabelMxpr('ev-boolean')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('NilExpr'))])),
    BranchMstmt(LabelMxpr('ev-nil')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('QuoteExpr'))])),
    BranchMstmt(LabelMxpr('ev-quote')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('LambdaExpr'))])),
    BranchMstmt(LabelMxpr('ev-lambda')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('CallExpr'))])),
    BranchMstmt(LabelMxpr('ev-call')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('IfExpr'))])),
    BranchMstmt(LabelMxpr('ev-if')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('SetExpr'))])),
    BranchMstmt(LabelMxpr('ev-set')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('DefineVarExpr'))])),
    BranchMstmt(LabelMxpr('ev-define-var')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('DefineProcExpr'))])),
    BranchMstmt(LabelMxpr('ev-define-proc')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('AndExpr'))])),
    BranchMstmt(LabelMxpr('ev-and')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('OrExpr'))])),
    BranchMstmt(LabelMxpr('ev-or')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('NotExpr'))])),
    BranchMstmt(LabelMxpr('ev-not')),
    # put expression type in err, then goto error
    AssignMstmt('err', OpMxpr('ec_eval_expr_invalid', [RegMxpr('unev')])),
    GotoMstmt(LabelMxpr('error-handler')),

  LabelMstmt('ev-string'),
    AssignMstmt('val', OpMxpr('pure_eval_string', [RegMxpr('expr')])),
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-number'),
    AssignMstmt('val', OpMxpr('pure_eval_number', [RegMxpr('expr')])),
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-boolean'),
    AssignMstmt('val', OpMxpr('pure_eval_boolean', [RegMxpr('expr')])),
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-nil'),
    AssignMstmt('val', OpMxpr('pure_eval_nil', [])),
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-quote'),
    AssignMstmt('val', OpMxpr('pure_eval_quote', [RegMxpr('expr')])),
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-lambda'),
    AssignMstmt('val', OpMxpr('pure_eval_lambda_plain', [RegMxpr('expr'), RegMxpr('env')])),
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-symbol'),
    AssignMstmt('unev', OpMxpr('get_var_name', [RegMxpr('expr')])),
    # unev2 = distance
    AssignMstmt('unev2', OpMxpr('get_distance', [RegMxpr('dist'), RegMxpr('expr')])),
    # val = pair(error, result)
    AssignMstmt('val', OpMxpr('ec_env_lookup_at', [RegMxpr('env'), RegMxpr('unev2'), RegMxpr('unev')])),
    # unev = error
    AssignMstmt('unev', OpMxpr('car', [RegMxpr('val')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(UndefVal())])),
    BranchMstmt(LabelMxpr('ev-symbol-no-error')),
    # has error, first val = token, then val = concatenated_message
    AssignMstmt('val', OpMxpr('get_var_name_token', [RegMxpr('expr')])),
    AssignMstmt('err', OpMxpr('concat_token_message', [RegMxpr('val'), RegMxpr('unev')])),
    GotoMstmt(LabelMxpr('error-handler')),
  LabelMstmt('ev-symbol-no-error'),
    # val = result
    AssignMstmt('val', OpMxpr('cdr', [RegMxpr('val')])),
    GotoMstmt(RegMxpr('continue')),

    # we need three registers for contents, n=len(contents), i
    # we use unev, unev2, unev3
  LabelMstmt('ev-sequence'),
    AssignMstmt('unev', OpMxpr('get_expr_contents', [RegMxpr('expr')])),
    AssignMstmt('unev2', OpMxpr('get_exprs_len', [RegMxpr('unev')])),
    TestMstmt(OpMxpr('>', [RegMxpr('unev2'), ConstMxpr(NumberVal(0))])),
    BranchMstmt(LabelMxpr('ev-sequence-non-empty')),
    GotoMstmt(RegMxpr('continue')),
  LabelMstmt('ev-sequence-non-empty'),
    SaveMstmt('continue'),
    # now unev2 = len-1
    AssignMstmt('unev2', OpMxpr('-', [RegMxpr('unev2'), ConstMxpr(NumberVal(1))])),
    # init unev3 = 0
    AssignMstmt('unev3', ConstMxpr(NumberVal(0))),
  LabelMstmt('ev-sequence-fronts'),
    TestMstmt(OpMxpr('=', [RegMxpr('unev3'), RegMxpr('unev2')])),
    BranchMstmt(LabelMxpr('ev-sequence-last')),
    SaveMstmt('unev'),
    SaveMstmt('unev2'),
    SaveMstmt('unev3'),
    SaveMstmt('env'),
    AssignMstmt('expr', OpMxpr('get_expr_at', [RegMxpr('unev'), RegMxpr('unev3')])),
    AssignMstmt('continue', LabelMxpr('ev-sequence-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-sequence-ret'),
    RestoreMstmt('env'),
    RestoreMstmt('unev3'),
    RestoreMstmt('unev2'),
    RestoreMstmt('unev'),
    AssignMstmt('unev3', OpMxpr('+', [RegMxpr('unev3'), ConstMxpr(NumberVal(1))])),
    GotoMstmt(LabelMxpr('ev-sequence-fronts')),
    # support for tail recursion: ensure goto eval-dispatch is the last instruction
    # to do that, can't save/restore for env/unev/unev2/unev3
    # and should restore continue before call rather than after
  LabelMstmt('ev-sequence-last'),
    AssignMstmt('expr', OpMxpr('get_expr_at', [RegMxpr('unev'), RegMxpr('unev3')])),
    RestoreMstmt('continue'),
    GotoMstmt(LabelMxpr('eval-dispatch')),

  LabelMstmt('ev-call'),
    SaveMstmt('continue'),
    SaveMstmt('expr'),
    SaveMstmt('env'),
    AssignMstmt('unev', OpMxpr('get_call_operands', [RegMxpr('expr')])),
    SaveMstmt('unev'),
    # getting operator
    AssignMstmt('expr', OpMxpr('get_call_operator', [RegMxpr('expr')])),
    AssignMstmt('continue', LabelMxpr('ev-call-operands')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-call-operands'),
    # getting operands
    # we still do save/restore for the last operand
    # this has a little performance lost, but do not destroy tail recursion
    AssignMstmt('proc', RegMxpr('val')),
    # each time we must create a new empty list
    # therefore we must call op init_val_list
    # we cannot assign from a const [], otherwise that [] will be mutated and reused
    # an alternative solution is to not mutate to [], instead every append create a new one
    AssignMstmt('argl', OpMxpr('init_val_list', [])),
    RestoreMstmt('unev'),
    RestoreMstmt('env'),
    AssignMstmt('unev2', OpMxpr('get_exprs_len', [RegMxpr('unev')])),
    AssignMstmt('unev3', ConstMxpr(NumberVal(0))),
    SaveMstmt('proc'),
  LabelMstmt('ev-call-operand-start'),
    TestMstmt(OpMxpr('=', [RegMxpr('unev3'), RegMxpr('unev2')])),
    BranchMstmt(LabelMxpr('ev-call-call')),
    SaveMstmt('env'),
    SaveMstmt('unev'),
    SaveMstmt('unev2'),
    SaveMstmt('unev3'),
    SaveMstmt('argl'),
    AssignMstmt('expr', OpMxpr('get_expr_at', [RegMxpr('unev'), RegMxpr('unev3')])),
    AssignMstmt('continue', LabelMxpr('ev-call-operand-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-call-operand-ret'),
    RestoreMstmt('argl'),
    RestoreMstmt('unev3'),
    RestoreMstmt('unev2'),
    RestoreMstmt('unev'),
    RestoreMstmt('env'),
    # the evil list mutation, because of this argl must be recreated from op in every call
    PerformMstmt(OpMxpr('append_val_list', [RegMxpr('argl'), RegMxpr('val')])),
    AssignMstmt('unev3', OpMxpr('+', [RegMxpr('unev3'), ConstMxpr(NumberVal(1))])),
    GotoMstmt(LabelMxpr('ev-call-operand-start')),
    # calling body, need proc, and argl is already correct
  LabelMstmt('ev-call-call'),
    RestoreMstmt('proc'),
    RestoreMstmt('expr'),
    RestoreMstmt('continue'),
    AssignMstmt('unev', OpMxpr('get_val_type', [RegMxpr('proc')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('ProcPlainVal'))])),
    BranchMstmt(LabelMxpr('ev-call-proc-plain')),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(StringVal('PrimVal'))])),
    BranchMstmt(LabelMxpr('ev-call-prim')),
    GotoMstmt(LabelMxpr('ev-call-invalid')),

  LabelMstmt('ev-call-invalid'),  
    AssignMstmt('unev', OpMxpr('get_paren_token', [RegMxpr('expr')])),
    AssignMstmt('val', OpMxpr('ec_eval_call_invalid', [RegMxpr('proc')])),
    AssignMstmt('err', OpMxpr('concat_token_message', [RegMxpr('unev'), RegMxpr('val')])),
    GotoMstmt(LabelMxpr('error-handler')),

  LabelMstmt('ev-call-proc-plain'),
    AssignMstmt('val', OpMxpr('ec_check_proc_arity', [RegMxpr('proc'), RegMxpr('argl')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('val'), ConstMxpr(UndefVal())])),
    BranchMstmt(LabelMxpr('ev-call-proc-plain-arity-ok')),
    AssignMstmt('unev', OpMxpr('get_paren_token', [RegMxpr('expr')])),
    AssignMstmt('err', OpMxpr('concat_token_message', [RegMxpr('unev'), RegMxpr('val')])),
    GotoMstmt(LabelMxpr('error-handler')),
  LabelMstmt('ev-call-proc-plain-arity-ok'),
    AssignMstmt('env', OpMxpr('get_proc_env', [RegMxpr('proc')])),
    AssignMstmt('unev', OpMxpr('get_call_parameters', [RegMxpr('proc')])),
    AssignMstmt('unev2', OpMxpr('get_call_arguments', [RegMxpr('proc'), RegMxpr('argl')])),
    AssignMstmt('env', OpMxpr('ec_env_extend', [RegMxpr('env'), RegMxpr('unev'), RegMxpr('unev2')])),
    AssignMstmt('expr', OpMxpr('get_proc_plain_val_body', [RegMxpr('proc')])),
    GotoMstmt(LabelMxpr('ev-sequence')),

  LabelMstmt('ev-call-prim'),
    AssignMstmt('val', OpMxpr('ec_check_prim_arity', [RegMxpr('proc'), RegMxpr('argl')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('val'), ConstMxpr(UndefVal())])),
    BranchMstmt(LabelMxpr('ev-call-prim-arity-ok')),
    AssignMstmt('unev', OpMxpr('get_paren_token', [RegMxpr('expr')])),
    AssignMstmt('err', OpMxpr('concat_token_message', [RegMxpr('unev'), RegMxpr('val')])),
    GotoMstmt(LabelMxpr('error-handler')),
  LabelMstmt('ev-call-prim-arity-ok'),
    AssignMstmt('uenv', OpMxpr('call_prim', [RegMxpr('proc'), RegMxpr('argl')])),
    AssignMstmt('val', OpMxpr('car', [RegMxpr('uenv')])), 
    TestMstmt(OpMxpr('equal?', [RegMxpr('val'), ConstMxpr(UndefVal())])),
    BranchMstmt(LabelMxpr('ev-call-prim-call-ok')),
    AssignMstmt('unev', OpMxpr('get_paren_token', [RegMxpr('expr')])),
    AssignMstmt('err', OpMxpr('concat_token_message', [RegMxpr('unev'), RegMxpr('val')])),
    GotoMstmt(LabelMxpr('error-handler')),
  LabelMstmt('ev-call-prim-call-ok'),
    AssignMstmt('val', OpMxpr('cdr', [RegMxpr('uenv')])), 
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-if'),
    SaveMstmt('continue'),
    SaveMstmt('expr'),
    SaveMstmt('env'),
    AssignMstmt('expr', OpMxpr('get_if_predicate', [RegMxpr('expr')])),
    AssignMstmt('continue', LabelMxpr('ev-if-predicate-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-if-predicate-ret'),
    RestoreMstmt('env'),
    RestoreMstmt('expr'),
    RestoreMstmt('continue'),
    # directly assigning flag, not using test
    # here we assume TestMstmt will call is_truthy, so flag does not have to be boolean
    AssignMstmt('flag', RegMxpr('val')),
    BranchMstmt(LabelMxpr('ev-if-consequent')),
    TestMstmt(OpMxpr('has_if_alternative', [RegMxpr('expr')])),
    BranchMstmt(LabelMxpr('ev-if-alternative')),
    # no alternative
    AssignMstmt('val', ConstMxpr(UndefVal())),
    GotoMstmt(RegMxpr('continue')),
    # tail recursion supported
  LabelMstmt('ev-if-consequent'),
    AssignMstmt('expr', OpMxpr('get_if_consequent', [RegMxpr('expr')])),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-if-alternative'),
    AssignMstmt('expr', OpMxpr('get_if_alternative', [RegMxpr('expr')])),
    GotoMstmt(LabelMxpr('eval-dispatch')),

  LabelMstmt('ev-set'),
    SaveMstmt('expr'),
    SaveMstmt('env'),
    SaveMstmt('continue'),
    AssignMstmt('expr', OpMxpr('get_var_init', [RegMxpr('expr')])),
    AssignMstmt('continue', LabelMxpr('ev-set-init-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
    # now val = initializer
  LabelMstmt('ev-set-init-ret'),  
    RestoreMstmt('continue'),
    RestoreMstmt('env'),
    RestoreMstmt('expr'),
    # unev = name
    AssignMstmt('unev', OpMxpr('get_var_name', [RegMxpr('expr')])),
    # unev2 = distance
    AssignMstmt('unev2', OpMxpr('get_distance', [RegMxpr('dist'), RegMxpr('expr')])),
    AssignMstmt('val', OpMxpr('ec_env_set_at', [RegMxpr('env'), RegMxpr('unev2'), RegMxpr('unev'), RegMxpr('val')])),
    AssignMstmt('unev', OpMxpr('car', [RegMxpr('val')])),
    TestMstmt(OpMxpr('equal?', [RegMxpr('unev'), ConstMxpr(UndefVal())])),
    BranchMstmt(LabelMxpr('ev-set-ok')),
    AssignMstmt('val', OpMxpr('get_var_name_token', [RegMxpr('expr')])),
    AssignMstmt('err', OpMxpr('concat_token_message', [RegMxpr('val'), RegMxpr('unev')])),
    GotoMstmt(LabelMxpr('error-handler')),
  LabelMstmt('ev-set-ok'),
    AssignMstmt('val', OpMxpr('cdr', [RegMxpr('val')])),
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-define-var'),
    SaveMstmt('expr'),
    SaveMstmt('env'),
    SaveMstmt('continue'),
    AssignMstmt('expr', OpMxpr('get_var_init', [RegMxpr('expr')])),
    AssignMstmt('continue', LabelMxpr('ev-define-var-init-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-define-var-init-ret'),  
    RestoreMstmt('continue'),
    RestoreMstmt('env'),
    RestoreMstmt('expr'),
    AssignMstmt('unev', OpMxpr('get_var_name', [RegMxpr('expr')])),
    PerformMstmt(OpMxpr('ec_env_define', [RegMxpr('env'), RegMxpr('unev'), RegMxpr('val')])),
    AssignMstmt('val', OpMxpr('get_var_symbol', [RegMxpr('expr')])),
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-define-proc'),
    AssignMstmt('val', OpMxpr('ec_define_proc_plain_val', [RegMxpr('expr'), RegMxpr('env')])),
    AssignMstmt('unev', OpMxpr('get_var_name', [RegMxpr('expr')])),
    PerformMstmt(OpMxpr('ec_env_define', [RegMxpr('env'), RegMxpr('unev'), RegMxpr('val')])),
    AssignMstmt('val', OpMxpr('get_var_symbol', [RegMxpr('expr')])),
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-and'),
    AssignMstmt('unev', OpMxpr('get_expr_contents', [RegMxpr('expr')])),
    AssignMstmt('unev2', OpMxpr('get_exprs_len', [RegMxpr('unev')])),
    SaveMstmt('continue'),
    # init unev3 = 0
    AssignMstmt('unev3', ConstMxpr(NumberVal(0))),
  LabelMstmt('ev-and-loop'),
    TestMstmt(OpMxpr('=', [RegMxpr('unev3'), RegMxpr('unev2')])),
    BranchMstmt(LabelMxpr('ev-and-finish')),
    SaveMstmt('unev'),
    SaveMstmt('unev2'),
    SaveMstmt('unev3'),
    SaveMstmt('env'),
    AssignMstmt('expr', OpMxpr('get_expr_at', [RegMxpr('unev'), RegMxpr('unev3')])),
    AssignMstmt('continue', LabelMxpr('ev-and-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-and-ret'),
    RestoreMstmt('env'),
    RestoreMstmt('unev3'),
    RestoreMstmt('unev2'),
    RestoreMstmt('unev'),
    AssignMstmt('unev3', OpMxpr('+', [RegMxpr('unev3'), ConstMxpr(NumberVal(1))])),
    AssignMstmt('flag', RegMxpr('val')),
    BranchMstmt(LabelMxpr('ev-and-loop')),
    # no support for tail recursion, because we don't know where to early return (which is first falsy expr)
  LabelMstmt('ev-and-finish'),
    RestoreMstmt('continue'),
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-or'),
    AssignMstmt('unev', OpMxpr('get_expr_contents', [RegMxpr('expr')])),
    AssignMstmt('unev2', OpMxpr('get_exprs_len', [RegMxpr('unev')])),
    SaveMstmt('continue'),
    # init unev3 = 0
    AssignMstmt('unev3', ConstMxpr(NumberVal(0))),
  LabelMstmt('ev-or-loop'),
    TestMstmt(OpMxpr('=', [RegMxpr('unev3'), RegMxpr('unev2')])),
    BranchMstmt(LabelMxpr('ev-or-finish')),
    SaveMstmt('unev'),
    SaveMstmt('unev2'),
    SaveMstmt('unev3'),
    SaveMstmt('env'),
    AssignMstmt('expr', OpMxpr('get_expr_at', [RegMxpr('unev'), RegMxpr('unev3')])),
    AssignMstmt('continue', LabelMxpr('ev-or-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-or-ret'),
    RestoreMstmt('env'),
    RestoreMstmt('unev3'),
    RestoreMstmt('unev2'),
    RestoreMstmt('unev'),
    AssignMstmt('unev3', OpMxpr('+', [RegMxpr('unev3'), ConstMxpr(NumberVal(1))])),
    AssignMstmt('flag', RegMxpr('val')),
    # only difference with and: branch go to finish, rather than loop
    BranchMstmt(LabelMxpr('ev-or-finish')),
    GotoMstmt(LabelMxpr('ev-or-loop')),
  LabelMstmt('ev-or-finish'),
    RestoreMstmt('continue'),
    GotoMstmt(RegMxpr('continue')),

  LabelMstmt('ev-not'),
    SaveMstmt('continue'),
    AssignMstmt('expr', OpMxpr('get_expr_content', [RegMxpr('expr')])),
    AssignMstmt('continue', LabelMxpr('ev-not-ret')),
    GotoMstmt(LabelMxpr('eval-dispatch')),
  LabelMstmt('ev-not-ret'), 
    AssignMstmt('val', OpMxpr('boolean_not', [RegMxpr('val')])),
    RestoreMstmt('continue'),
    GotoMstmt(RegMxpr('continue')),

    # handling of all errors are the same
  LabelMstmt('error-handler'),
    # just goto_panic, assuming the error message in val 
    PerformMstmt(OpMxpr('goto_panic', [RegMxpr('err')])),
    # following goto not really necessary, since goto_panic will exit execution
    GotoMstmt(LabelMxpr('done')),

  LabelMstmt('done')
]

# fmt: on

'''
additioanl operations
we try to make their input/ouput only of following types
Expression, List[Expression], Environment, SchemeVal, List[SchemeVal], Token
we try to exclude pure integer and string
'''


def concat_token_message(token: Token, message: StringVal):
    rt_err = SchemeRuntimeError(token, message.value)
    return StringVal(str(rt_err))


def get_distance(distances: ResDistancesType, expr: Union[SymbolExpr, SetExpr]):
    return NumberVal(distances[expr])


def ec_env_lookup_at(env: Environment, distance: NumberVal, name: StringVal):
    '''return error and result'''
    try:
        return PairVal(UndefVal(), env_lookup_at(env, int(distance.value), name.value))
    except SchemeEnvError:
        return PairVal(StringVal('symbol undefined'), UndefVal())


def ec_eval_expr_invalid(expr_type: StringVal):
    message = 'expression type undefined: %s' % expr_type.value
    return StringVal(message)


def ec_eval_call_invalid(operator: SchemeVal):
    return StringVal('cannot call %s value' % type(operator).__name__)


def _ec_check_arity(name: str, pos_arity: int, has_rest: bool, arg_count: int):
    if has_rest:
        if arg_count < pos_arity:
            return '%s expect at least %d arguments, only get %d' % (name, pos_arity, arg_count)
    else:
        if arg_count != pos_arity:
            return '%s expect exactly %d arguments, but get %d' % (name, pos_arity, arg_count)
    return ''


def ec_check_prim_arity(operator: PrimVal, operands: List[SchemeVal]):
    message = _ec_check_arity(
        operator.name, operator.pos_arity, operator.has_rest, len(operands))
    return UndefVal() if message == '' else StringVal(message)


def ec_check_proc_arity(operator: ProcVal, operands: List[SchemeVal]):
    message = _ec_check_arity(operator.name, len(
        operator.pos_paras), operator.rest_para is not None, len(operands))
    return UndefVal() if message == '' else StringVal(message)


def get_expr_type(expr: GenericExpr):
    return StringVal(type(expr).__name__)


def get_expr_contents(expr: Union[SequenceExpr, AndExpr, OrExpr]):
    return expr.contents


def get_expr_content(expr: NotExpr):
    return expr.content


def get_exprs_len(exprs: List[GenericExpr]):
    return NumberVal(len(exprs))


def get_expr_at(exprs: List[GenericExpr], index: NumberVal):
    return exprs[int(index.value)]


def get_paren_token(expr: CallExpr):
    return expr.paren


def get_call_operator(expr: CallExpr):
    return expr.operator


def get_call_operands(expr: CallExpr):
    return expr.operands


def get_proc_plain_val_body(proc: ProcPlainVal):
    return proc.body


def ec_define_proc_plain_val(expr: DefineProcExpr, env: Environment):
    return pure_eval_define_proc_plain_value(expr.name.literal, expr.pos_paras, expr.rest_para, expr.body, env)


def init_val_list():
    ls: List[SchemeVal] = []
    return ls


def append_val_list(vals: List[SchemeVal], val: SchemeVal):
    vals.append(val)


def get_val_type(expr: GenericVal):
    return StringVal(type(expr).__name__)


def call_prim(operator: PrimVal, operands: List[SchemeVal]):
    try:
        return PairVal(UndefVal(), operator.body(*operands))
    except SchemePrimError as err:
        return PairVal(StringVal(err.message), UndefVal())


def get_if_predicate(expr: IfExpr):
    return expr.pred


def get_if_consequent(expr: IfExpr):
    return expr.then_branch


def get_if_alternative(expr: IfExpr):
    return expr.else_branch


def has_if_alternative(expr: IfExpr):
    return BooleanVal(expr.else_branch is not None)


def get_var_name(expr: Union[SymbolExpr, SetExpr, DefineVarExpr, DefineProcExpr]):
    return StringVal(expr.name.literal)


def get_var_name_token(expr: Union[SymbolExpr, SetExpr, DefineVarExpr, DefineProcExpr]):
    return expr.name


def get_var_symbol(expr: Union[SymbolExpr, SetExpr, DefineVarExpr, DefineProcExpr]):
    return SymbolVal(expr.name.literal)


def get_var_init(expr: Union[SetExpr, DefineVarExpr]):
    return expr.initializer


def ec_env_set_at(env: Environment, distance: NumberVal, name: StringVal, initializer: SchemeVal):
    try:
        env_set_at(env, int(distance.value), name.value, initializer)
        return PairVal(UndefVal(), initializer)
    except SchemeEnvError:
        return PairVal(StringVal('symbol undefined'), UndefVal())


def ec_env_define(env: Environment, name: StringVal, initializer: SchemeVal):
    env_define(env, name.value, initializer)


def goto_panic(message: StringVal):
    scheme_panic(message.value)


def boolean_not(val: SchemeVal):
    return BooleanVal(False if is_truthy(val) else True)


def get_proc_env(val: ProcPlainVal):
    return val.env


def get_call_parameters(operator: ProcVal):
    parameters = pure_get_proc_parameters(operator)
    return [StringVal(s) for s in parameters]


def get_call_arguments(operator: ProcVal, operands: List[SchemeVal]):
    arguments = pure_get_proc_arguments(operator, operands)
    return arguments


def ec_env_extend(env: Environment, parameters: List[StringVal], arguments: List[SchemeVal]):
    return env_extend(env, [s.value for s in parameters], arguments)


def install_ec_operations():
    ops = {
        'pure_eval_string': pure_eval_string,
        'pure_eval_number': pure_eval_number,
        'pure_eval_boolean': pure_eval_boolean,
        'pure_eval_nil': pure_eval_nil,
        'pure_eval_quote': pure_eval_quote,
        'pure_eval_lambda_plain': pure_eval_lambda_plain,
        'pure_eval_define_var': pure_eval_define_var,
        'goto_panic': goto_panic,

        'get_var_name_token': get_var_name_token,
        'concat_token_message': concat_token_message,
        'get_expr_type': get_expr_type,
        'get_expr_contents': get_expr_contents,
        'get_expr_content': get_expr_content,
        'get_exprs_len': get_exprs_len,
        'get_expr_at': get_expr_at,
        'get_paren_token': get_paren_token,
        'get_call_operator': get_call_operator,
        'get_call_operands': get_call_operands,
        'get_proc_plain_val_body': get_proc_plain_val_body,
        'get_proc_env': get_proc_env,
        'get_call_parameters': get_call_parameters,
        'get_call_arguments': get_call_arguments,
        'init_val_list': init_val_list,
        'append_val_list': append_val_list,
        'get_val_type': get_val_type,
        'call_prim': call_prim,
        'get_if_predicate': get_if_predicate,
        'get_if_consequent': get_if_consequent,
        'get_if_alternative': get_if_alternative,
        'has_if_alternative': has_if_alternative,
        'get_var_name': get_var_name,
        'get_var_symbol': get_var_symbol,
        'get_var_init': get_var_init,
        'ec_env_set_at': ec_env_set_at,
        'ec_env_define': ec_env_define,
        'ec_env_lookup_at': ec_env_lookup_at,
        'ec_env_extend': ec_env_extend,
        'get_distance': get_distance,
        'ec_define_proc_plain_val': ec_define_proc_plain_val,
        'ec_eval_expr_invalid': ec_eval_expr_invalid,
        'ec_eval_call_invalid': ec_eval_call_invalid,
        'ec_check_prim_arity': ec_check_prim_arity,
        'ec_check_proc_arity': ec_check_proc_arity,
        'boolean_not': boolean_not,
    }
    update_operations(ops)


'''
we have two more tmp registers: unev2, unev3
we also have dist register to hold resolution distances
and err register hold err message
'''
ec_eval_regs = {
    'val': None,
    'expr': None,
    'env': None,
    'unev': None,
    'unev2': None,
    'unev3': None,
    'dist': None,
    'err': None
}


def test_one(source: str, **kargs: str):
    # source
    source = source.strip()
    print('* source: %s' % source)

    try:
        # scan
        tokens = scan_source(source)

        # parse
        combos = parse_tokens(tokens)
        expr = parse_expr(combos)

        # resolve
        distances = resolve_expr(expr)

        # build machine
        ops = get_operations()
        glbenv = make_global_env()
        machine = make_machine(ec_eval_regs, ops, ec_eval_code)
        machine.state.regs.update(
            {'expr': expr, 'env': glbenv, 'dist': distances})
        execute_machine = make_run_machine(lambda _: False)

        # result
        init_machine_pc(machine)
        execute_machine(machine)
        result = machine.state.regs['val']
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


def test_one_recursion(source_tmpl: str, name: str, nrng: Tuple[int, int], get_val: Callable[[int], int]):
    print('%s (%d, %d)' % (name, nrng[0], nrng[1]))
    source_tmpl = source_tmpl.strip()
    print(source_tmpl)
    for nval in range(*nrng):
        # source
        source = source_tmpl % nval

        try:
            # scan
            tokens = scan_source(source)

            # parse
            combos = parse_tokens(tokens)
            expr = parse_expr(combos)

            # resolve
            distances = resolve_expr(expr)

            # build machine
            ops = get_operations()
            glbenv = make_global_env()
            machine = make_machine(ec_eval_regs, ops, ec_eval_code)
            statistics = MachineStatistic()
            monitor_statistics(machine.instructions, machine.state, statistics)
            machine.state.regs.update(
                {'expr': expr, 'env': glbenv, 'dist': distances})
            execute_machine = make_run_machine(lambda _: False)

            # result
            init_machine_pc(machine)
            execute_machine(machine)
            res = machine.state.regs['val']
            res_str = stringify_value(res)
            assert res_str == str(get_val(nval))

            print('n = %d, val = %s, total_insts = %d, stack_ops = %d, stack_depth = %d' %
                  (nval, res_str, statistics.total_insts, statistics.stack_ops, statistics.stack_depth))

        except SchemePanic as err:
            # any kind of panic
            print('* panic: %s' % err.message)
            assert False
    print('----------')


def test_error():
    test_one(
        'x',
        panic='runtime error at SYMBOL:x in line 1: symbol undefined'
    )
    test_one(
        '''
        (define (f a b . c) c)
        (f 1)
        ''',
        panic='runtime error at LEFT_PAREN in line 2: f expect at least 2 arguments, only get 1'
    )
    test_one(
        '''
        (define f "not_an_op")
        (f 1 2)
        ''',
        panic='runtime error at LEFT_PAREN in line 2: cannot call StringVal value'
    )
    test_one(
        '(+ "1" "2")',
        panic='runtime error at LEFT_PAREN in line 1: <lambda> requires both operators to be numbers, now StringVal and StringVal'
    )


def test_expr():
    test_one(
        '((lambda (x) (+ x 1)) 2)',
        result='3',
    )
    test_one(
        '''
        (define (f x) (+ x 1))
        (f 2)
        ''',
        result='3',
    )
    test_one(
        '(if #t (if 3 4) 2)',
        result='4',
    )
    test_one(
        '(and (+ 1 2) (or (not #t) (list 3 4)))',
        result='(3 4)',
    )
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


def test_resolve():
    # use before intialization in different scopes pass resolution
    test_one(
        '''
        (define (f)
          (define (g) x)
          (define x 1)
          (g))
        (f)
        ''',
        result='1'
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
        result='2'
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


def factorial(n: int):
    product = 1
    for i in range(1, n+1):
        product *= i
    return product


def test_recursion():
    # recursion
    test_one_recursion(
        '''
        (define (factorial n)
          (if (= n 1)
            1
            (* n (factorial (- n 1)))))
        (factorial %d)
        ''',
        name='factorial-recur',
        nrng=(1, 10),
        get_val=factorial
    )
    # iteration, should use constant stack depth
    test_one_recursion(
        '''
        (define (factorial n)
          (define (fact-iter product counter)
            (if (> counter n)
               product
               (fact-iter (* counter product)
                 (+ counter 1))))
          (fact-iter 1 1))
        (factorial %d)
        ''',
        name='factorial-iter',
        nrng=(1, 10),
        get_val=factorial
    )


def install_rules():
    install_parse_expr_rules()
    install_stringify_expr_rules()
    install_stringify_value_rules()
    install_is_equal_rules()
    install_resolver_rules()
    install_primitives()
    install_assemble_mxpr_rules()
    install_assemble_mstmt_rules()
    install_operations()
    install_ec_operations()


def test():
    test_error()
    test_expr()
    test_resolve()
    test_recursion()


if __name__ == '__main__':
    install_rules()
    test()

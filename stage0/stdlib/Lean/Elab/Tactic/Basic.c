// Lean compiler output
// Module: Lean.Elab.Tactic.Basic
// Imports: Lean.Meta.Tactic.Util Lean.Elab.Term
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___rarg___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalTactic_handleEx___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__2;
static lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__9;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___closed__1;
extern lean_object* l_Lean_profiler;
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__2(lean_object*);
static lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_admitGoal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__4;
lean_object* l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__4;
static lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_evalTactic___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___rarg(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Context_recover___default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instOrElseTacticM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SavedState_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_instInhabitedTacticParsedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__11;
lean_object* l_Lean_indentD(lean_object*);
double lean_float_div(double, double);
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__1;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__1;
lean_object* lean_io_promise_new(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___closed__2;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTacticAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTactic___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__1;
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_handleEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__2;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___boxed(lean_object**);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297_(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__10;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__5;
static lean_object* l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__2;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getMessageLog___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__3;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_instMonadTermElabM;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_appendGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_eval___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withoutRecover___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__3;
static lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focus(lean_object*);
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1;
static double l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__4;
static lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__2;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_evalTactic___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_orElse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1;
static lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__3;
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_goalsToMessageData___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_result(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_setMVarUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_replaceMainGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__6___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState___boxed(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_throwExs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_throwExs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_eval___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_instAlternativeTacticM___spec__1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__3;
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__6;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkTacticAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_checked_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__8;
static lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic_throwExs___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___closed__2;
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Elab_Tactic_evalTactic___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__2;
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__2;
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2___boxed(lean_object**);
static lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1;
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
static double l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__6;
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__1;
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_withMacroExpansion___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__7;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM;
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8339_(lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8339____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__3;
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Elab_Tactic_evalTactic___spec__4___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__15;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_orElse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___rarg(lean_object*);
lean_object* lean_io_mono_nanos_now(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__4;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withRestoreOrSaveFull___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_builtinIncrementalElabs;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Elab_Tactic_evalTactic___spec__9(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_reportUnsolvedGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__3;
static lean_object* l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_eval___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
extern lean_object* l_Lean_warningAsError;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
static lean_object* l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__2;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_threshold;
uint8_t l_Lean_MetavarContext_isAnonymousMVar(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1;
static lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_evalTactic_eval___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_run___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Language_Snapshot_Diagnostics_empty;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_isAbortTacticException(lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_goalsToMessageData___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatch(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isAssigned___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Elab_Tactic_evalTactic___spec__4___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__9;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Elab_Tactic_evalTactic___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_interruptExceptionId;
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkTacticInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTactic___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Elab_Tactic_evalTactic___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTacticAtRaw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Elab_Tactic_evalTactic___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__2;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__2(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___rarg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__2(lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__2;
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__4;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_appendGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__13;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_handleEx___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMainContext(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_instAlternativeTacticM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_incrementalAttr;
static lean_object* l_Lean_Elab_Tactic_instOrElseTacticM___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalTactic_handleEx___closed__2;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_adaptExpander___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_instAlternativeTacticM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic_throwExs___closed__1;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2;
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_done___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_withMacroExpansion___spec__2(lean_object*);
extern lean_object* l_Lean_trace_profiler;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule___rarg(lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__1;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__3;
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__8;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__7;
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__4;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_handleEx___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__3;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__5;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_admitGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___boxed(lean_object**);
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__6;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_done(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_106_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__14;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__2;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
extern lean_object* l_Lean_Elab_abortTacticExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
double lean_float_sub(double, double);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l_Lean_Elab_goalsToMessageData___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_pure___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withoutRecover(lean_object*);
lean_object* l_Array_get_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_admitGoal___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Meta_mkSorry(x_9, x_11, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_2, x_13, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_admitGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = l_Lean_Expr_mvar___override(x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_admitGoal___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_goalsToMessageData___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_goalsToMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_goalsToMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_goalsToMessageData___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_goalsToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at_Lean_Elab_goalsToMessageData___spec__1(x_1, x_2);
x_4 = l_Lean_Elab_goalsToMessageData___closed__2;
x_5 = l_Lean_MessageData_joinSep(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_reportUnsolvedGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Elab_admitGoal(x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_1 = x_10;
x_6 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_2 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolved goals\n", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_7 = l_Lean_Elab_goalsToMessageData(x_1);
x_8 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__5;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__3;
x_13 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = 2;
lean_inc(x_4);
x_15 = l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(x_13, x_14, x_2, x_3, x_4, x_5, x_6);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_List_forM___at_Lean_Elab_Term_reportUnsolvedGoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_16);
return x_17;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Context_recover___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = lean_apply_9(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_apply_10(x_4, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_instMonadTermElabM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_instMonadTacticM___closed__1;
x_2 = l_ReaderT_instFunctorOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_instMonadTacticM___closed__1;
x_2 = l_ReaderT_instApplicativeOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadTacticM___lambda__1___boxed), 11, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadTacticM___lambda__2), 13, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Elab_Tactic_instMonadTacticM___closed__3;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
x_5 = l_Lean_Elab_Tactic_instMonadTacticM___closed__2;
x_6 = l_Lean_Elab_Tactic_instMonadTacticM___closed__4;
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
x_7 = l_Lean_Elab_Tactic_instMonadTacticM___closed__5;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_instMonadTacticM___closed__2;
x_13 = l_Lean_Elab_Tactic_instMonadTacticM___closed__4;
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
x_15 = l_Lean_Elab_Tactic_instMonadTacticM___closed__5;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_instMonadTacticM___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_instMonadTacticM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instInhabitedTacticM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instInhabitedTacticM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_instInhabitedTacticM___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_instInhabitedTacticM___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instInhabitedTacticM___rarg), 1, 0);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_instInhabitedTacticM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getGoals___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_getGoals___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getGoals(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_set(x_3, x_1, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_setGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_7, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 7);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isAssigned___spec__1(x_15, x_1);
x_17 = lean_box(x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 7);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isAssigned___spec__1(x_21, x_1);
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = l_Lean_MVarId_isAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_15;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_10 = x_19;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_object* x_21; 
lean_free_object(x_1);
lean_dec(x_14);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_1 = x_15;
x_11 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = l_Lean_MVarId_isAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_2);
x_1 = x_24;
x_2 = x_29;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_31; 
lean_dec(x_23);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_1 = x_24;
x_11 = x_31;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l_Lean_Elab_Tactic_getGoals___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_List_filterAuxM___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__2(x_11, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_reverse___rarg(x_15);
x_18 = l_Lean_Elab_Tactic_setGoals(x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_isAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_filterAuxM___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Tactic_getGoals___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_mk_ref(x_3, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_15 = lean_apply_9(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_13, x_17);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_11, 1, x_20);
lean_ctor_set(x_11, 0, x_16);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_11, 1, x_21);
lean_ctor_set(x_11, 0, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_11);
lean_dec(x_13);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
lean_inc(x_28);
x_30 = lean_apply_9(x_1, x_2, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_28, x_32);
lean_dec(x_28);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_34);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_28);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_41 = x_30;
} else {
 lean_dec_ref(x_30);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_st_mk_ref(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = lean_apply_9(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_12, x_16);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_2, x_3, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg), 9, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_run___lambda__1___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_4, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_15, 2);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_15, 2, x_19);
x_20 = lean_st_ref_set(x_4, x_15, x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_77; lean_object* x_78; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 0, x_1);
x_48 = lean_st_mk_ref(x_20, x_22);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_77 = l_Lean_Elab_Tactic_run___lambda__1___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_78 = lean_apply_9(x_2, x_77, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_50);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_77, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_51 = x_81;
x_52 = x_82;
goto block_76;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
lean_dec(x_78);
x_85 = l_Lean_Exception_isInterrupt(x_83);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = l_Lean_Exception_isRuntime(x_83);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = l_Lean_Elab_isAbortTacticException(x_83);
if (x_87 == 0)
{
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_24 = x_83;
x_25 = x_84;
goto block_47;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_83);
x_88 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_77, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_84);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_51 = x_89;
x_52 = x_90;
goto block_76;
}
}
else
{
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_24 = x_83;
x_25 = x_84;
goto block_47;
}
}
else
{
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_24 = x_83;
x_25 = x_84;
goto block_47;
}
}
block_47:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_st_ref_take(x_4, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_27, 2);
lean_dec(x_30);
lean_ctor_set(x_27, 2, x_13);
x_31 = lean_st_ref_set(x_4, x_27, x_28);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_24);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
x_38 = lean_ctor_get(x_27, 3);
x_39 = lean_ctor_get(x_27, 4);
x_40 = lean_ctor_get(x_27, 5);
x_41 = lean_ctor_get(x_27, 6);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_42 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 2, x_13);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_42, 5, x_40);
lean_ctor_set(x_42, 6, x_41);
x_43 = lean_st_ref_set(x_4, x_42, x_28);
lean_dec(x_4);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_24);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
block_76:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_st_ref_get(x_49, x_52);
lean_dec(x_49);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_take(x_4, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_56, 2);
lean_dec(x_59);
lean_ctor_set(x_56, 2, x_13);
x_60 = lean_st_ref_set(x_4, x_56, x_57);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set(x_60, 0, x_51);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_51);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_56, 0);
x_66 = lean_ctor_get(x_56, 1);
x_67 = lean_ctor_get(x_56, 3);
x_68 = lean_ctor_get(x_56, 4);
x_69 = lean_ctor_get(x_56, 5);
x_70 = lean_ctor_get(x_56, 6);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_56);
x_71 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_66);
lean_ctor_set(x_71, 2, x_13);
lean_ctor_set(x_71, 3, x_67);
lean_ctor_set(x_71, 4, x_68);
lean_ctor_set(x_71, 5, x_69);
lean_ctor_set(x_71, 6, x_70);
x_72 = lean_st_ref_set(x_4, x_71, x_57);
lean_dec(x_4);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_51);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_134; lean_object* x_135; 
x_91 = lean_ctor_get(x_20, 1);
lean_inc(x_91);
lean_dec(x_20);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_19);
x_111 = lean_st_mk_ref(x_92, x_91);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_134 = l_Lean_Elab_Tactic_run___lambda__1___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_112);
x_135 = lean_apply_9(x_2, x_134, x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_113);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_134, x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_136);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_114 = x_138;
x_115 = x_139;
goto block_133;
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 1);
lean_inc(x_141);
lean_dec(x_135);
x_142 = l_Lean_Exception_isInterrupt(x_140);
if (x_142 == 0)
{
uint8_t x_143; 
x_143 = l_Lean_Exception_isRuntime(x_140);
if (x_143 == 0)
{
uint8_t x_144; 
x_144 = l_Lean_Elab_isAbortTacticException(x_140);
if (x_144 == 0)
{
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_93 = x_140;
x_94 = x_141;
goto block_110;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_140);
x_145 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_134, x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_141);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_114 = x_146;
x_115 = x_147;
goto block_133;
}
}
else
{
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_93 = x_140;
x_94 = x_141;
goto block_110;
}
}
else
{
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_93 = x_140;
x_94 = x_141;
goto block_110;
}
}
block_110:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_95 = lean_st_ref_take(x_4, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_96, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 5);
lean_inc(x_102);
x_103 = lean_ctor_get(x_96, 6);
lean_inc(x_103);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 lean_ctor_release(x_96, 3);
 lean_ctor_release(x_96, 4);
 lean_ctor_release(x_96, 5);
 lean_ctor_release(x_96, 6);
 x_104 = x_96;
} else {
 lean_dec_ref(x_96);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 7, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_99);
lean_ctor_set(x_105, 2, x_13);
lean_ctor_set(x_105, 3, x_100);
lean_ctor_set(x_105, 4, x_101);
lean_ctor_set(x_105, 5, x_102);
lean_ctor_set(x_105, 6, x_103);
x_106 = lean_st_ref_set(x_4, x_105, x_97);
lean_dec(x_4);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
 lean_ctor_set_tag(x_109, 1);
}
lean_ctor_set(x_109, 0, x_93);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
block_133:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_116 = lean_st_ref_get(x_112, x_115);
lean_dec(x_112);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_st_ref_take(x_4, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 5);
lean_inc(x_125);
x_126 = lean_ctor_get(x_119, 6);
lean_inc(x_126);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 lean_ctor_release(x_119, 5);
 lean_ctor_release(x_119, 6);
 x_127 = x_119;
} else {
 lean_dec_ref(x_119);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 7, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_121);
lean_ctor_set(x_128, 1, x_122);
lean_ctor_set(x_128, 2, x_13);
lean_ctor_set(x_128, 3, x_123);
lean_ctor_set(x_128, 4, x_124);
lean_ctor_set(x_128, 5, x_125);
lean_ctor_set(x_128, 6, x_126);
x_129 = lean_st_ref_set(x_4, x_128, x_120);
lean_dec(x_4);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_114);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_201; lean_object* x_202; 
x_148 = lean_ctor_get(x_15, 0);
x_149 = lean_ctor_get(x_15, 1);
x_150 = lean_ctor_get(x_15, 3);
x_151 = lean_ctor_get(x_15, 4);
x_152 = lean_ctor_get(x_15, 5);
x_153 = lean_ctor_get(x_15, 6);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_15);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_155, 0, x_148);
lean_ctor_set(x_155, 1, x_149);
lean_ctor_set(x_155, 2, x_154);
lean_ctor_set(x_155, 3, x_150);
lean_ctor_set(x_155, 4, x_151);
lean_ctor_set(x_155, 5, x_152);
lean_ctor_set(x_155, 6, x_153);
x_156 = lean_st_ref_set(x_4, x_155, x_16);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
 lean_ctor_set_tag(x_159, 1);
}
lean_ctor_set(x_159, 0, x_1);
lean_ctor_set(x_159, 1, x_154);
x_178 = lean_st_mk_ref(x_159, x_157);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_201 = l_Lean_Elab_Tactic_run___lambda__1___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_179);
x_202 = lean_apply_9(x_2, x_201, x_179, x_3, x_4, x_5, x_6, x_7, x_8, x_180);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_201, x_179, x_3, x_4, x_5, x_6, x_7, x_8, x_203);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_181 = x_205;
x_182 = x_206;
goto block_200;
}
else
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_207 = lean_ctor_get(x_202, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_202, 1);
lean_inc(x_208);
lean_dec(x_202);
x_209 = l_Lean_Exception_isInterrupt(x_207);
if (x_209 == 0)
{
uint8_t x_210; 
x_210 = l_Lean_Exception_isRuntime(x_207);
if (x_210 == 0)
{
uint8_t x_211; 
x_211 = l_Lean_Elab_isAbortTacticException(x_207);
if (x_211 == 0)
{
lean_dec(x_179);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_160 = x_207;
x_161 = x_208;
goto block_177;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_207);
x_212 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_201, x_179, x_3, x_4, x_5, x_6, x_7, x_8, x_208);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_181 = x_213;
x_182 = x_214;
goto block_200;
}
}
else
{
lean_dec(x_179);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_160 = x_207;
x_161 = x_208;
goto block_177;
}
}
else
{
lean_dec(x_179);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_160 = x_207;
x_161 = x_208;
goto block_177;
}
}
block_177:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_162 = lean_st_ref_take(x_4, x_161);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 4);
lean_inc(x_168);
x_169 = lean_ctor_get(x_163, 5);
lean_inc(x_169);
x_170 = lean_ctor_get(x_163, 6);
lean_inc(x_170);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 lean_ctor_release(x_163, 3);
 lean_ctor_release(x_163, 4);
 lean_ctor_release(x_163, 5);
 lean_ctor_release(x_163, 6);
 x_171 = x_163;
} else {
 lean_dec_ref(x_163);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 7, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_165);
lean_ctor_set(x_172, 1, x_166);
lean_ctor_set(x_172, 2, x_13);
lean_ctor_set(x_172, 3, x_167);
lean_ctor_set(x_172, 4, x_168);
lean_ctor_set(x_172, 5, x_169);
lean_ctor_set(x_172, 6, x_170);
x_173 = lean_st_ref_set(x_4, x_172, x_164);
lean_dec(x_4);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
 lean_ctor_set_tag(x_176, 1);
}
lean_ctor_set(x_176, 0, x_160);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
block_200:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_183 = lean_st_ref_get(x_179, x_182);
lean_dec(x_179);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_st_ref_take(x_4, x_184);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_186, 3);
lean_inc(x_190);
x_191 = lean_ctor_get(x_186, 4);
lean_inc(x_191);
x_192 = lean_ctor_get(x_186, 5);
lean_inc(x_192);
x_193 = lean_ctor_get(x_186, 6);
lean_inc(x_193);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 lean_ctor_release(x_186, 4);
 lean_ctor_release(x_186, 5);
 lean_ctor_release(x_186, 6);
 x_194 = x_186;
} else {
 lean_dec_ref(x_186);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(0, 7, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_188);
lean_ctor_set(x_195, 1, x_189);
lean_ctor_set(x_195, 2, x_13);
lean_ctor_set(x_195, 3, x_190);
lean_ctor_set(x_195, 4, x_191);
lean_ctor_set(x_195, 5, x_192);
lean_ctor_set(x_195, 6, x_193);
x_196 = lean_st_ref_set(x_4, x_195, x_187);
lean_dec(x_4);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_181);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___lambda__1), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Term_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_st_ref_get(x_1, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_9, 1, x_14);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_9, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_st_ref_get(x_1, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_21);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_saveState___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_saveState___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_saveState(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l_Lean_Elab_Term_SavedState_restore(x_12, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_st_ref_set(x_4, x_15, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SavedState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_6);
x_14 = lean_apply_2(x_1, x_5, x_6);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Elab_Term_withRestoreOrSaveFull___rarg(x_15, x_3, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_st_ref_get(x_6, x_18);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_17, 1, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_st_ref_get(x_6, x_18);
lean_dec(x_6);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_2);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 1);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
lean_ctor_set(x_43, 1, x_46);
x_47 = l_Lean_Elab_Term_withRestoreOrSaveFull___rarg(x_2, x_3, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_st_ref_get(x_6, x_49);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_48, 1, x_55);
lean_ctor_set(x_52, 0, x_48);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_48, 1, x_58);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_48, 0);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_48);
x_62 = lean_st_ref_get(x_6, x_49);
lean_dec(x_6);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_6);
x_69 = !lean_is_exclusive(x_47);
if (x_69 == 0)
{
return x_47;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_47, 0);
x_71 = lean_ctor_get(x_47, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_47);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_43, 0);
x_74 = lean_ctor_get(x_43, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_43);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_2, 0, x_76);
x_77 = l_Lean_Elab_Term_withRestoreOrSaveFull___rarg(x_2, x_3, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = lean_st_ref_get(x_6, x_79);
lean_dec(x_6);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_84);
if (lean_is_scalar(x_82)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_82;
}
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set(x_88, 1, x_87);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_6);
x_90 = lean_ctor_get(x_77, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_77, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_92 = x_77;
} else {
 lean_dec_ref(x_77);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_2, 0);
lean_inc(x_94);
lean_dec(x_2);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lean_Elab_Term_withRestoreOrSaveFull___rarg(x_100, x_3, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_106 = x_102;
} else {
 lean_dec_ref(x_102);
 x_106 = lean_box(0);
}
x_107 = lean_st_ref_get(x_6, x_103);
lean_dec(x_6);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_108);
if (lean_is_scalar(x_106)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_106;
}
lean_ctor_set(x_112, 0, x_104);
lean_ctor_set(x_112, 1, x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_109);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_6);
x_114 = lean_ctor_get(x_101, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_101, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_116 = x_101;
} else {
 lean_dec_ref(x_101);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Elab_Tactic_withRestoreOrSaveFull___rarg___lambda__1(x_3, x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_set(x_5, x_17, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Tactic_withRestoreOrSaveFull___rarg___lambda__1(x_3, x_1, x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRestoreOrSaveFull___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_withRestoreOrSaveFull___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 10);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getCurrMacroScope___rarg___boxed), 3, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_getCurrMacroScope___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_getCurrMacroScope(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_environment_main_module(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_environment_main_module(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMainModule___rarg___boxed), 2, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getMainModule___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_getMainModule(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("builtin_tactic", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__6;
x_3 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
x_3 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_4 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticElabAttribute", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
x_3 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_4 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkTacticAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__2;
x_3 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__4;
x_4 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__7;
x_5 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__9;
x_6 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__3;
x_7 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__11;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkTacticInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_9, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 0, x_21);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_1);
lean_ctor_set(x_22, 2, x_2);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 0, x_26);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_27, 2, x_2);
lean_ctor_set(x_27, 3, x_17);
lean_ctor_set(x_27, 4, x_24);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_1);
lean_ctor_set(x_39, 2, x_2);
lean_ctor_set(x_39, 3, x_32);
lean_ctor_set(x_39, 4, x_34);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkTacticInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_mkTacticInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_mkTacticInfo(x_2, x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1___boxed), 12, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_14);
lean_closure_set(x_18, 2, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1___boxed), 12, 3);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_14);
lean_closure_set(x_21, 2, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 6);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 6);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 6);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_10, 1);
lean_dec(x_15);
x_16 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__3;
lean_ctor_set(x_10, 1, x_16);
x_17 = lean_st_ref_set(x_1, x_9, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_7);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__3;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_22);
lean_ctor_set(x_9, 6, x_25);
x_26 = lean_st_ref_set(x_1, x_9, x_11);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
x_32 = lean_ctor_get(x_9, 2);
x_33 = lean_ctor_get(x_9, 3);
x_34 = lean_ctor_get(x_9, 4);
x_35 = lean_ctor_get(x_9, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_36 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_37 = lean_ctor_get(x_10, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_38 = x_10;
} else {
 lean_dec_ref(x_10);
 x_38 = lean_box(0);
}
x_39 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__3;
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 1);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_36);
x_41 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_31);
lean_ctor_set(x_41, 2, x_32);
lean_ctor_set(x_41, 3, x_33);
lean_ctor_set(x_41, 4, x_34);
lean_ctor_set(x_41, 5, x_35);
lean_ctor_set(x_41, 6, x_40);
x_42 = lean_st_ref_set(x_1, x_41, x_11);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_7);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___boxed), 2, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 6);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg(x_10, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_10, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 6);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_10);
x_30 = lean_apply_10(x_2, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_take(x_10, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_34, 6);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
lean_ctor_set(x_35, 1, x_41);
x_42 = lean_st_ref_set(x_10, x_34, x_36);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_23);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_47);
lean_ctor_set(x_34, 6, x_50);
x_51 = lean_st_ref_set(x_10, x_34, x_36);
lean_dec(x_10);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_23);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
x_57 = lean_ctor_get(x_34, 2);
x_58 = lean_ctor_get(x_34, 3);
x_59 = lean_ctor_get(x_34, 4);
x_60 = lean_ctor_get(x_34, 5);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
x_61 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_63 = x_35;
} else {
 lean_dec_ref(x_35);
 x_63 = lean_box(0);
}
x_64 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 1);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_61);
x_66 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_56);
lean_ctor_set(x_66, 2, x_57);
lean_ctor_set(x_66, 3, x_58);
lean_ctor_set(x_66, 4, x_59);
lean_ctor_set(x_66, 5, x_60);
lean_ctor_set(x_66, 6, x_65);
x_67 = lean_st_ref_set(x_10, x_66, x_36);
lean_dec(x_10);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_23);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_10);
x_71 = !lean_is_exclusive(x_30);
if (x_71 == 0)
{
return x_30;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_30, 0);
x_73 = lean_ctor_get(x_30, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_30);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_22, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_22, 1);
lean_inc(x_76);
lean_dec(x_22);
x_77 = lean_st_ref_get(x_10, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 6);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
lean_inc(x_10);
x_82 = lean_apply_10(x_2, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_take(x_10, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_86, 6);
lean_dec(x_90);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_87, 1);
lean_dec(x_92);
x_93 = l_Lean_PersistentArray_push___rarg(x_20, x_83);
lean_ctor_set(x_87, 1, x_93);
x_94 = lean_st_ref_set(x_10, x_86, x_88);
lean_dec(x_10);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
lean_ctor_set_tag(x_94, 1);
lean_ctor_set(x_94, 0, x_75);
return x_94;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_75);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
x_100 = lean_ctor_get(x_87, 0);
lean_inc(x_100);
lean_dec(x_87);
x_101 = l_Lean_PersistentArray_push___rarg(x_20, x_83);
x_102 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_99);
lean_ctor_set(x_86, 6, x_102);
x_103 = lean_st_ref_set(x_10, x_86, x_88);
lean_dec(x_10);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
 lean_ctor_set_tag(x_106, 1);
}
lean_ctor_set(x_106, 0, x_75);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_107 = lean_ctor_get(x_86, 0);
x_108 = lean_ctor_get(x_86, 1);
x_109 = lean_ctor_get(x_86, 2);
x_110 = lean_ctor_get(x_86, 3);
x_111 = lean_ctor_get(x_86, 4);
x_112 = lean_ctor_get(x_86, 5);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_86);
x_113 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
x_114 = lean_ctor_get(x_87, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_115 = x_87;
} else {
 lean_dec_ref(x_87);
 x_115 = lean_box(0);
}
x_116 = l_Lean_PersistentArray_push___rarg(x_20, x_83);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 1);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_113);
x_118 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_118, 0, x_107);
lean_ctor_set(x_118, 1, x_108);
lean_ctor_set(x_118, 2, x_109);
lean_ctor_set(x_118, 3, x_110);
lean_ctor_set(x_118, 4, x_111);
lean_ctor_set(x_118, 5, x_112);
lean_ctor_set(x_118, 6, x_117);
x_119 = lean_st_ref_set(x_10, x_118, x_88);
lean_dec(x_10);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
 lean_ctor_set_tag(x_122, 1);
}
lean_ctor_set(x_122, 0, x_75);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_dec(x_75);
lean_dec(x_20);
lean_dec(x_10);
x_123 = !lean_is_exclusive(x_82);
if (x_123 == 0)
{
return x_82;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_82, 0);
x_125 = lean_ctor_get(x_82, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_82);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg___lambda__1), 11, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 5);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 5, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
x_24 = lean_ctor_get(x_9, 8);
x_25 = lean_ctor_get(x_9, 9);
x_26 = lean_ctor_get(x_9, 10);
x_27 = lean_ctor_get_uint8(x_9, sizeof(void*)*12);
x_28 = lean_ctor_get(x_9, 11);
x_29 = lean_ctor_get_uint8(x_9, sizeof(void*)*12 + 1);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_30 = l_Lean_replaceRef(x_1, x_21);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_17);
lean_ctor_set(x_31, 2, x_18);
lean_ctor_set(x_31, 3, x_19);
lean_ctor_set(x_31, 4, x_20);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set(x_31, 7, x_23);
lean_ctor_set(x_31, 8, x_24);
lean_ctor_set(x_31, 9, x_25);
lean_ctor_set(x_31, 10, x_26);
lean_ctor_set(x_31, 11, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*12, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*12 + 1, x_29);
x_32 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31, x_10, x_11);
lean_dec(x_31);
return x_32;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic_throwExs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected syntax ", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic_throwExs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalTactic_throwExs___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_throwExs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_inc(x_1);
x_15 = l_Lean_MessageData_ofSyntax(x_1);
x_16 = l_Lean_indentD(x_15);
x_17 = l_Lean_Elab_Tactic_evalTactic_throwExs___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__1(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_12, x_22);
lean_dec(x_12);
x_24 = lean_array_fget(x_2, x_23);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_28 = l_Lean_Elab_Tactic_SavedState_restore(x_26, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_25);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_throwExs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalTactic_throwExs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1___closed__1;
x_12 = lean_st_ref_get(x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_8, 2);
x_16 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_14, x_15, x_1);
lean_dec(x_14);
x_17 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_ctor_get(x_8, 2);
x_21 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_18, x_20, x_1);
lean_dec(x_18);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
}
static double _init_l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_9, 5);
x_13 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_10, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; double x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_18, 3);
x_22 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__1;
x_23 = 0;
x_24 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__2;
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_12);
lean_ctor_set(x_16, 1, x_27);
lean_ctor_set(x_16, 0, x_12);
x_28 = l_Lean_PersistentArray_push___rarg(x_21, x_16);
lean_ctor_set(x_18, 3, x_28);
x_29 = lean_st_ref_set(x_10, x_18, x_20);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; double x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_36 = lean_ctor_get(x_16, 1);
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
x_39 = lean_ctor_get(x_18, 2);
x_40 = lean_ctor_get(x_18, 3);
x_41 = lean_ctor_get(x_18, 4);
x_42 = lean_ctor_get(x_18, 5);
x_43 = lean_ctor_get(x_18, 6);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
x_44 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__1;
x_45 = 0;
x_46 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_47 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_float(x_47, sizeof(void*)*2, x_44);
lean_ctor_set_float(x_47, sizeof(void*)*2 + 8, x_44);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 16, x_45);
x_48 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__2;
x_49 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_14);
lean_ctor_set(x_49, 2, x_48);
lean_inc(x_12);
lean_ctor_set(x_16, 1, x_49);
lean_ctor_set(x_16, 0, x_12);
x_50 = l_Lean_PersistentArray_push___rarg(x_40, x_16);
x_51 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_51, 0, x_37);
lean_ctor_set(x_51, 1, x_38);
lean_ctor_set(x_51, 2, x_39);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_41);
lean_ctor_set(x_51, 5, x_42);
lean_ctor_set(x_51, 6, x_43);
x_52 = lean_st_ref_set(x_10, x_51, x_36);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; double x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_57 = lean_ctor_get(x_16, 0);
x_58 = lean_ctor_get(x_16, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_16);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 5);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 6);
lean_inc(x_65);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 lean_ctor_release(x_57, 6);
 x_66 = x_57;
} else {
 lean_dec_ref(x_57);
 x_66 = lean_box(0);
}
x_67 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__1;
x_68 = 0;
x_69 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_70 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set_float(x_70, sizeof(void*)*2, x_67);
lean_ctor_set_float(x_70, sizeof(void*)*2 + 8, x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 16, x_68);
x_71 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__2;
x_72 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_14);
lean_ctor_set(x_72, 2, x_71);
lean_inc(x_12);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_12);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_PersistentArray_push___rarg(x_62, x_73);
if (lean_is_scalar(x_66)) {
 x_75 = lean_alloc_ctor(0, 7, 0);
} else {
 x_75 = x_66;
}
lean_ctor_set(x_75, 0, x_59);
lean_ctor_set(x_75, 1, x_60);
lean_ctor_set(x_75, 2, x_61);
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_75, 4, x_63);
lean_ctor_set(x_75, 5, x_64);
lean_ctor_set(x_75, 6, x_65);
x_76 = lean_st_ref_set(x_10, x_75, x_58);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = lean_box(0);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_9, 5);
x_13 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_10, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; double x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_18, 3);
x_22 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__1;
x_23 = 0;
x_24 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__2;
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_12);
lean_ctor_set(x_16, 1, x_27);
lean_ctor_set(x_16, 0, x_12);
x_28 = l_Lean_PersistentArray_push___rarg(x_21, x_16);
lean_ctor_set(x_18, 3, x_28);
x_29 = lean_st_ref_set(x_10, x_18, x_20);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; double x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_36 = lean_ctor_get(x_16, 1);
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
x_39 = lean_ctor_get(x_18, 2);
x_40 = lean_ctor_get(x_18, 3);
x_41 = lean_ctor_get(x_18, 4);
x_42 = lean_ctor_get(x_18, 5);
x_43 = lean_ctor_get(x_18, 6);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
x_44 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__1;
x_45 = 0;
x_46 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_47 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_float(x_47, sizeof(void*)*2, x_44);
lean_ctor_set_float(x_47, sizeof(void*)*2 + 8, x_44);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 16, x_45);
x_48 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__2;
x_49 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_14);
lean_ctor_set(x_49, 2, x_48);
lean_inc(x_12);
lean_ctor_set(x_16, 1, x_49);
lean_ctor_set(x_16, 0, x_12);
x_50 = l_Lean_PersistentArray_push___rarg(x_40, x_16);
x_51 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_51, 0, x_37);
lean_ctor_set(x_51, 1, x_38);
lean_ctor_set(x_51, 2, x_39);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_41);
lean_ctor_set(x_51, 5, x_42);
lean_ctor_set(x_51, 6, x_43);
x_52 = lean_st_ref_set(x_10, x_51, x_36);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; double x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_57 = lean_ctor_get(x_16, 0);
x_58 = lean_ctor_get(x_16, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_16);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 5);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 6);
lean_inc(x_65);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 lean_ctor_release(x_57, 6);
 x_66 = x_57;
} else {
 lean_dec_ref(x_57);
 x_66 = lean_box(0);
}
x_67 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__1;
x_68 = 0;
x_69 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_70 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set_float(x_70, sizeof(void*)*2, x_67);
lean_ctor_set_float(x_70, sizeof(void*)*2 + 8, x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 16, x_68);
x_71 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__2;
x_72 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_14);
lean_ctor_set(x_72, 2, x_71);
lean_inc(x_12);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_12);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_PersistentArray_push___rarg(x_62, x_73);
if (lean_is_scalar(x_66)) {
 x_75 = lean_alloc_ctor(0, 7, 0);
} else {
 x_75 = x_66;
}
lean_ctor_set(x_75, 0, x_59);
lean_ctor_set(x_75, 1, x_60);
lean_ctor_set(x_75, 2, x_61);
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_75, 4, x_63);
lean_ctor_set(x_75, 5, x_64);
lean_ctor_set(x_75, 6, x_65);
x_76 = lean_st_ref_set(x_10, x_75, x_58);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = lean_box(0);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backtrack", 9, 9);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__3;
x_3 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__2;
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_1 = x_14;
x_2 = x_20;
x_11 = x_19;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_13, 4);
lean_inc(x_23);
lean_dec(x_13);
x_24 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__3(x_15, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_1 = x_14;
x_2 = x_26;
x_11 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_handleEx___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Tactic_saveState___rarg(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_ctor_set(x_15, 1, x_17);
lean_ctor_set(x_15, 0, x_1);
x_19 = lean_array_push(x_2, x_15);
x_20 = 1;
x_21 = l_Lean_Elab_Tactic_SavedState_restore(x_3, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_apply_10(x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_array_push(x_2, x_26);
x_28 = 1;
x_29 = l_Lean_Elab_Tactic_SavedState_restore(x_3, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_apply_10(x_4, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_30);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic_handleEx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic_handleEx___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_abortTacticExceptionId;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_handleEx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__2;
x_15 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Tactic_evalTactic_handleEx___lambda__1(x_3, x_2, x_1, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
lean_inc(x_3);
x_22 = l_Lean_Exception_toMessageData(x_3);
x_23 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2(x_14, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Tactic_evalTactic_handleEx___lambda__1(x_3, x_2, x_1, x_4, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = l_Lean_Elab_Tactic_evalTactic_handleEx___closed__1;
x_29 = lean_nat_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Elab_Tactic_evalTactic_handleEx___closed__2;
x_31 = lean_nat_dec_eq(x_27, x_30);
lean_dec(x_27);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_13);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_33 = l_Lean_Core_getMessageLog___rarg(x_12, x_13);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_MessageLog_toList(x_34);
lean_dec(x_34);
x_37 = lean_box(0);
x_38 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4(x_36, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Elab_Tactic_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_ctor_set(x_40, 1, x_42);
lean_ctor_set(x_40, 0, x_3);
x_44 = lean_array_push(x_2, x_40);
x_45 = 1;
x_46 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_45, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_43);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_apply_10(x_4, x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_array_push(x_2, x_51);
x_53 = 1;
x_54 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_53, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_50);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_apply_10(x_4, x_52, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_27);
lean_dec(x_3);
x_57 = 1;
x_58 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_57, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_apply_10(x_4, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_handleEx___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_evalTactic_handleEx___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_builtinIncrementalElabs;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_incrementalAttr;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__1;
x_12 = lean_st_ref_get(x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_NameSet_contains(x_14, x_1);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_free_object(x_12);
x_17 = lean_st_ref_get(x_9, x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__2;
x_22 = l_Lean_TagAttribute_hasTag(x_21, x_20, x_1);
lean_dec(x_20);
x_23 = lean_box(x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__2;
x_28 = l_Lean_TagAttribute_hasTag(x_27, x_26, x_1);
lean_dec(x_26);
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_1);
x_31 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_31);
return x_12;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = l_Lean_NameSet_contains(x_32, x_1);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_st_ref_get(x_9, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__2;
x_41 = l_Lean_TagAttribute_hasTag(x_40, x_39, x_1);
lean_dec(x_39);
x_42 = lean_box(x_41);
if (lean_is_scalar(x_38)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_38;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_1);
x_44 = lean_box(x_34);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_33);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_evalTactic_eval___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 6);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg(x_10, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_10, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 6);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_10);
x_30 = lean_apply_10(x_2, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_take(x_10, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_34, 6);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
lean_ctor_set(x_35, 1, x_41);
x_42 = lean_st_ref_set(x_10, x_34, x_36);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_23);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_47);
lean_ctor_set(x_34, 6, x_50);
x_51 = lean_st_ref_set(x_10, x_34, x_36);
lean_dec(x_10);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_23);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
x_57 = lean_ctor_get(x_34, 2);
x_58 = lean_ctor_get(x_34, 3);
x_59 = lean_ctor_get(x_34, 4);
x_60 = lean_ctor_get(x_34, 5);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
x_61 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_63 = x_35;
} else {
 lean_dec_ref(x_35);
 x_63 = lean_box(0);
}
x_64 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 1);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_61);
x_66 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_56);
lean_ctor_set(x_66, 2, x_57);
lean_ctor_set(x_66, 3, x_58);
lean_ctor_set(x_66, 4, x_59);
lean_ctor_set(x_66, 5, x_60);
lean_ctor_set(x_66, 6, x_65);
x_67 = lean_st_ref_set(x_10, x_66, x_36);
lean_dec(x_10);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_23);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_10);
x_71 = !lean_is_exclusive(x_30);
if (x_71 == 0)
{
return x_30;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_30, 0);
x_73 = lean_ctor_get(x_30, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_30);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_22, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_22, 1);
lean_inc(x_76);
lean_dec(x_22);
x_77 = lean_st_ref_get(x_10, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 6);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
lean_inc(x_10);
x_82 = lean_apply_10(x_2, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_take(x_10, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_86, 6);
lean_dec(x_90);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_87, 1);
lean_dec(x_92);
x_93 = l_Lean_PersistentArray_push___rarg(x_20, x_83);
lean_ctor_set(x_87, 1, x_93);
x_94 = lean_st_ref_set(x_10, x_86, x_88);
lean_dec(x_10);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
lean_ctor_set_tag(x_94, 1);
lean_ctor_set(x_94, 0, x_75);
return x_94;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_75);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
x_100 = lean_ctor_get(x_87, 0);
lean_inc(x_100);
lean_dec(x_87);
x_101 = l_Lean_PersistentArray_push___rarg(x_20, x_83);
x_102 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_99);
lean_ctor_set(x_86, 6, x_102);
x_103 = lean_st_ref_set(x_10, x_86, x_88);
lean_dec(x_10);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
 lean_ctor_set_tag(x_106, 1);
}
lean_ctor_set(x_106, 0, x_75);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_107 = lean_ctor_get(x_86, 0);
x_108 = lean_ctor_get(x_86, 1);
x_109 = lean_ctor_get(x_86, 2);
x_110 = lean_ctor_get(x_86, 3);
x_111 = lean_ctor_get(x_86, 4);
x_112 = lean_ctor_get(x_86, 5);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_86);
x_113 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
x_114 = lean_ctor_get(x_87, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_115 = x_87;
} else {
 lean_dec_ref(x_87);
 x_115 = lean_box(0);
}
x_116 = l_Lean_PersistentArray_push___rarg(x_20, x_83);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 1);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_113);
x_118 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_118, 0, x_107);
lean_ctor_set(x_118, 1, x_108);
lean_ctor_set(x_118, 2, x_109);
lean_ctor_set(x_118, 3, x_110);
lean_ctor_set(x_118, 4, x_111);
lean_ctor_set(x_118, 5, x_112);
lean_ctor_set(x_118, 6, x_117);
x_119 = lean_st_ref_set(x_10, x_118, x_88);
lean_dec(x_10);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
 lean_ctor_set_tag(x_122, 1);
}
lean_ctor_set(x_122, 0, x_75);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_dec(x_75);
lean_dec(x_20);
lean_dec(x_10);
x_123 = !lean_is_exclusive(x_82);
if (x_123 == 0)
{
return x_82;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_82, 0);
x_125 = lean_ctor_get(x_82, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_82);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reuse", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__1;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
x_3 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reuse stopped: guard failed at ", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_5, 8);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 8);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_5, 8, x_15);
x_16 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_23 = lean_ctor_get(x_5, 3);
x_24 = lean_ctor_get(x_5, 4);
x_25 = lean_ctor_get(x_5, 5);
x_26 = lean_ctor_get(x_5, 6);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_31 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_32 = lean_ctor_get(x_5, 7);
x_33 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_34 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
lean_inc(x_32);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_18);
lean_ctor_set(x_36, 2, x_19);
lean_ctor_set(x_36, 3, x_23);
lean_ctor_set(x_36, 4, x_24);
lean_ctor_set(x_36, 5, x_25);
lean_ctor_set(x_36, 6, x_26);
lean_ctor_set(x_36, 7, x_32);
lean_ctor_set(x_36, 8, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*9, x_20);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 1, x_21);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 2, x_22);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 3, x_27);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 4, x_28);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 5, x_29);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 6, x_30);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 7, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 8, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 9, x_34);
x_37 = lean_apply_9(x_2, x_3, x_4, x_36, x_6, x_7, x_8, x_9, x_10, x_11);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_5, 8);
lean_dec(x_42);
x_43 = lean_box(0);
x_44 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(x_1, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_12);
lean_dec(x_39);
x_45 = lean_box(0);
lean_ctor_set(x_5, 8, x_45);
x_46 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; 
x_48 = lean_ctor_get(x_5, 0);
x_49 = lean_ctor_get(x_5, 1);
x_50 = lean_ctor_get(x_5, 2);
x_51 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_52 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_53 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_54 = lean_ctor_get(x_5, 3);
x_55 = lean_ctor_get(x_5, 4);
x_56 = lean_ctor_get(x_5, 5);
x_57 = lean_ctor_get(x_5, 6);
x_58 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_59 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_60 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_61 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_62 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_63 = lean_ctor_get(x_5, 7);
x_64 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_65 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
lean_inc(x_63);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_5);
x_66 = lean_box(0);
x_67 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(x_1, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_free_object(x_12);
lean_dec(x_39);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_69, 0, x_48);
lean_ctor_set(x_69, 1, x_49);
lean_ctor_set(x_69, 2, x_50);
lean_ctor_set(x_69, 3, x_54);
lean_ctor_set(x_69, 4, x_55);
lean_ctor_set(x_69, 5, x_56);
lean_ctor_set(x_69, 6, x_57);
lean_ctor_set(x_69, 7, x_63);
lean_ctor_set(x_69, 8, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*9, x_51);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 1, x_52);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 2, x_53);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 3, x_58);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 4, x_59);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 5, x_60);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 6, x_61);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 7, x_62);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 8, x_64);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 9, x_65);
x_70 = lean_apply_9(x_2, x_3, x_4, x_69, x_6, x_7, x_8, x_9, x_10, x_11);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_71, 0, x_48);
lean_ctor_set(x_71, 1, x_49);
lean_ctor_set(x_71, 2, x_50);
lean_ctor_set(x_71, 3, x_54);
lean_ctor_set(x_71, 4, x_55);
lean_ctor_set(x_71, 5, x_56);
lean_ctor_set(x_71, 6, x_57);
lean_ctor_set(x_71, 7, x_63);
lean_ctor_set(x_71, 8, x_12);
lean_ctor_set_uint8(x_71, sizeof(void*)*9, x_51);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 1, x_52);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 2, x_53);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 3, x_58);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 4, x_59);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 5, x_60);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 6, x_61);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 7, x_62);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 8, x_64);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 9, x_65);
x_72 = lean_apply_9(x_2, x_3, x_4, x_71, x_6, x_7, x_8, x_9, x_10, x_11);
return x_72;
}
}
}
else
{
lean_free_object(x_12);
if (x_1 == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_40);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_40, 0);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_5);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_5, 8);
lean_dec(x_76);
x_77 = lean_box(0);
x_78 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(x_1, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_free_object(x_40);
lean_dec(x_39);
x_79 = lean_box(0);
lean_ctor_set(x_5, 8, x_79);
x_80 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_80;
}
else
{
lean_object* x_81; 
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_5, 8, x_40);
x_81 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; lean_object* x_100; uint8_t x_101; 
x_82 = lean_ctor_get(x_5, 0);
x_83 = lean_ctor_get(x_5, 1);
x_84 = lean_ctor_get(x_5, 2);
x_85 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_86 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_87 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_88 = lean_ctor_get(x_5, 3);
x_89 = lean_ctor_get(x_5, 4);
x_90 = lean_ctor_get(x_5, 5);
x_91 = lean_ctor_get(x_5, 6);
x_92 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_93 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_94 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_95 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_96 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_97 = lean_ctor_get(x_5, 7);
x_98 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_99 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
lean_inc(x_97);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_5);
x_100 = lean_box(0);
x_101 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(x_1, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_40);
lean_dec(x_39);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_103, 0, x_82);
lean_ctor_set(x_103, 1, x_83);
lean_ctor_set(x_103, 2, x_84);
lean_ctor_set(x_103, 3, x_88);
lean_ctor_set(x_103, 4, x_89);
lean_ctor_set(x_103, 5, x_90);
lean_ctor_set(x_103, 6, x_91);
lean_ctor_set(x_103, 7, x_97);
lean_ctor_set(x_103, 8, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*9, x_85);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 1, x_86);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 2, x_87);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 3, x_92);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 4, x_93);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 5, x_94);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 6, x_95);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 7, x_96);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 8, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 9, x_99);
x_104 = lean_apply_9(x_2, x_3, x_4, x_103, x_6, x_7, x_8, x_9, x_10, x_11);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_ctor_set(x_40, 0, x_39);
x_105 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_105, 0, x_82);
lean_ctor_set(x_105, 1, x_83);
lean_ctor_set(x_105, 2, x_84);
lean_ctor_set(x_105, 3, x_88);
lean_ctor_set(x_105, 4, x_89);
lean_ctor_set(x_105, 5, x_90);
lean_ctor_set(x_105, 6, x_91);
lean_ctor_set(x_105, 7, x_97);
lean_ctor_set(x_105, 8, x_40);
lean_ctor_set_uint8(x_105, sizeof(void*)*9, x_85);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 1, x_86);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 2, x_87);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 3, x_92);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 4, x_93);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 5, x_94);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 6, x_95);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 7, x_96);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 8, x_98);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 9, x_99);
x_106 = lean_apply_9(x_2, x_3, x_4, x_105, x_6, x_7, x_8, x_9, x_10, x_11);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_40);
x_107 = lean_ctor_get(x_5, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_5, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_5, 2);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_111 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_112 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_113 = lean_ctor_get(x_5, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_5, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_5, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_5, 6);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_118 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_119 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_120 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_121 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_122 = lean_ctor_get(x_5, 7);
lean_inc(x_122);
x_123 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_124 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 x_125 = x_5;
} else {
 lean_dec_ref(x_5);
 x_125 = lean_box(0);
}
x_126 = lean_box(0);
x_127 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(x_1, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_39);
x_128 = lean_box(0);
if (lean_is_scalar(x_125)) {
 x_129 = lean_alloc_ctor(0, 9, 10);
} else {
 x_129 = x_125;
}
lean_ctor_set(x_129, 0, x_107);
lean_ctor_set(x_129, 1, x_108);
lean_ctor_set(x_129, 2, x_109);
lean_ctor_set(x_129, 3, x_113);
lean_ctor_set(x_129, 4, x_114);
lean_ctor_set(x_129, 5, x_115);
lean_ctor_set(x_129, 6, x_116);
lean_ctor_set(x_129, 7, x_122);
lean_ctor_set(x_129, 8, x_128);
lean_ctor_set_uint8(x_129, sizeof(void*)*9, x_110);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 1, x_111);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 2, x_112);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 3, x_117);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 4, x_118);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 5, x_119);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 6, x_120);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 7, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 8, x_123);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 9, x_124);
x_130 = lean_apply_9(x_2, x_3, x_4, x_129, x_6, x_7, x_8, x_9, x_10, x_11);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_39);
if (lean_is_scalar(x_125)) {
 x_132 = lean_alloc_ctor(0, 9, 10);
} else {
 x_132 = x_125;
}
lean_ctor_set(x_132, 0, x_107);
lean_ctor_set(x_132, 1, x_108);
lean_ctor_set(x_132, 2, x_109);
lean_ctor_set(x_132, 3, x_113);
lean_ctor_set(x_132, 4, x_114);
lean_ctor_set(x_132, 5, x_115);
lean_ctor_set(x_132, 6, x_116);
lean_ctor_set(x_132, 7, x_122);
lean_ctor_set(x_132, 8, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*9, x_110);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 1, x_111);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 2, x_112);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 3, x_117);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 4, x_118);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 5, x_119);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 6, x_120);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 7, x_121);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 8, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 9, x_124);
x_133 = lean_apply_9(x_2, x_3, x_4, x_132, x_6, x_7, x_8, x_9, x_10, x_11);
return x_133;
}
}
}
else
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_5);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_5, 8);
lean_dec(x_135);
x_136 = !lean_is_exclusive(x_40);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_143; 
x_137 = lean_ctor_get(x_40, 0);
x_138 = lean_ctor_get(x_9, 2);
lean_inc(x_138);
x_139 = lean_box(x_1);
x_140 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1___boxed), 2, 1);
lean_closure_set(x_140, 0, x_139);
x_141 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__3;
x_142 = 0;
x_143 = l_Lean_KVMap_getBool(x_138, x_141, x_142);
lean_dec(x_138);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_140);
lean_dec(x_137);
x_144 = lean_box(0);
x_145 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(x_1, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_free_object(x_40);
lean_dec(x_39);
x_146 = lean_box(0);
lean_ctor_set(x_5, 8, x_146);
x_147 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_147;
}
else
{
lean_object* x_148; 
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_5, 8, x_40);
x_148 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_149 = lean_ctor_get(x_137, 0);
lean_inc(x_149);
lean_dec(x_137);
x_150 = lean_box(0);
x_151 = lean_unsigned_to_nat(0u);
x_152 = l_Lean_Syntax_formatStxAux(x_150, x_142, x_151, x_149);
x_153 = l_Std_Format_defWidth;
x_154 = lean_format_pretty(x_152, x_153, x_151, x_151);
x_155 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__4;
x_156 = lean_string_append(x_155, x_154);
lean_dec(x_154);
x_157 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_158 = lean_string_append(x_156, x_157);
x_159 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__2___boxed), 2, 1);
lean_closure_set(x_159, 0, x_140);
x_160 = lean_dbg_trace(x_158, x_159);
x_161 = lean_unbox(x_160);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; 
lean_free_object(x_40);
lean_dec(x_39);
lean_ctor_set(x_5, 8, x_150);
x_162 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_162;
}
else
{
lean_object* x_163; 
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_5, 8, x_40);
x_163 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; 
x_164 = lean_ctor_get(x_40, 0);
lean_inc(x_164);
lean_dec(x_40);
x_165 = lean_ctor_get(x_9, 2);
lean_inc(x_165);
x_166 = lean_box(x_1);
x_167 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1___boxed), 2, 1);
lean_closure_set(x_167, 0, x_166);
x_168 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__3;
x_169 = 0;
x_170 = l_Lean_KVMap_getBool(x_165, x_168, x_169);
lean_dec(x_165);
if (x_170 == 0)
{
lean_object* x_171; uint8_t x_172; 
lean_dec(x_167);
lean_dec(x_164);
x_171 = lean_box(0);
x_172 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(x_1, x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_39);
x_173 = lean_box(0);
lean_ctor_set(x_5, 8, x_173);
x_174 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_39);
lean_ctor_set(x_5, 8, x_175);
x_176 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_177 = lean_ctor_get(x_164, 0);
lean_inc(x_177);
lean_dec(x_164);
x_178 = lean_box(0);
x_179 = lean_unsigned_to_nat(0u);
x_180 = l_Lean_Syntax_formatStxAux(x_178, x_169, x_179, x_177);
x_181 = l_Std_Format_defWidth;
x_182 = lean_format_pretty(x_180, x_181, x_179, x_179);
x_183 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__4;
x_184 = lean_string_append(x_183, x_182);
lean_dec(x_182);
x_185 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_186 = lean_string_append(x_184, x_185);
x_187 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__2___boxed), 2, 1);
lean_closure_set(x_187, 0, x_167);
x_188 = lean_dbg_trace(x_186, x_187);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; 
lean_dec(x_39);
lean_ctor_set(x_5, 8, x_178);
x_190 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_39);
lean_ctor_set(x_5, 8, x_191);
x_192 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_192;
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; lean_object* x_208; uint8_t x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_218; 
x_193 = lean_ctor_get(x_5, 0);
x_194 = lean_ctor_get(x_5, 1);
x_195 = lean_ctor_get(x_5, 2);
x_196 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_197 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_198 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_199 = lean_ctor_get(x_5, 3);
x_200 = lean_ctor_get(x_5, 4);
x_201 = lean_ctor_get(x_5, 5);
x_202 = lean_ctor_get(x_5, 6);
x_203 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_204 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_205 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_206 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_207 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_208 = lean_ctor_get(x_5, 7);
x_209 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_210 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
lean_inc(x_208);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_5);
x_211 = lean_ctor_get(x_40, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_212 = x_40;
} else {
 lean_dec_ref(x_40);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_9, 2);
lean_inc(x_213);
x_214 = lean_box(x_1);
x_215 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1___boxed), 2, 1);
lean_closure_set(x_215, 0, x_214);
x_216 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__3;
x_217 = 0;
x_218 = l_Lean_KVMap_getBool(x_213, x_216, x_217);
lean_dec(x_213);
if (x_218 == 0)
{
lean_object* x_219; uint8_t x_220; 
lean_dec(x_215);
lean_dec(x_211);
x_219 = lean_box(0);
x_220 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(x_1, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_212);
lean_dec(x_39);
x_221 = lean_box(0);
x_222 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_222, 0, x_193);
lean_ctor_set(x_222, 1, x_194);
lean_ctor_set(x_222, 2, x_195);
lean_ctor_set(x_222, 3, x_199);
lean_ctor_set(x_222, 4, x_200);
lean_ctor_set(x_222, 5, x_201);
lean_ctor_set(x_222, 6, x_202);
lean_ctor_set(x_222, 7, x_208);
lean_ctor_set(x_222, 8, x_221);
lean_ctor_set_uint8(x_222, sizeof(void*)*9, x_196);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 1, x_197);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 2, x_198);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 3, x_203);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 4, x_204);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 5, x_205);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 6, x_206);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 7, x_207);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 8, x_209);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 9, x_210);
x_223 = lean_apply_9(x_2, x_3, x_4, x_222, x_6, x_7, x_8, x_9, x_10, x_11);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
if (lean_is_scalar(x_212)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_212;
}
lean_ctor_set(x_224, 0, x_39);
x_225 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_225, 0, x_193);
lean_ctor_set(x_225, 1, x_194);
lean_ctor_set(x_225, 2, x_195);
lean_ctor_set(x_225, 3, x_199);
lean_ctor_set(x_225, 4, x_200);
lean_ctor_set(x_225, 5, x_201);
lean_ctor_set(x_225, 6, x_202);
lean_ctor_set(x_225, 7, x_208);
lean_ctor_set(x_225, 8, x_224);
lean_ctor_set_uint8(x_225, sizeof(void*)*9, x_196);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 1, x_197);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 2, x_198);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 3, x_203);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 4, x_204);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 5, x_205);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 6, x_206);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 7, x_207);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 8, x_209);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 9, x_210);
x_226 = lean_apply_9(x_2, x_3, x_4, x_225, x_6, x_7, x_8, x_9, x_10, x_11);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_227 = lean_ctor_get(x_211, 0);
lean_inc(x_227);
lean_dec(x_211);
x_228 = lean_box(0);
x_229 = lean_unsigned_to_nat(0u);
x_230 = l_Lean_Syntax_formatStxAux(x_228, x_217, x_229, x_227);
x_231 = l_Std_Format_defWidth;
x_232 = lean_format_pretty(x_230, x_231, x_229, x_229);
x_233 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__4;
x_234 = lean_string_append(x_233, x_232);
lean_dec(x_232);
x_235 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_236 = lean_string_append(x_234, x_235);
x_237 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__2___boxed), 2, 1);
lean_closure_set(x_237, 0, x_215);
x_238 = lean_dbg_trace(x_236, x_237);
x_239 = lean_unbox(x_238);
lean_dec(x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_212);
lean_dec(x_39);
x_240 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_240, 0, x_193);
lean_ctor_set(x_240, 1, x_194);
lean_ctor_set(x_240, 2, x_195);
lean_ctor_set(x_240, 3, x_199);
lean_ctor_set(x_240, 4, x_200);
lean_ctor_set(x_240, 5, x_201);
lean_ctor_set(x_240, 6, x_202);
lean_ctor_set(x_240, 7, x_208);
lean_ctor_set(x_240, 8, x_228);
lean_ctor_set_uint8(x_240, sizeof(void*)*9, x_196);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 1, x_197);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 2, x_198);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 3, x_203);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 4, x_204);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 5, x_205);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 6, x_206);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 7, x_207);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 8, x_209);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 9, x_210);
x_241 = lean_apply_9(x_2, x_3, x_4, x_240, x_6, x_7, x_8, x_9, x_10, x_11);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
if (lean_is_scalar(x_212)) {
 x_242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_242 = x_212;
}
lean_ctor_set(x_242, 0, x_39);
x_243 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_243, 0, x_193);
lean_ctor_set(x_243, 1, x_194);
lean_ctor_set(x_243, 2, x_195);
lean_ctor_set(x_243, 3, x_199);
lean_ctor_set(x_243, 4, x_200);
lean_ctor_set(x_243, 5, x_201);
lean_ctor_set(x_243, 6, x_202);
lean_ctor_set(x_243, 7, x_208);
lean_ctor_set(x_243, 8, x_242);
lean_ctor_set_uint8(x_243, sizeof(void*)*9, x_196);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 1, x_197);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 2, x_198);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 3, x_203);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 4, x_204);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 5, x_205);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 6, x_206);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 7, x_207);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 8, x_209);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 9, x_210);
x_244 = lean_apply_9(x_2, x_3, x_4, x_243, x_6, x_7, x_8, x_9, x_10, x_11);
return x_244;
}
}
}
}
}
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_12, 0);
lean_inc(x_245);
lean_dec(x_12);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_258; uint8_t x_259; uint8_t x_260; uint8_t x_261; lean_object* x_262; uint8_t x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_247 = lean_ctor_get(x_5, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_5, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_5, 2);
lean_inc(x_249);
x_250 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_251 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_252 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_253 = lean_ctor_get(x_5, 3);
lean_inc(x_253);
x_254 = lean_ctor_get(x_5, 4);
lean_inc(x_254);
x_255 = lean_ctor_get(x_5, 5);
lean_inc(x_255);
x_256 = lean_ctor_get(x_5, 6);
lean_inc(x_256);
x_257 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_258 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_259 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_260 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_261 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_262 = lean_ctor_get(x_5, 7);
lean_inc(x_262);
x_263 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_264 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 x_265 = x_5;
} else {
 lean_dec_ref(x_5);
 x_265 = lean_box(0);
}
x_266 = lean_box(0);
x_267 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(x_1, x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_245);
x_268 = lean_box(0);
if (lean_is_scalar(x_265)) {
 x_269 = lean_alloc_ctor(0, 9, 10);
} else {
 x_269 = x_265;
}
lean_ctor_set(x_269, 0, x_247);
lean_ctor_set(x_269, 1, x_248);
lean_ctor_set(x_269, 2, x_249);
lean_ctor_set(x_269, 3, x_253);
lean_ctor_set(x_269, 4, x_254);
lean_ctor_set(x_269, 5, x_255);
lean_ctor_set(x_269, 6, x_256);
lean_ctor_set(x_269, 7, x_262);
lean_ctor_set(x_269, 8, x_268);
lean_ctor_set_uint8(x_269, sizeof(void*)*9, x_250);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 1, x_251);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 2, x_252);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 3, x_257);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 4, x_258);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 5, x_259);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 6, x_260);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 7, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 8, x_263);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 9, x_264);
x_270 = lean_apply_9(x_2, x_3, x_4, x_269, x_6, x_7, x_8, x_9, x_10, x_11);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_245);
if (lean_is_scalar(x_265)) {
 x_272 = lean_alloc_ctor(0, 9, 10);
} else {
 x_272 = x_265;
}
lean_ctor_set(x_272, 0, x_247);
lean_ctor_set(x_272, 1, x_248);
lean_ctor_set(x_272, 2, x_249);
lean_ctor_set(x_272, 3, x_253);
lean_ctor_set(x_272, 4, x_254);
lean_ctor_set(x_272, 5, x_255);
lean_ctor_set(x_272, 6, x_256);
lean_ctor_set(x_272, 7, x_262);
lean_ctor_set(x_272, 8, x_271);
lean_ctor_set_uint8(x_272, sizeof(void*)*9, x_250);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 1, x_251);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 2, x_252);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 3, x_257);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 4, x_258);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 5, x_259);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 6, x_260);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 7, x_261);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 8, x_263);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 9, x_264);
x_273 = lean_apply_9(x_2, x_3, x_4, x_272, x_6, x_7, x_8, x_9, x_10, x_11);
return x_273;
}
}
else
{
if (x_1 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; uint8_t x_286; uint8_t x_287; uint8_t x_288; uint8_t x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_274 = x_246;
} else {
 lean_dec_ref(x_246);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_5, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_5, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_5, 2);
lean_inc(x_277);
x_278 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_279 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_280 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_281 = lean_ctor_get(x_5, 3);
lean_inc(x_281);
x_282 = lean_ctor_get(x_5, 4);
lean_inc(x_282);
x_283 = lean_ctor_get(x_5, 5);
lean_inc(x_283);
x_284 = lean_ctor_get(x_5, 6);
lean_inc(x_284);
x_285 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_286 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_287 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_288 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_289 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_290 = lean_ctor_get(x_5, 7);
lean_inc(x_290);
x_291 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_292 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 x_293 = x_5;
} else {
 lean_dec_ref(x_5);
 x_293 = lean_box(0);
}
x_294 = lean_box(0);
x_295 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(x_1, x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_274);
lean_dec(x_245);
x_296 = lean_box(0);
if (lean_is_scalar(x_293)) {
 x_297 = lean_alloc_ctor(0, 9, 10);
} else {
 x_297 = x_293;
}
lean_ctor_set(x_297, 0, x_275);
lean_ctor_set(x_297, 1, x_276);
lean_ctor_set(x_297, 2, x_277);
lean_ctor_set(x_297, 3, x_281);
lean_ctor_set(x_297, 4, x_282);
lean_ctor_set(x_297, 5, x_283);
lean_ctor_set(x_297, 6, x_284);
lean_ctor_set(x_297, 7, x_290);
lean_ctor_set(x_297, 8, x_296);
lean_ctor_set_uint8(x_297, sizeof(void*)*9, x_278);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 1, x_279);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 2, x_280);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 3, x_285);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 4, x_286);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 5, x_287);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 6, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 7, x_289);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 8, x_291);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 9, x_292);
x_298 = lean_apply_9(x_2, x_3, x_4, x_297, x_6, x_7, x_8, x_9, x_10, x_11);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
if (lean_is_scalar(x_274)) {
 x_299 = lean_alloc_ctor(1, 1, 0);
} else {
 x_299 = x_274;
}
lean_ctor_set(x_299, 0, x_245);
if (lean_is_scalar(x_293)) {
 x_300 = lean_alloc_ctor(0, 9, 10);
} else {
 x_300 = x_293;
}
lean_ctor_set(x_300, 0, x_275);
lean_ctor_set(x_300, 1, x_276);
lean_ctor_set(x_300, 2, x_277);
lean_ctor_set(x_300, 3, x_281);
lean_ctor_set(x_300, 4, x_282);
lean_ctor_set(x_300, 5, x_283);
lean_ctor_set(x_300, 6, x_284);
lean_ctor_set(x_300, 7, x_290);
lean_ctor_set(x_300, 8, x_299);
lean_ctor_set_uint8(x_300, sizeof(void*)*9, x_278);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 1, x_279);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 2, x_280);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 3, x_285);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 4, x_286);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 5, x_287);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 6, x_288);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 7, x_289);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 8, x_291);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 9, x_292);
x_301 = lean_apply_9(x_2, x_3, x_4, x_300, x_6, x_7, x_8, x_9, x_10, x_11);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; uint8_t x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; uint8_t x_313; uint8_t x_314; uint8_t x_315; uint8_t x_316; lean_object* x_317; uint8_t x_318; uint8_t x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_328; 
x_302 = lean_ctor_get(x_5, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_5, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_5, 2);
lean_inc(x_304);
x_305 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_306 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_307 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_308 = lean_ctor_get(x_5, 3);
lean_inc(x_308);
x_309 = lean_ctor_get(x_5, 4);
lean_inc(x_309);
x_310 = lean_ctor_get(x_5, 5);
lean_inc(x_310);
x_311 = lean_ctor_get(x_5, 6);
lean_inc(x_311);
x_312 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_313 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_314 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_315 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_316 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_317 = lean_ctor_get(x_5, 7);
lean_inc(x_317);
x_318 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_319 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 x_320 = x_5;
} else {
 lean_dec_ref(x_5);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_246, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_322 = x_246;
} else {
 lean_dec_ref(x_246);
 x_322 = lean_box(0);
}
x_323 = lean_ctor_get(x_9, 2);
lean_inc(x_323);
x_324 = lean_box(x_1);
x_325 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1___boxed), 2, 1);
lean_closure_set(x_325, 0, x_324);
x_326 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__3;
x_327 = 0;
x_328 = l_Lean_KVMap_getBool(x_323, x_326, x_327);
lean_dec(x_323);
if (x_328 == 0)
{
lean_object* x_329; uint8_t x_330; 
lean_dec(x_325);
lean_dec(x_321);
x_329 = lean_box(0);
x_330 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(x_1, x_329);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_322);
lean_dec(x_245);
x_331 = lean_box(0);
if (lean_is_scalar(x_320)) {
 x_332 = lean_alloc_ctor(0, 9, 10);
} else {
 x_332 = x_320;
}
lean_ctor_set(x_332, 0, x_302);
lean_ctor_set(x_332, 1, x_303);
lean_ctor_set(x_332, 2, x_304);
lean_ctor_set(x_332, 3, x_308);
lean_ctor_set(x_332, 4, x_309);
lean_ctor_set(x_332, 5, x_310);
lean_ctor_set(x_332, 6, x_311);
lean_ctor_set(x_332, 7, x_317);
lean_ctor_set(x_332, 8, x_331);
lean_ctor_set_uint8(x_332, sizeof(void*)*9, x_305);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 1, x_306);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 2, x_307);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 3, x_312);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 4, x_313);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 5, x_314);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 6, x_315);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 7, x_316);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 8, x_318);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 9, x_319);
x_333 = lean_apply_9(x_2, x_3, x_4, x_332, x_6, x_7, x_8, x_9, x_10, x_11);
return x_333;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
if (lean_is_scalar(x_322)) {
 x_334 = lean_alloc_ctor(1, 1, 0);
} else {
 x_334 = x_322;
}
lean_ctor_set(x_334, 0, x_245);
if (lean_is_scalar(x_320)) {
 x_335 = lean_alloc_ctor(0, 9, 10);
} else {
 x_335 = x_320;
}
lean_ctor_set(x_335, 0, x_302);
lean_ctor_set(x_335, 1, x_303);
lean_ctor_set(x_335, 2, x_304);
lean_ctor_set(x_335, 3, x_308);
lean_ctor_set(x_335, 4, x_309);
lean_ctor_set(x_335, 5, x_310);
lean_ctor_set(x_335, 6, x_311);
lean_ctor_set(x_335, 7, x_317);
lean_ctor_set(x_335, 8, x_334);
lean_ctor_set_uint8(x_335, sizeof(void*)*9, x_305);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 1, x_306);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 2, x_307);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 3, x_312);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 4, x_313);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 5, x_314);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 6, x_315);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 7, x_316);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 8, x_318);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 9, x_319);
x_336 = lean_apply_9(x_2, x_3, x_4, x_335, x_6, x_7, x_8, x_9, x_10, x_11);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_337 = lean_ctor_get(x_321, 0);
lean_inc(x_337);
lean_dec(x_321);
x_338 = lean_box(0);
x_339 = lean_unsigned_to_nat(0u);
x_340 = l_Lean_Syntax_formatStxAux(x_338, x_327, x_339, x_337);
x_341 = l_Std_Format_defWidth;
x_342 = lean_format_pretty(x_340, x_341, x_339, x_339);
x_343 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__4;
x_344 = lean_string_append(x_343, x_342);
lean_dec(x_342);
x_345 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_346 = lean_string_append(x_344, x_345);
x_347 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__2___boxed), 2, 1);
lean_closure_set(x_347, 0, x_325);
x_348 = lean_dbg_trace(x_346, x_347);
x_349 = lean_unbox(x_348);
lean_dec(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_322);
lean_dec(x_245);
if (lean_is_scalar(x_320)) {
 x_350 = lean_alloc_ctor(0, 9, 10);
} else {
 x_350 = x_320;
}
lean_ctor_set(x_350, 0, x_302);
lean_ctor_set(x_350, 1, x_303);
lean_ctor_set(x_350, 2, x_304);
lean_ctor_set(x_350, 3, x_308);
lean_ctor_set(x_350, 4, x_309);
lean_ctor_set(x_350, 5, x_310);
lean_ctor_set(x_350, 6, x_311);
lean_ctor_set(x_350, 7, x_317);
lean_ctor_set(x_350, 8, x_338);
lean_ctor_set_uint8(x_350, sizeof(void*)*9, x_305);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 1, x_306);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 2, x_307);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 3, x_312);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 4, x_313);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 5, x_314);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 6, x_315);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 7, x_316);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 8, x_318);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 9, x_319);
x_351 = lean_apply_9(x_2, x_3, x_4, x_350, x_6, x_7, x_8, x_9, x_10, x_11);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
if (lean_is_scalar(x_322)) {
 x_352 = lean_alloc_ctor(1, 1, 0);
} else {
 x_352 = x_322;
}
lean_ctor_set(x_352, 0, x_245);
if (lean_is_scalar(x_320)) {
 x_353 = lean_alloc_ctor(0, 9, 10);
} else {
 x_353 = x_320;
}
lean_ctor_set(x_353, 0, x_302);
lean_ctor_set(x_353, 1, x_303);
lean_ctor_set(x_353, 2, x_304);
lean_ctor_set(x_353, 3, x_308);
lean_ctor_set(x_353, 4, x_309);
lean_ctor_set(x_353, 5, x_310);
lean_ctor_set(x_353, 6, x_311);
lean_ctor_set(x_353, 7, x_317);
lean_ctor_set(x_353, 8, x_352);
lean_ctor_set_uint8(x_353, sizeof(void*)*9, x_305);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 1, x_306);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 2, x_307);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 3, x_312);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 4, x_313);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 5, x_314);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 6, x_315);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 7, x_316);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 8, x_318);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 9, x_319);
x_354 = lean_apply_9(x_2, x_3, x_4, x_353, x_6, x_7, x_8, x_9, x_10, x_11);
return x_354;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_eval___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Elab_Tactic_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_1);
x_20 = lean_array_push(x_2, x_16);
x_21 = 1;
lean_inc(x_3);
x_22 = l_Lean_Elab_Tactic_SavedState_restore(x_3, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Elab_Tactic_evalTactic_eval(x_4, x_3, x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_array_push(x_2, x_27);
x_29 = 1;
lean_inc(x_3);
x_30 = l_Lean_Elab_Tactic_SavedState_restore(x_3, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Elab_Tactic_evalTactic_eval(x_4, x_3, x_5, x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_eval___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
lean_ctor_set(x_4, 0, x_1);
x_15 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg___lambda__1), 11, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_evalTactic_eval___spec__2(x_3, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_2, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg___lambda__1), 11, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_evalTactic_eval___spec__2(x_3, x_25, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = l_Lean_Elab_Tactic_evalTactic_throwExs(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_17 = x_3;
} else {
 lean_dec_ref(x_3);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_19);
x_74 = l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_15, 1);
lean_inc(x_77);
lean_dec(x_15);
lean_inc(x_1);
x_78 = lean_apply_1(x_77, x_1);
lean_inc(x_1);
x_79 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic_eval___lambda__2), 12, 3);
lean_closure_set(x_79, 0, x_19);
lean_closure_set(x_79, 1, x_1);
lean_closure_set(x_79, 2, x_78);
x_80 = lean_unbox(x_75);
lean_dec(x_75);
if (x_80 == 0)
{
uint8_t x_81; lean_object* x_82; 
x_81 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_82 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3(x_81, x_79, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_20 = x_83;
x_21 = x_84;
goto block_73;
}
}
else
{
uint8_t x_85; lean_object* x_86; 
x_85 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_86 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3(x_85, x_79, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_76);
if (lean_obj_tag(x_86) == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_20 = x_87;
x_21 = x_88;
goto block_73;
}
}
block_73:
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isInterrupt(x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Exception_isRuntime(x_20);
if (x_23 == 0)
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_17);
x_24 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__2;
x_25 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Tactic_evalTactic_eval___lambda__1(x_20, x_4, x_2, x_1, x_16, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
lean_inc(x_20);
x_32 = l_Lean_Exception_toMessageData(x_20);
x_33 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2(x_24, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Elab_Tactic_evalTactic_eval___lambda__1(x_20, x_4, x_2, x_1, x_16, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
lean_dec(x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
x_38 = l_Lean_Elab_Tactic_evalTactic_handleEx___closed__1;
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Elab_Tactic_evalTactic_handleEx___closed__2;
x_41 = lean_nat_dec_eq(x_37, x_40);
lean_dec(x_37);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_17)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_17;
}
lean_ctor_set(x_42, 0, x_20);
lean_ctor_set(x_42, 1, x_21);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_17);
x_43 = l_Lean_Core_getMessageLog___rarg(x_12, x_21);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_MessageLog_toList(x_44);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4(x_46, x_47, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_45);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Elab_Tactic_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_49);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_ctor_set(x_50, 1, x_52);
lean_ctor_set(x_50, 0, x_20);
x_54 = lean_array_push(x_4, x_50);
x_55 = 1;
lean_inc(x_2);
x_56 = l_Lean_Elab_Tactic_SavedState_restore(x_2, x_55, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_53);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_3 = x_16;
x_4 = x_54;
x_13 = x_57;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_50);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_20);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_array_push(x_4, x_61);
x_63 = 1;
lean_inc(x_2);
x_64 = l_Lean_Elab_Tactic_SavedState_restore(x_2, x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_60);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_3 = x_16;
x_4 = x_62;
x_13 = x_65;
goto _start;
}
}
}
else
{
uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_37);
lean_dec(x_20);
lean_dec(x_17);
x_67 = 1;
lean_inc(x_2);
x_68 = l_Lean_Elab_Tactic_SavedState_restore(x_2, x_67, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_3 = x_16;
x_13 = x_69;
goto _start;
}
}
}
else
{
lean_object* x_71; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_17)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_17;
}
lean_ctor_set(x_71, 0, x_20);
lean_ctor_set(x_71, 1, x_21);
return x_71;
}
}
else
{
lean_object* x_72; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_17)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_17;
}
lean_ctor_set(x_72, 0, x_20);
lean_ctor_set(x_72, 1, x_21);
return x_72;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_eval___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_evalTactic_eval___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_15);
x_17 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_1 = x_14;
x_10 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_16);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2(x_15, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_1 = x_14;
x_10 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 5);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 5, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__4(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
x_24 = lean_ctor_get(x_9, 8);
x_25 = lean_ctor_get(x_9, 9);
x_26 = lean_ctor_get(x_9, 10);
x_27 = lean_ctor_get_uint8(x_9, sizeof(void*)*12);
x_28 = lean_ctor_get(x_9, 11);
x_29 = lean_ctor_get_uint8(x_9, sizeof(void*)*12 + 1);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_30 = l_Lean_replaceRef(x_1, x_21);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_17);
lean_ctor_set(x_31, 2, x_18);
lean_ctor_set(x_31, 3, x_19);
lean_ctor_set(x_31, 4, x_20);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set(x_31, 7, x_23);
lean_ctor_set(x_31, 8, x_24);
lean_ctor_set(x_31, 9, x_25);
lean_ctor_set(x_31, 10, x_26);
lean_ctor_set(x_31, 11, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*12, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*12 + 1, x_29);
x_32 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__4(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31, x_10, x_11);
lean_dec(x_31);
return x_32;
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__2;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalTactic_handleEx___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_16);
lean_dec(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_20, x_3, x_16);
lean_dec(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_22);
lean_dec(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_27, x_3, x_22);
lean_dec(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_34, x_3, x_31);
lean_dec(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_40, x_3, x_36);
lean_dec(x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Environment_contains(x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_8, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 7);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 10);
lean_inc(x_20);
lean_inc(x_14);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_21, 0, x_14);
lean_inc(x_18);
x_22 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed), 3, 1);
lean_closure_set(x_22, 0, x_18);
lean_inc(x_14);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_23, 0, x_14);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_14);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_24, 0, x_14);
lean_closure_set(x_24, 1, x_18);
lean_closure_set(x_24, 2, x_19);
lean_inc(x_14);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_25, 0, x_14);
lean_closure_set(x_25, 1, x_18);
lean_closure_set(x_25, 2, x_19);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_26, 4, x_25);
x_27 = lean_st_ref_get(x_9, x_13);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_environment_main_module(x_14);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_20);
lean_ctor_set(x_33, 3, x_15);
lean_ctor_set(x_33, 4, x_16);
lean_ctor_set(x_33, 5, x_17);
x_34 = lean_box(0);
lean_ctor_set(x_27, 1, x_34);
lean_ctor_set(x_27, 0, x_31);
x_35 = lean_apply_2(x_1, x_33, x_27);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_st_ref_take(x_9, x_30);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_43 = lean_ctor_get(x_40, 1);
lean_dec(x_43);
lean_ctor_set(x_40, 1, x_38);
x_44 = lean_st_ref_set(x_9, x_40, x_41);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = l_List_reverse___rarg(x_46);
x_48 = l_List_forM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__2(x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_8);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_36);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_36);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_53 = lean_ctor_get(x_40, 0);
x_54 = lean_ctor_get(x_40, 2);
x_55 = lean_ctor_get(x_40, 3);
x_56 = lean_ctor_get(x_40, 4);
x_57 = lean_ctor_get(x_40, 5);
x_58 = lean_ctor_get(x_40, 6);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_40);
x_59 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_38);
lean_ctor_set(x_59, 2, x_54);
lean_ctor_set(x_59, 3, x_55);
lean_ctor_set(x_59, 4, x_56);
lean_ctor_set(x_59, 5, x_57);
lean_ctor_set(x_59, 6, x_58);
x_60 = lean_st_ref_set(x_9, x_59, x_41);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_ctor_get(x_37, 1);
lean_inc(x_62);
lean_dec(x_37);
x_63 = l_List_reverse___rarg(x_62);
x_64 = l_List_forM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__2(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_61);
lean_dec(x_8);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_36);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_35, 0);
lean_inc(x_68);
lean_dec(x_35);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_maxRecDepthErrorMessage;
x_72 = lean_string_dec_eq(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_70);
x_74 = l_Lean_MessageData_ofFormat(x_73);
x_75 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__3(x_69, x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_69);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_70);
x_76 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5(x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_8);
return x_76;
}
}
else
{
lean_object* x_77; 
lean_dec(x_8);
x_77 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___rarg(x_30);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_27, 0);
x_79 = lean_ctor_get(x_27, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_27);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_environment_main_module(x_14);
x_82 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_82, 0, x_26);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_20);
lean_ctor_set(x_82, 3, x_15);
lean_ctor_set(x_82, 4, x_16);
lean_ctor_set(x_82, 5, x_17);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_apply_2(x_1, x_82, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_st_ref_take(x_9, x_79);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 5);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 6);
lean_inc(x_97);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 lean_ctor_release(x_90, 3);
 lean_ctor_release(x_90, 4);
 lean_ctor_release(x_90, 5);
 lean_ctor_release(x_90, 6);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 7, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_92);
lean_ctor_set(x_99, 1, x_88);
lean_ctor_set(x_99, 2, x_93);
lean_ctor_set(x_99, 3, x_94);
lean_ctor_set(x_99, 4, x_95);
lean_ctor_set(x_99, 5, x_96);
lean_ctor_set(x_99, 6, x_97);
x_100 = lean_st_ref_set(x_9, x_99, x_91);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = l_List_reverse___rarg(x_102);
x_104 = l_List_forM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__2(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_101);
lean_dec(x_8);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_86);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_85, 0);
lean_inc(x_108);
lean_dec(x_85);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_maxRecDepthErrorMessage;
x_112 = lean_string_dec_eq(x_110, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_113, 0, x_110);
x_114 = l_Lean_MessageData_ofFormat(x_113);
x_115 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__3(x_109, x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_79);
lean_dec(x_109);
return x_115;
}
else
{
lean_object* x_116; 
lean_dec(x_110);
x_116 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5(x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_79);
lean_dec(x_8);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_8);
x_117 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___rarg(x_79);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_io_promise_new(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = lean_apply_10(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_io_promise_resolve(x_1, x_13, x_17);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_io_promise_resolve(x_1, x_13, x_24);
lean_dec(x_13);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalTactic(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalTactic", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expandEval", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
x_3 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_4 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__1;
x_5 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__2;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__3;
x_2 = 1;
x_3 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__4;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__5;
x_3 = l_Lean_Language_Snapshot_Diagnostics_empty;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_Tactic_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_20 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__6;
lean_ctor_set(x_14, 1, x_19);
lean_ctor_set(x_14, 0, x_20);
x_21 = l_Lean_Language_SnapshotTask_pure___rarg(x_14);
x_22 = 0;
x_23 = l_Lean_Syntax_getRange_x3f(x_1, x_22);
lean_inc(x_4);
x_24 = lean_io_promise_result(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_mk(x_27);
lean_inc(x_1);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 2, x_18);
lean_ctor_set(x_29, 3, x_21);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_io_promise_resolve(x_30, x_31, x_17);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_7, 8);
lean_dec(x_37);
lean_ctor_set(x_32, 1, x_4);
lean_ctor_set(x_32, 0, x_18);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_7, 8, x_38);
x_39 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get(x_7, 1);
x_42 = lean_ctor_get(x_7, 2);
x_43 = lean_ctor_get_uint8(x_7, sizeof(void*)*9);
x_44 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 1);
x_45 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 2);
x_46 = lean_ctor_get(x_7, 3);
x_47 = lean_ctor_get(x_7, 4);
x_48 = lean_ctor_get(x_7, 5);
x_49 = lean_ctor_get(x_7, 6);
x_50 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 3);
x_51 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 4);
x_52 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 5);
x_53 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 6);
x_54 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 7);
x_55 = lean_ctor_get(x_7, 7);
x_56 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 8);
x_57 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 9);
lean_inc(x_55);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_7);
lean_ctor_set(x_32, 1, x_4);
lean_ctor_set(x_32, 0, x_18);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_32);
x_59 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_59, 0, x_40);
lean_ctor_set(x_59, 1, x_41);
lean_ctor_set(x_59, 2, x_42);
lean_ctor_set(x_59, 3, x_46);
lean_ctor_set(x_59, 4, x_47);
lean_ctor_set(x_59, 5, x_48);
lean_ctor_set(x_59, 6, x_49);
lean_ctor_set(x_59, 7, x_55);
lean_ctor_set(x_59, 8, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*9, x_43);
lean_ctor_set_uint8(x_59, sizeof(void*)*9 + 1, x_44);
lean_ctor_set_uint8(x_59, sizeof(void*)*9 + 2, x_45);
lean_ctor_set_uint8(x_59, sizeof(void*)*9 + 3, x_50);
lean_ctor_set_uint8(x_59, sizeof(void*)*9 + 4, x_51);
lean_ctor_set_uint8(x_59, sizeof(void*)*9 + 5, x_52);
lean_ctor_set_uint8(x_59, sizeof(void*)*9 + 6, x_53);
lean_ctor_set_uint8(x_59, sizeof(void*)*9 + 7, x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*9 + 8, x_56);
lean_ctor_set_uint8(x_59, sizeof(void*)*9 + 9, x_57);
x_60 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_59, x_8, x_9, x_10, x_11, x_12, x_34);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_61 = lean_ctor_get(x_32, 1);
lean_inc(x_61);
lean_dec(x_32);
x_62 = lean_ctor_get(x_7, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_7, 2);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_7, sizeof(void*)*9);
x_66 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 1);
x_67 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 2);
x_68 = lean_ctor_get(x_7, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_7, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_7, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_7, 6);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 3);
x_73 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 4);
x_74 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 5);
x_75 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 6);
x_76 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 7);
x_77 = lean_ctor_get(x_7, 7);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 8);
x_79 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 x_80 = x_7;
} else {
 lean_dec_ref(x_7);
 x_80 = lean_box(0);
}
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_18);
lean_ctor_set(x_81, 1, x_4);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 9, 10);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_62);
lean_ctor_set(x_83, 1, x_63);
lean_ctor_set(x_83, 2, x_64);
lean_ctor_set(x_83, 3, x_68);
lean_ctor_set(x_83, 4, x_69);
lean_ctor_set(x_83, 5, x_70);
lean_ctor_set(x_83, 6, x_71);
lean_ctor_set(x_83, 7, x_77);
lean_ctor_set(x_83, 8, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*9, x_65);
lean_ctor_set_uint8(x_83, sizeof(void*)*9 + 1, x_66);
lean_ctor_set_uint8(x_83, sizeof(void*)*9 + 2, x_67);
lean_ctor_set_uint8(x_83, sizeof(void*)*9 + 3, x_72);
lean_ctor_set_uint8(x_83, sizeof(void*)*9 + 4, x_73);
lean_ctor_set_uint8(x_83, sizeof(void*)*9 + 5, x_74);
lean_ctor_set_uint8(x_83, sizeof(void*)*9 + 6, x_75);
lean_ctor_set_uint8(x_83, sizeof(void*)*9 + 7, x_76);
lean_ctor_set_uint8(x_83, sizeof(void*)*9 + 8, x_78);
lean_ctor_set_uint8(x_83, sizeof(void*)*9 + 9, x_79);
x_84 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_83, x_8, x_9, x_10, x_11, x_12, x_61);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_3);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_32);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_3, 0);
x_88 = lean_ctor_get(x_32, 1);
x_89 = lean_ctor_get(x_32, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_7);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_7, 8);
lean_dec(x_91);
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
lean_dec(x_87);
x_93 = lean_ctor_get(x_92, 4);
lean_inc(x_93);
x_94 = lean_unsigned_to_nat(0u);
x_95 = l_Array_get_x3f___rarg(x_93, x_94);
lean_dec(x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
lean_dec(x_92);
lean_ctor_set(x_32, 1, x_4);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_3, 0, x_32);
lean_ctor_set(x_7, 8, x_3);
x_96 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_88);
return x_96;
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_95, 0);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_dec(x_92);
lean_ctor_set(x_32, 1, x_98);
lean_ctor_set(x_32, 0, x_99);
lean_ctor_set(x_95, 0, x_32);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_4);
lean_ctor_set(x_3, 0, x_100);
lean_ctor_set(x_7, 8, x_3);
x_101 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_88);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_95, 0);
lean_inc(x_102);
lean_dec(x_95);
x_103 = lean_ctor_get(x_92, 1);
lean_inc(x_103);
lean_dec(x_92);
lean_ctor_set(x_32, 1, x_102);
lean_ctor_set(x_32, 0, x_103);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_32);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_4);
lean_ctor_set(x_3, 0, x_105);
lean_ctor_set(x_7, 8, x_3);
x_106 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_88);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_107 = lean_ctor_get(x_7, 0);
x_108 = lean_ctor_get(x_7, 1);
x_109 = lean_ctor_get(x_7, 2);
x_110 = lean_ctor_get_uint8(x_7, sizeof(void*)*9);
x_111 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 1);
x_112 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 2);
x_113 = lean_ctor_get(x_7, 3);
x_114 = lean_ctor_get(x_7, 4);
x_115 = lean_ctor_get(x_7, 5);
x_116 = lean_ctor_get(x_7, 6);
x_117 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 3);
x_118 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 4);
x_119 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 5);
x_120 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 6);
x_121 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 7);
x_122 = lean_ctor_get(x_7, 7);
x_123 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 8);
x_124 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 9);
lean_inc(x_122);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_7);
x_125 = lean_ctor_get(x_87, 0);
lean_inc(x_125);
lean_dec(x_87);
x_126 = lean_ctor_get(x_125, 4);
lean_inc(x_126);
x_127 = lean_unsigned_to_nat(0u);
x_128 = l_Array_get_x3f___rarg(x_126, x_127);
lean_dec(x_126);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_125);
lean_ctor_set(x_32, 1, x_4);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_3, 0, x_32);
x_129 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_129, 0, x_107);
lean_ctor_set(x_129, 1, x_108);
lean_ctor_set(x_129, 2, x_109);
lean_ctor_set(x_129, 3, x_113);
lean_ctor_set(x_129, 4, x_114);
lean_ctor_set(x_129, 5, x_115);
lean_ctor_set(x_129, 6, x_116);
lean_ctor_set(x_129, 7, x_122);
lean_ctor_set(x_129, 8, x_3);
lean_ctor_set_uint8(x_129, sizeof(void*)*9, x_110);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 1, x_111);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 2, x_112);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 3, x_117);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 4, x_118);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 5, x_119);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 6, x_120);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 7, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 8, x_123);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 9, x_124);
x_130 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_129, x_8, x_9, x_10, x_11, x_12, x_88);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_132 = x_128;
} else {
 lean_dec_ref(x_128);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_125, 1);
lean_inc(x_133);
lean_dec(x_125);
lean_ctor_set(x_32, 1, x_131);
lean_ctor_set(x_32, 0, x_133);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_32);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_4);
lean_ctor_set(x_3, 0, x_135);
x_136 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_136, 0, x_107);
lean_ctor_set(x_136, 1, x_108);
lean_ctor_set(x_136, 2, x_109);
lean_ctor_set(x_136, 3, x_113);
lean_ctor_set(x_136, 4, x_114);
lean_ctor_set(x_136, 5, x_115);
lean_ctor_set(x_136, 6, x_116);
lean_ctor_set(x_136, 7, x_122);
lean_ctor_set(x_136, 8, x_3);
lean_ctor_set_uint8(x_136, sizeof(void*)*9, x_110);
lean_ctor_set_uint8(x_136, sizeof(void*)*9 + 1, x_111);
lean_ctor_set_uint8(x_136, sizeof(void*)*9 + 2, x_112);
lean_ctor_set_uint8(x_136, sizeof(void*)*9 + 3, x_117);
lean_ctor_set_uint8(x_136, sizeof(void*)*9 + 4, x_118);
lean_ctor_set_uint8(x_136, sizeof(void*)*9 + 5, x_119);
lean_ctor_set_uint8(x_136, sizeof(void*)*9 + 6, x_120);
lean_ctor_set_uint8(x_136, sizeof(void*)*9 + 7, x_121);
lean_ctor_set_uint8(x_136, sizeof(void*)*9 + 8, x_123);
lean_ctor_set_uint8(x_136, sizeof(void*)*9 + 9, x_124);
x_137 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_136, x_8, x_9, x_10, x_11, x_12, x_88);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; lean_object* x_155; uint8_t x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_138 = lean_ctor_get(x_3, 0);
x_139 = lean_ctor_get(x_32, 1);
lean_inc(x_139);
lean_dec(x_32);
x_140 = lean_ctor_get(x_7, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_7, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_7, 2);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_7, sizeof(void*)*9);
x_144 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 1);
x_145 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 2);
x_146 = lean_ctor_get(x_7, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_7, 4);
lean_inc(x_147);
x_148 = lean_ctor_get(x_7, 5);
lean_inc(x_148);
x_149 = lean_ctor_get(x_7, 6);
lean_inc(x_149);
x_150 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 3);
x_151 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 4);
x_152 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 5);
x_153 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 6);
x_154 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 7);
x_155 = lean_ctor_get(x_7, 7);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 8);
x_157 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 x_158 = x_7;
} else {
 lean_dec_ref(x_7);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_138, 0);
lean_inc(x_159);
lean_dec(x_138);
x_160 = lean_ctor_get(x_159, 4);
lean_inc(x_160);
x_161 = lean_unsigned_to_nat(0u);
x_162 = l_Array_get_x3f___rarg(x_160, x_161);
lean_dec(x_160);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_159);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_18);
lean_ctor_set(x_163, 1, x_4);
lean_ctor_set(x_3, 0, x_163);
if (lean_is_scalar(x_158)) {
 x_164 = lean_alloc_ctor(0, 9, 10);
} else {
 x_164 = x_158;
}
lean_ctor_set(x_164, 0, x_140);
lean_ctor_set(x_164, 1, x_141);
lean_ctor_set(x_164, 2, x_142);
lean_ctor_set(x_164, 3, x_146);
lean_ctor_set(x_164, 4, x_147);
lean_ctor_set(x_164, 5, x_148);
lean_ctor_set(x_164, 6, x_149);
lean_ctor_set(x_164, 7, x_155);
lean_ctor_set(x_164, 8, x_3);
lean_ctor_set_uint8(x_164, sizeof(void*)*9, x_143);
lean_ctor_set_uint8(x_164, sizeof(void*)*9 + 1, x_144);
lean_ctor_set_uint8(x_164, sizeof(void*)*9 + 2, x_145);
lean_ctor_set_uint8(x_164, sizeof(void*)*9 + 3, x_150);
lean_ctor_set_uint8(x_164, sizeof(void*)*9 + 4, x_151);
lean_ctor_set_uint8(x_164, sizeof(void*)*9 + 5, x_152);
lean_ctor_set_uint8(x_164, sizeof(void*)*9 + 6, x_153);
lean_ctor_set_uint8(x_164, sizeof(void*)*9 + 7, x_154);
lean_ctor_set_uint8(x_164, sizeof(void*)*9 + 8, x_156);
lean_ctor_set_uint8(x_164, sizeof(void*)*9 + 9, x_157);
x_165 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_164, x_8, x_9, x_10, x_11, x_12, x_139);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_167 = x_162;
} else {
 lean_dec_ref(x_162);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_159, 1);
lean_inc(x_168);
lean_dec(x_159);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_166);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(1, 1, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_4);
lean_ctor_set(x_3, 0, x_171);
if (lean_is_scalar(x_158)) {
 x_172 = lean_alloc_ctor(0, 9, 10);
} else {
 x_172 = x_158;
}
lean_ctor_set(x_172, 0, x_140);
lean_ctor_set(x_172, 1, x_141);
lean_ctor_set(x_172, 2, x_142);
lean_ctor_set(x_172, 3, x_146);
lean_ctor_set(x_172, 4, x_147);
lean_ctor_set(x_172, 5, x_148);
lean_ctor_set(x_172, 6, x_149);
lean_ctor_set(x_172, 7, x_155);
lean_ctor_set(x_172, 8, x_3);
lean_ctor_set_uint8(x_172, sizeof(void*)*9, x_143);
lean_ctor_set_uint8(x_172, sizeof(void*)*9 + 1, x_144);
lean_ctor_set_uint8(x_172, sizeof(void*)*9 + 2, x_145);
lean_ctor_set_uint8(x_172, sizeof(void*)*9 + 3, x_150);
lean_ctor_set_uint8(x_172, sizeof(void*)*9 + 4, x_151);
lean_ctor_set_uint8(x_172, sizeof(void*)*9 + 5, x_152);
lean_ctor_set_uint8(x_172, sizeof(void*)*9 + 6, x_153);
lean_ctor_set_uint8(x_172, sizeof(void*)*9 + 7, x_154);
lean_ctor_set_uint8(x_172, sizeof(void*)*9 + 8, x_156);
lean_ctor_set_uint8(x_172, sizeof(void*)*9 + 9, x_157);
x_173 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_172, x_8, x_9, x_10, x_11, x_12, x_139);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_174 = lean_ctor_get(x_3, 0);
lean_inc(x_174);
lean_dec(x_3);
x_175 = lean_ctor_get(x_32, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_176 = x_32;
} else {
 lean_dec_ref(x_32);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_7, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_7, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_7, 2);
lean_inc(x_179);
x_180 = lean_ctor_get_uint8(x_7, sizeof(void*)*9);
x_181 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 1);
x_182 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 2);
x_183 = lean_ctor_get(x_7, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_7, 4);
lean_inc(x_184);
x_185 = lean_ctor_get(x_7, 5);
lean_inc(x_185);
x_186 = lean_ctor_get(x_7, 6);
lean_inc(x_186);
x_187 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 3);
x_188 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 4);
x_189 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 5);
x_190 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 6);
x_191 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 7);
x_192 = lean_ctor_get(x_7, 7);
lean_inc(x_192);
x_193 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 8);
x_194 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 x_195 = x_7;
} else {
 lean_dec_ref(x_7);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_174, 0);
lean_inc(x_196);
lean_dec(x_174);
x_197 = lean_ctor_get(x_196, 4);
lean_inc(x_197);
x_198 = lean_unsigned_to_nat(0u);
x_199 = l_Array_get_x3f___rarg(x_197, x_198);
lean_dec(x_197);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_196);
if (lean_is_scalar(x_176)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_176;
}
lean_ctor_set(x_200, 0, x_18);
lean_ctor_set(x_200, 1, x_4);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
if (lean_is_scalar(x_195)) {
 x_202 = lean_alloc_ctor(0, 9, 10);
} else {
 x_202 = x_195;
}
lean_ctor_set(x_202, 0, x_177);
lean_ctor_set(x_202, 1, x_178);
lean_ctor_set(x_202, 2, x_179);
lean_ctor_set(x_202, 3, x_183);
lean_ctor_set(x_202, 4, x_184);
lean_ctor_set(x_202, 5, x_185);
lean_ctor_set(x_202, 6, x_186);
lean_ctor_set(x_202, 7, x_192);
lean_ctor_set(x_202, 8, x_201);
lean_ctor_set_uint8(x_202, sizeof(void*)*9, x_180);
lean_ctor_set_uint8(x_202, sizeof(void*)*9 + 1, x_181);
lean_ctor_set_uint8(x_202, sizeof(void*)*9 + 2, x_182);
lean_ctor_set_uint8(x_202, sizeof(void*)*9 + 3, x_187);
lean_ctor_set_uint8(x_202, sizeof(void*)*9 + 4, x_188);
lean_ctor_set_uint8(x_202, sizeof(void*)*9 + 5, x_189);
lean_ctor_set_uint8(x_202, sizeof(void*)*9 + 6, x_190);
lean_ctor_set_uint8(x_202, sizeof(void*)*9 + 7, x_191);
lean_ctor_set_uint8(x_202, sizeof(void*)*9 + 8, x_193);
lean_ctor_set_uint8(x_202, sizeof(void*)*9 + 9, x_194);
x_203 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_202, x_8, x_9, x_10, x_11, x_12, x_175);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_204 = lean_ctor_get(x_199, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 x_205 = x_199;
} else {
 lean_dec_ref(x_199);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_196, 1);
lean_inc(x_206);
lean_dec(x_196);
if (lean_is_scalar(x_176)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_176;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
if (lean_is_scalar(x_205)) {
 x_208 = lean_alloc_ctor(1, 1, 0);
} else {
 x_208 = x_205;
}
lean_ctor_set(x_208, 0, x_207);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_4);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
if (lean_is_scalar(x_195)) {
 x_211 = lean_alloc_ctor(0, 9, 10);
} else {
 x_211 = x_195;
}
lean_ctor_set(x_211, 0, x_177);
lean_ctor_set(x_211, 1, x_178);
lean_ctor_set(x_211, 2, x_179);
lean_ctor_set(x_211, 3, x_183);
lean_ctor_set(x_211, 4, x_184);
lean_ctor_set(x_211, 5, x_185);
lean_ctor_set(x_211, 6, x_186);
lean_ctor_set(x_211, 7, x_192);
lean_ctor_set(x_211, 8, x_210);
lean_ctor_set_uint8(x_211, sizeof(void*)*9, x_180);
lean_ctor_set_uint8(x_211, sizeof(void*)*9 + 1, x_181);
lean_ctor_set_uint8(x_211, sizeof(void*)*9 + 2, x_182);
lean_ctor_set_uint8(x_211, sizeof(void*)*9 + 3, x_187);
lean_ctor_set_uint8(x_211, sizeof(void*)*9 + 4, x_188);
lean_ctor_set_uint8(x_211, sizeof(void*)*9 + 5, x_189);
lean_ctor_set_uint8(x_211, sizeof(void*)*9 + 6, x_190);
lean_ctor_set_uint8(x_211, sizeof(void*)*9 + 7, x_191);
lean_ctor_set_uint8(x_211, sizeof(void*)*9 + 8, x_193);
lean_ctor_set_uint8(x_211, sizeof(void*)*9 + 9, x_194);
x_212 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_211, x_8, x_9, x_10, x_11, x_12, x_175);
return x_212;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_213 = lean_ctor_get(x_14, 0);
x_214 = lean_ctor_get(x_14, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_14);
x_215 = lean_box(0);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_213);
x_217 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__6;
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
x_219 = l_Lean_Language_SnapshotTask_pure___rarg(x_218);
x_220 = 0;
x_221 = l_Lean_Syntax_getRange_x3f(x_1, x_220);
lean_inc(x_4);
x_222 = lean_io_promise_result(x_4);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_box(0);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_array_mk(x_225);
lean_inc(x_1);
x_227 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_227, 0, x_217);
lean_ctor_set(x_227, 1, x_1);
lean_ctor_set(x_227, 2, x_215);
lean_ctor_set(x_227, 3, x_219);
lean_ctor_set(x_227, 4, x_226);
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_229 = lean_ctor_get(x_2, 1);
x_230 = lean_io_promise_resolve(x_228, x_229, x_214);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; lean_object* x_248; uint8_t x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_232 = x_230;
} else {
 lean_dec_ref(x_230);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_7, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_7, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_7, 2);
lean_inc(x_235);
x_236 = lean_ctor_get_uint8(x_7, sizeof(void*)*9);
x_237 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 1);
x_238 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 2);
x_239 = lean_ctor_get(x_7, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_7, 4);
lean_inc(x_240);
x_241 = lean_ctor_get(x_7, 5);
lean_inc(x_241);
x_242 = lean_ctor_get(x_7, 6);
lean_inc(x_242);
x_243 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 3);
x_244 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 4);
x_245 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 5);
x_246 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 6);
x_247 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 7);
x_248 = lean_ctor_get(x_7, 7);
lean_inc(x_248);
x_249 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 8);
x_250 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 x_251 = x_7;
} else {
 lean_dec_ref(x_7);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_232;
}
lean_ctor_set(x_252, 0, x_215);
lean_ctor_set(x_252, 1, x_4);
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_252);
if (lean_is_scalar(x_251)) {
 x_254 = lean_alloc_ctor(0, 9, 10);
} else {
 x_254 = x_251;
}
lean_ctor_set(x_254, 0, x_233);
lean_ctor_set(x_254, 1, x_234);
lean_ctor_set(x_254, 2, x_235);
lean_ctor_set(x_254, 3, x_239);
lean_ctor_set(x_254, 4, x_240);
lean_ctor_set(x_254, 5, x_241);
lean_ctor_set(x_254, 6, x_242);
lean_ctor_set(x_254, 7, x_248);
lean_ctor_set(x_254, 8, x_253);
lean_ctor_set_uint8(x_254, sizeof(void*)*9, x_236);
lean_ctor_set_uint8(x_254, sizeof(void*)*9 + 1, x_237);
lean_ctor_set_uint8(x_254, sizeof(void*)*9 + 2, x_238);
lean_ctor_set_uint8(x_254, sizeof(void*)*9 + 3, x_243);
lean_ctor_set_uint8(x_254, sizeof(void*)*9 + 4, x_244);
lean_ctor_set_uint8(x_254, sizeof(void*)*9 + 5, x_245);
lean_ctor_set_uint8(x_254, sizeof(void*)*9 + 6, x_246);
lean_ctor_set_uint8(x_254, sizeof(void*)*9 + 7, x_247);
lean_ctor_set_uint8(x_254, sizeof(void*)*9 + 8, x_249);
lean_ctor_set_uint8(x_254, sizeof(void*)*9 + 9, x_250);
x_255 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_254, x_8, x_9, x_10, x_11, x_12, x_231);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; uint8_t x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; lean_object* x_275; uint8_t x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_256 = lean_ctor_get(x_3, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_257 = x_3;
} else {
 lean_dec_ref(x_3);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_230, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_259 = x_230;
} else {
 lean_dec_ref(x_230);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_7, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_7, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_7, 2);
lean_inc(x_262);
x_263 = lean_ctor_get_uint8(x_7, sizeof(void*)*9);
x_264 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 1);
x_265 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 2);
x_266 = lean_ctor_get(x_7, 3);
lean_inc(x_266);
x_267 = lean_ctor_get(x_7, 4);
lean_inc(x_267);
x_268 = lean_ctor_get(x_7, 5);
lean_inc(x_268);
x_269 = lean_ctor_get(x_7, 6);
lean_inc(x_269);
x_270 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 3);
x_271 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 4);
x_272 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 5);
x_273 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 6);
x_274 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 7);
x_275 = lean_ctor_get(x_7, 7);
lean_inc(x_275);
x_276 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 8);
x_277 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 x_278 = x_7;
} else {
 lean_dec_ref(x_7);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_256, 0);
lean_inc(x_279);
lean_dec(x_256);
x_280 = lean_ctor_get(x_279, 4);
lean_inc(x_280);
x_281 = lean_unsigned_to_nat(0u);
x_282 = l_Array_get_x3f___rarg(x_280, x_281);
lean_dec(x_280);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_279);
if (lean_is_scalar(x_259)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_259;
}
lean_ctor_set(x_283, 0, x_215);
lean_ctor_set(x_283, 1, x_4);
if (lean_is_scalar(x_257)) {
 x_284 = lean_alloc_ctor(1, 1, 0);
} else {
 x_284 = x_257;
}
lean_ctor_set(x_284, 0, x_283);
if (lean_is_scalar(x_278)) {
 x_285 = lean_alloc_ctor(0, 9, 10);
} else {
 x_285 = x_278;
}
lean_ctor_set(x_285, 0, x_260);
lean_ctor_set(x_285, 1, x_261);
lean_ctor_set(x_285, 2, x_262);
lean_ctor_set(x_285, 3, x_266);
lean_ctor_set(x_285, 4, x_267);
lean_ctor_set(x_285, 5, x_268);
lean_ctor_set(x_285, 6, x_269);
lean_ctor_set(x_285, 7, x_275);
lean_ctor_set(x_285, 8, x_284);
lean_ctor_set_uint8(x_285, sizeof(void*)*9, x_263);
lean_ctor_set_uint8(x_285, sizeof(void*)*9 + 1, x_264);
lean_ctor_set_uint8(x_285, sizeof(void*)*9 + 2, x_265);
lean_ctor_set_uint8(x_285, sizeof(void*)*9 + 3, x_270);
lean_ctor_set_uint8(x_285, sizeof(void*)*9 + 4, x_271);
lean_ctor_set_uint8(x_285, sizeof(void*)*9 + 5, x_272);
lean_ctor_set_uint8(x_285, sizeof(void*)*9 + 6, x_273);
lean_ctor_set_uint8(x_285, sizeof(void*)*9 + 7, x_274);
lean_ctor_set_uint8(x_285, sizeof(void*)*9 + 8, x_276);
lean_ctor_set_uint8(x_285, sizeof(void*)*9 + 9, x_277);
x_286 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_285, x_8, x_9, x_10, x_11, x_12, x_258);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_287 = lean_ctor_get(x_282, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 x_288 = x_282;
} else {
 lean_dec_ref(x_282);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_279, 1);
lean_inc(x_289);
lean_dec(x_279);
if (lean_is_scalar(x_259)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_259;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_287);
if (lean_is_scalar(x_288)) {
 x_291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_291 = x_288;
}
lean_ctor_set(x_291, 0, x_290);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_4);
if (lean_is_scalar(x_257)) {
 x_293 = lean_alloc_ctor(1, 1, 0);
} else {
 x_293 = x_257;
}
lean_ctor_set(x_293, 0, x_292);
if (lean_is_scalar(x_278)) {
 x_294 = lean_alloc_ctor(0, 9, 10);
} else {
 x_294 = x_278;
}
lean_ctor_set(x_294, 0, x_260);
lean_ctor_set(x_294, 1, x_261);
lean_ctor_set(x_294, 2, x_262);
lean_ctor_set(x_294, 3, x_266);
lean_ctor_set(x_294, 4, x_267);
lean_ctor_set(x_294, 5, x_268);
lean_ctor_set(x_294, 6, x_269);
lean_ctor_set(x_294, 7, x_275);
lean_ctor_set(x_294, 8, x_293);
lean_ctor_set_uint8(x_294, sizeof(void*)*9, x_263);
lean_ctor_set_uint8(x_294, sizeof(void*)*9 + 1, x_264);
lean_ctor_set_uint8(x_294, sizeof(void*)*9 + 2, x_265);
lean_ctor_set_uint8(x_294, sizeof(void*)*9 + 3, x_270);
lean_ctor_set_uint8(x_294, sizeof(void*)*9 + 4, x_271);
lean_ctor_set_uint8(x_294, sizeof(void*)*9 + 5, x_272);
lean_ctor_set_uint8(x_294, sizeof(void*)*9 + 6, x_273);
lean_ctor_set_uint8(x_294, sizeof(void*)*9 + 7, x_274);
lean_ctor_set_uint8(x_294, sizeof(void*)*9 + 8, x_276);
lean_ctor_set_uint8(x_294, sizeof(void*)*9 + 9, x_277);
x_295 = l_Lean_Elab_Tactic_evalTactic(x_1, x_5, x_6, x_294, x_8, x_9, x_10, x_11, x_12, x_258);
return x_295;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_11);
x_14 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_isEmpty___rarg(x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_4);
x_18 = l_Lean_Elab_Tactic_evalTactic(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = l_List_isEmpty___rarg(x_3);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_4);
x_20 = l_Lean_Elab_Tactic_evalTactic(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_7, 8);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_4);
x_22 = l_Lean_Elab_Tactic_evalTactic(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_12, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_12, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 3);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_48; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_4);
x_48 = lean_box(0);
x_33 = x_48;
goto block_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_32, 0);
lean_inc(x_49);
lean_dec(x_32);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = l_Lean_Syntax_getKind(x_4);
x_52 = l_Lean_Syntax_isOfKind(x_50, x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_49);
lean_dec(x_31);
lean_dec(x_27);
x_53 = lean_box(0);
x_33 = x_53;
goto block_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec(x_49);
x_55 = l_Lean_Language_SnapshotTask_get___rarg(x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Language_SnapshotTask_get___rarg(x_57);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
lean_dec(x_55);
lean_dec(x_31);
lean_dec(x_27);
x_60 = lean_box(0);
x_33 = x_60;
goto block_47;
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
x_68 = lean_nat_dec_eq(x_67, x_27);
lean_dec(x_27);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_66);
lean_free_object(x_59);
lean_dec(x_55);
lean_dec(x_31);
x_69 = lean_box(0);
x_33 = x_69;
goto block_47;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_66, 3);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_ctor_get(x_70, 2);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_eq(x_71, x_72);
lean_dec(x_71);
if (x_73 == 0)
{
lean_object* x_74; 
lean_free_object(x_59);
lean_dec(x_55);
lean_dec(x_31);
x_74 = lean_box(0);
x_33 = x_74;
goto block_47;
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_31, 2);
lean_inc(x_75);
lean_dec(x_31);
x_76 = lean_nat_dec_eq(x_75, x_72);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_free_object(x_59);
lean_dec(x_55);
x_77 = lean_box(0);
x_33 = x_77;
goto block_47;
}
else
{
lean_ctor_set(x_59, 0, x_55);
x_33 = x_59;
goto block_47;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_78 = lean_ctor_get(x_59, 0);
lean_inc(x_78);
lean_dec(x_59);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
x_84 = lean_nat_dec_eq(x_83, x_27);
lean_dec(x_27);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_55);
lean_dec(x_31);
x_85 = lean_box(0);
x_33 = x_85;
goto block_47;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_82, 3);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_ctor_get(x_86, 2);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_dec_eq(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_55);
lean_dec(x_31);
x_90 = lean_box(0);
x_33 = x_90;
goto block_47;
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_31, 2);
lean_inc(x_91);
lean_dec(x_31);
x_92 = lean_nat_dec_eq(x_91, x_88);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
lean_dec(x_55);
x_93 = lean_box(0);
x_33 = x_93;
goto block_47;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_55);
x_33 = x_94;
goto block_47;
}
}
}
}
}
}
}
block_47:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___boxed), 13, 3);
lean_closure_set(x_34, 0, x_15);
lean_closure_set(x_34, 1, x_23);
lean_closure_set(x_34, 2, x_33);
x_35 = l_Lean_Elab_Tactic_instInhabitedTacticParsedSnapshot;
x_36 = l_Lean_Language_withAlwaysResolvedPromise___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__7(x_35, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_95 = !lean_is_exclusive(x_14);
if (x_95 == 0)
{
return x_14;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_14, 0);
x_97 = lean_ctor_get(x_14, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_14);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Elab_Tactic_saveState___rarg(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_ctor_set(x_17, 1, x_19);
lean_ctor_set(x_17, 0, x_1);
x_21 = lean_array_push(x_2, x_17);
x_22 = 1;
lean_inc(x_3);
x_23 = l_Lean_Elab_Tactic_SavedState_restore(x_3, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_20);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Tactic_evalTactic_expandEval(x_4, x_3, x_5, x_6, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_array_push(x_2, x_28);
x_30 = 1;
lean_inc(x_3);
x_31 = l_Lean_Elab_Tactic_SavedState_restore(x_3, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Elab_Tactic_evalTactic_expandEval(x_4, x_3, x_5, x_6, x_29, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_32);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_evalTactic_eval(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_18 = x_3;
} else {
 lean_dec_ref(x_3);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_1);
x_20 = lean_apply_1(x_19, x_1);
lean_inc(x_1);
lean_inc(x_17);
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__4___boxed), 13, 4);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_4);
lean_closure_set(x_21, 2, x_17);
lean_closure_set(x_21, 3, x_1);
x_76 = lean_ctor_get(x_16, 0);
lean_inc(x_76);
lean_dec(x_16);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
lean_inc(x_1);
x_80 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_79, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg___lambda__1), 11, 1);
lean_closure_set(x_83, 0, x_81);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_84 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_evalTactic_eval___spec__2(x_21, x_83, x_79, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_22 = x_85;
x_23 = x_86;
goto block_75;
}
block_75:
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isInterrupt(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isRuntime(x_22);
if (x_25 == 0)
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_18);
x_26 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__2;
x_27 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__5(x_22, x_5, x_2, x_1, x_17, x_4, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
lean_inc(x_22);
x_34 = l_Lean_Exception_toMessageData(x_22);
x_35 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2(x_26, x_34, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__5(x_22, x_5, x_2, x_1, x_17, x_4, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_37);
lean_dec(x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
x_40 = l_Lean_Elab_Tactic_evalTactic_handleEx___closed__1;
x_41 = lean_nat_dec_eq(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Elab_Tactic_evalTactic_handleEx___closed__2;
x_43 = lean_nat_dec_eq(x_39, x_42);
lean_dec(x_39);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_18)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_18;
}
lean_ctor_set(x_44, 0, x_22);
lean_ctor_set(x_44, 1, x_23);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_18);
x_45 = l_Lean_Core_getMessageLog___rarg(x_13, x_23);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_MessageLog_toList(x_46);
lean_dec(x_46);
x_49 = lean_box(0);
x_50 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4(x_48, x_49, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_47);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Lean_Elab_Tactic_saveState___rarg(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_51);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_ctor_set(x_52, 1, x_54);
lean_ctor_set(x_52, 0, x_22);
x_56 = lean_array_push(x_5, x_52);
x_57 = 1;
lean_inc(x_2);
x_58 = l_Lean_Elab_Tactic_SavedState_restore(x_2, x_57, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_55);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_3 = x_17;
x_5 = x_56;
x_14 = x_59;
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_22);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_array_push(x_5, x_63);
x_65 = 1;
lean_inc(x_2);
x_66 = l_Lean_Elab_Tactic_SavedState_restore(x_2, x_65, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_62);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_3 = x_17;
x_5 = x_64;
x_14 = x_67;
goto _start;
}
}
}
else
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_39);
lean_dec(x_22);
lean_dec(x_18);
x_69 = 1;
lean_inc(x_2);
x_70 = l_Lean_Elab_Tactic_SavedState_restore(x_2, x_69, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_3 = x_17;
x_14 = x_71;
goto _start;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_18)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_18;
}
lean_ctor_set(x_73, 0, x_22);
lean_ctor_set(x_73, 1, x_23);
return x_73;
}
}
else
{
lean_object* x_74; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_18)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_18;
}
lean_ctor_set(x_74, 0, x_22);
lean_ctor_set(x_74, 1, x_23);
return x_74;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 5);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 5, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
x_24 = lean_ctor_get(x_9, 8);
x_25 = lean_ctor_get(x_9, 9);
x_26 = lean_ctor_get(x_9, 10);
x_27 = lean_ctor_get_uint8(x_9, sizeof(void*)*12);
x_28 = lean_ctor_get(x_9, 11);
x_29 = lean_ctor_get_uint8(x_9, sizeof(void*)*12 + 1);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_30 = l_Lean_replaceRef(x_1, x_21);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_17);
lean_ctor_set(x_31, 2, x_18);
lean_ctor_set(x_31, 3, x_19);
lean_ctor_set(x_31, 4, x_20);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set(x_31, 7, x_23);
lean_ctor_set(x_31, 8, x_24);
lean_ctor_set(x_31, 9, x_25);
lean_ctor_set(x_31, 10, x_26);
lean_ctor_set(x_31, 11, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*12, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*12 + 1, x_29);
x_32 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31, x_10, x_11);
lean_dec(x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Elab_Tactic_evalTactic___spec__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_st_ref_take(x_1, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 3);
lean_dec(x_11);
x_12 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__3;
lean_ctor_set(x_8, 3, x_12);
x_13 = lean_st_ref_set(x_1, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 4);
x_22 = lean_ctor_get(x_8, 5);
x_23 = lean_ctor_get(x_8, 6);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_24 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__3;
x_25 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_21);
lean_ctor_set(x_25, 5, x_22);
lean_ctor_set(x_25, 6, x_23);
x_26 = lean_st_ref_set(x_1, x_25, x_9);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Elab_Tactic_evalTactic___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Elab_Tactic_evalTactic___spec__4___rarg___boxed), 2, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_15 = lean_ctor_get(x_11, 5);
x_16 = l_Lean_replaceRef(x_3, x_15);
lean_dec(x_15);
lean_ctor_set(x_11, 5, x_16);
x_17 = lean_st_ref_get(x_12, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 3);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_PersistentArray_toArray___rarg(x_20);
lean_dec(x_20);
x_22 = lean_array_size(x_21);
x_23 = 0;
x_24 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(x_22, x_23, x_21);
x_25 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_25, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_11);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_take(x_12, x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_29, 1);
x_34 = lean_ctor_get(x_31, 3);
lean_dec(x_34);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 0, x_3);
x_35 = l_Lean_PersistentArray_push___rarg(x_1, x_29);
lean_ctor_set(x_31, 3, x_35);
x_36 = lean_st_ref_set(x_12, x_31, x_33);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_29, 1);
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
x_46 = lean_ctor_get(x_31, 2);
x_47 = lean_ctor_get(x_31, 4);
x_48 = lean_ctor_get(x_31, 5);
x_49 = lean_ctor_get(x_31, 6);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 0, x_3);
x_50 = l_Lean_PersistentArray_push___rarg(x_1, x_29);
x_51 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_45);
lean_ctor_set(x_51, 2, x_46);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_47);
lean_ctor_set(x_51, 5, x_48);
lean_ctor_set(x_51, 6, x_49);
x_52 = lean_st_ref_set(x_12, x_51, x_43);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_57 = lean_ctor_get(x_29, 0);
x_58 = lean_ctor_get(x_29, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_29);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 6);
lean_inc(x_64);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 lean_ctor_release(x_57, 6);
 x_65 = x_57;
} else {
 lean_dec_ref(x_57);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_3);
lean_ctor_set(x_66, 1, x_27);
x_67 = l_Lean_PersistentArray_push___rarg(x_1, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 7, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_60);
lean_ctor_set(x_68, 2, x_61);
lean_ctor_set(x_68, 3, x_67);
lean_ctor_set(x_68, 4, x_62);
lean_ctor_set(x_68, 5, x_63);
lean_ctor_set(x_68, 6, x_64);
x_69 = lean_st_ref_set(x_12, x_68, x_58);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_74 = lean_ctor_get(x_11, 0);
x_75 = lean_ctor_get(x_11, 1);
x_76 = lean_ctor_get(x_11, 2);
x_77 = lean_ctor_get(x_11, 3);
x_78 = lean_ctor_get(x_11, 4);
x_79 = lean_ctor_get(x_11, 5);
x_80 = lean_ctor_get(x_11, 6);
x_81 = lean_ctor_get(x_11, 7);
x_82 = lean_ctor_get(x_11, 8);
x_83 = lean_ctor_get(x_11, 9);
x_84 = lean_ctor_get(x_11, 10);
x_85 = lean_ctor_get_uint8(x_11, sizeof(void*)*12);
x_86 = lean_ctor_get(x_11, 11);
x_87 = lean_ctor_get_uint8(x_11, sizeof(void*)*12 + 1);
lean_inc(x_86);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_11);
x_88 = l_Lean_replaceRef(x_3, x_79);
lean_dec(x_79);
x_89 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_75);
lean_ctor_set(x_89, 2, x_76);
lean_ctor_set(x_89, 3, x_77);
lean_ctor_set(x_89, 4, x_78);
lean_ctor_set(x_89, 5, x_88);
lean_ctor_set(x_89, 6, x_80);
lean_ctor_set(x_89, 7, x_81);
lean_ctor_set(x_89, 8, x_82);
lean_ctor_set(x_89, 9, x_83);
lean_ctor_set(x_89, 10, x_84);
lean_ctor_set(x_89, 11, x_86);
lean_ctor_set_uint8(x_89, sizeof(void*)*12, x_85);
lean_ctor_set_uint8(x_89, sizeof(void*)*12 + 1, x_87);
x_90 = lean_st_ref_get(x_12, x_13);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 3);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_PersistentArray_toArray___rarg(x_93);
lean_dec(x_93);
x_95 = lean_array_size(x_94);
x_96 = 0;
x_97 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(x_95, x_96, x_94);
x_98 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_98, 0, x_2);
lean_ctor_set(x_98, 1, x_4);
lean_ctor_set(x_98, 2, x_97);
x_99 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_98, x_9, x_10, x_89, x_12, x_92);
lean_dec(x_89);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_st_ref_take(x_12, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_103, 4);
lean_inc(x_109);
x_110 = lean_ctor_get(x_103, 5);
lean_inc(x_110);
x_111 = lean_ctor_get(x_103, 6);
lean_inc(x_111);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 lean_ctor_release(x_103, 5);
 lean_ctor_release(x_103, 6);
 x_112 = x_103;
} else {
 lean_dec_ref(x_103);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_105;
}
lean_ctor_set(x_113, 0, x_3);
lean_ctor_set(x_113, 1, x_100);
x_114 = l_Lean_PersistentArray_push___rarg(x_1, x_113);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 7, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_106);
lean_ctor_set(x_115, 1, x_107);
lean_ctor_set(x_115, 2, x_108);
lean_ctor_set(x_115, 3, x_114);
lean_ctor_set(x_115, 4, x_109);
lean_ctor_set(x_115, 5, x_110);
lean_ctor_set(x_115, 6, x_111);
x_116 = lean_st_ref_set(x_12, x_115, x_104);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_box(0);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_evalTactic___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_13);
x_16 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__5(x_1, x_5, x_2, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_evalTactic___spec__6(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
lean_dec(x_13);
return x_18;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_profiler;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, double x_9, double x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
double x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__1;
lean_inc(x_3);
lean_inc(x_1);
x_22 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set_float(x_22, sizeof(void*)*2, x_21);
lean_ctor_set_float(x_22, sizeof(void*)*2 + 8, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 16, x_2);
x_23 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2___closed__1;
x_24 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_7, x_23);
if (x_24 == 0)
{
if (x_8 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__1(x_4, x_5, x_11, x_6, x_22, x_25, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set_float(x_27, sizeof(void*)*2, x_9);
lean_ctor_set_float(x_27, sizeof(void*)*2 + 8, x_10);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 16, x_2);
x_28 = lean_box(0);
x_29 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__1(x_4, x_5, x_11, x_6, x_27, x_28, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set_float(x_30, sizeof(void*)*2, x_9);
lean_ctor_set_float(x_30, sizeof(void*)*2 + 8, x_10);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 16, x_2);
x_31 = lean_box(0);
x_32 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__1(x_4, x_5, x_11, x_6, x_30, x_31, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_32;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, double x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 5);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
x_22 = lean_apply_10(x_10, x_5, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_21, x_5, x_6, x_7, x_8, x_9, x_23, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_24);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___closed__2;
x_28 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_21, x_5, x_6, x_7, x_8, x_9, x_27, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_26);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
return x_28;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_useHeartbeats;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_threshold;
return x_1;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Elab_Tactic_evalTactic___spec__4___rarg(x_16, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__1;
x_22 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_io_mono_nanos_now(x_20);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_94 = lean_apply_9(x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_93);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_96);
x_99 = lean_io_mono_nanos_now(x_97);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; double x_105; double x_106; double x_107; double x_108; double x_109; lean_object* x_110; lean_object* x_111; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
x_103 = 0;
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_Float_ofScientific(x_92, x_103, x_104);
lean_dec(x_92);
x_106 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__5;
x_107 = lean_float_div(x_105, x_106);
x_108 = l_Float_ofScientific(x_101, x_103, x_104);
lean_dec(x_101);
x_109 = lean_float_div(x_108, x_106);
x_110 = lean_box_float(x_107);
x_111 = lean_box_float(x_109);
lean_ctor_set(x_99, 1, x_111);
lean_ctor_set(x_99, 0, x_110);
lean_ctor_set(x_94, 1, x_99);
lean_ctor_set(x_94, 0, x_98);
x_23 = x_94;
x_24 = x_102;
goto block_90;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; double x_116; double x_117; double x_118; double x_119; double x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_112 = lean_ctor_get(x_99, 0);
x_113 = lean_ctor_get(x_99, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_99);
x_114 = 0;
x_115 = lean_unsigned_to_nat(0u);
x_116 = l_Float_ofScientific(x_92, x_114, x_115);
lean_dec(x_92);
x_117 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__5;
x_118 = lean_float_div(x_116, x_117);
x_119 = l_Float_ofScientific(x_112, x_114, x_115);
lean_dec(x_112);
x_120 = lean_float_div(x_119, x_117);
x_121 = lean_box_float(x_118);
x_122 = lean_box_float(x_120);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_94, 1, x_123);
lean_ctor_set(x_94, 0, x_98);
x_23 = x_94;
x_24 = x_113;
goto block_90;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; double x_133; double x_134; double x_135; double x_136; double x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_124 = lean_ctor_get(x_94, 0);
x_125 = lean_ctor_get(x_94, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_94);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_124);
x_127 = lean_io_mono_nanos_now(x_125);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = 0;
x_132 = lean_unsigned_to_nat(0u);
x_133 = l_Float_ofScientific(x_92, x_131, x_132);
lean_dec(x_92);
x_134 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__5;
x_135 = lean_float_div(x_133, x_134);
x_136 = l_Float_ofScientific(x_128, x_131, x_132);
lean_dec(x_128);
x_137 = lean_float_div(x_136, x_134);
x_138 = lean_box_float(x_135);
x_139 = lean_box_float(x_137);
if (lean_is_scalar(x_130)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_130;
}
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_126);
lean_ctor_set(x_141, 1, x_140);
x_23 = x_141;
x_24 = x_129;
goto block_90;
}
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_94);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_143 = lean_ctor_get(x_94, 0);
x_144 = lean_ctor_get(x_94, 1);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_143);
x_146 = lean_io_mono_nanos_now(x_144);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; double x_152; double x_153; double x_154; double x_155; double x_156; lean_object* x_157; lean_object* x_158; 
x_148 = lean_ctor_get(x_146, 0);
x_149 = lean_ctor_get(x_146, 1);
x_150 = 0;
x_151 = lean_unsigned_to_nat(0u);
x_152 = l_Float_ofScientific(x_92, x_150, x_151);
lean_dec(x_92);
x_153 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__5;
x_154 = lean_float_div(x_152, x_153);
x_155 = l_Float_ofScientific(x_148, x_150, x_151);
lean_dec(x_148);
x_156 = lean_float_div(x_155, x_153);
x_157 = lean_box_float(x_154);
x_158 = lean_box_float(x_156);
lean_ctor_set(x_146, 1, x_158);
lean_ctor_set(x_146, 0, x_157);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 1, x_146);
lean_ctor_set(x_94, 0, x_145);
x_23 = x_94;
x_24 = x_149;
goto block_90;
}
else
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; double x_163; double x_164; double x_165; double x_166; double x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_159 = lean_ctor_get(x_146, 0);
x_160 = lean_ctor_get(x_146, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_146);
x_161 = 0;
x_162 = lean_unsigned_to_nat(0u);
x_163 = l_Float_ofScientific(x_92, x_161, x_162);
lean_dec(x_92);
x_164 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__5;
x_165 = lean_float_div(x_163, x_164);
x_166 = l_Float_ofScientific(x_159, x_161, x_162);
lean_dec(x_159);
x_167 = lean_float_div(x_166, x_164);
x_168 = lean_box_float(x_165);
x_169 = lean_box_float(x_167);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 1, x_170);
lean_ctor_set(x_94, 0, x_145);
x_23 = x_94;
x_24 = x_160;
goto block_90;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; double x_180; double x_181; double x_182; double x_183; double x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_171 = lean_ctor_get(x_94, 0);
x_172 = lean_ctor_get(x_94, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_94);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_171);
x_174 = lean_io_mono_nanos_now(x_172);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
x_178 = 0;
x_179 = lean_unsigned_to_nat(0u);
x_180 = l_Float_ofScientific(x_92, x_178, x_179);
lean_dec(x_92);
x_181 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__5;
x_182 = lean_float_div(x_180, x_181);
x_183 = l_Float_ofScientific(x_175, x_178, x_179);
lean_dec(x_175);
x_184 = lean_float_div(x_183, x_181);
x_185 = lean_box_float(x_182);
x_186 = lean_box_float(x_184);
if (lean_is_scalar(x_177)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_177;
}
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_173);
lean_ctor_set(x_188, 1, x_187);
x_23 = x_188;
x_24 = x_176;
goto block_90;
}
}
block_90:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_76; uint8_t x_77; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_76 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__2;
x_77 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_76);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = 0;
x_29 = x_78;
goto block_75;
}
else
{
double x_79; double x_80; double x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; double x_86; double x_87; double x_88; uint8_t x_89; 
x_79 = lean_unbox_float(x_28);
x_80 = lean_unbox_float(x_27);
x_81 = lean_float_sub(x_79, x_80);
x_82 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__3;
x_83 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_82);
x_84 = 0;
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Float_ofScientific(x_83, x_84, x_85);
lean_dec(x_83);
x_87 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__4;
x_88 = lean_float_div(x_86, x_87);
x_89 = lean_float_decLt(x_88, x_81);
x_29 = x_89;
goto block_75;
}
block_75:
{
if (x_6 == 0)
{
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_30 = lean_st_ref_take(x_16, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_31, 3);
x_35 = l_Lean_PersistentArray_append___rarg(x_19, x_34);
lean_dec(x_34);
lean_ctor_set(x_31, 3, x_35);
x_36 = lean_st_ref_set(x_16, x_31, x_32);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_evalTactic___spec__6(x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_37);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_26);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_31, 0);
x_48 = lean_ctor_get(x_31, 1);
x_49 = lean_ctor_get(x_31, 2);
x_50 = lean_ctor_get(x_31, 3);
x_51 = lean_ctor_get(x_31, 4);
x_52 = lean_ctor_get(x_31, 5);
x_53 = lean_ctor_get(x_31, 6);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_31);
x_54 = l_Lean_PersistentArray_append___rarg(x_19, x_50);
lean_dec(x_50);
x_55 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_55, 2, x_49);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_51);
lean_ctor_set(x_55, 5, x_52);
lean_ctor_set(x_55, 6, x_53);
x_56 = lean_st_ref_set(x_16, x_55, x_32);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_evalTactic___spec__6(x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_57);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_26);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; double x_68; double x_69; lean_object* x_70; 
x_67 = lean_box(0);
x_68 = lean_unbox_float(x_27);
lean_dec(x_27);
x_69 = lean_unbox_float(x_28);
lean_dec(x_28);
x_70 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3(x_2, x_3, x_4, x_19, x_26, x_1, x_29, x_68, x_69, x_5, x_67, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_24);
return x_70;
}
}
else
{
lean_object* x_71; double x_72; double x_73; lean_object* x_74; 
x_71 = lean_box(0);
x_72 = lean_unbox_float(x_27);
lean_dec(x_27);
x_73 = lean_unbox_float(x_28);
lean_dec(x_28);
x_74 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3(x_2, x_3, x_4, x_19, x_26, x_1, x_29, x_72, x_73, x_5, x_71, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_24);
return x_74;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_io_get_num_heartbeats(x_20);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_258 = lean_apply_9(x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_257);
if (lean_obj_tag(x_258) == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_260 = lean_ctor_get(x_258, 0);
x_261 = lean_ctor_get(x_258, 1);
x_262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_262, 0, x_260);
x_263 = lean_io_get_num_heartbeats(x_261);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; double x_269; double x_270; lean_object* x_271; lean_object* x_272; 
x_265 = lean_ctor_get(x_263, 0);
x_266 = lean_ctor_get(x_263, 1);
x_267 = 0;
x_268 = lean_unsigned_to_nat(0u);
x_269 = l_Float_ofScientific(x_256, x_267, x_268);
lean_dec(x_256);
x_270 = l_Float_ofScientific(x_265, x_267, x_268);
lean_dec(x_265);
x_271 = lean_box_float(x_269);
x_272 = lean_box_float(x_270);
lean_ctor_set(x_263, 1, x_272);
lean_ctor_set(x_263, 0, x_271);
lean_ctor_set(x_258, 1, x_263);
lean_ctor_set(x_258, 0, x_262);
x_189 = x_258;
x_190 = x_266;
goto block_254;
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; double x_277; double x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_273 = lean_ctor_get(x_263, 0);
x_274 = lean_ctor_get(x_263, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_263);
x_275 = 0;
x_276 = lean_unsigned_to_nat(0u);
x_277 = l_Float_ofScientific(x_256, x_275, x_276);
lean_dec(x_256);
x_278 = l_Float_ofScientific(x_273, x_275, x_276);
lean_dec(x_273);
x_279 = lean_box_float(x_277);
x_280 = lean_box_float(x_278);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
lean_ctor_set(x_258, 1, x_281);
lean_ctor_set(x_258, 0, x_262);
x_189 = x_258;
x_190 = x_274;
goto block_254;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; double x_291; double x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_282 = lean_ctor_get(x_258, 0);
x_283 = lean_ctor_get(x_258, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_258);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_282);
x_285 = lean_io_get_num_heartbeats(x_283);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_288 = x_285;
} else {
 lean_dec_ref(x_285);
 x_288 = lean_box(0);
}
x_289 = 0;
x_290 = lean_unsigned_to_nat(0u);
x_291 = l_Float_ofScientific(x_256, x_289, x_290);
lean_dec(x_256);
x_292 = l_Float_ofScientific(x_286, x_289, x_290);
lean_dec(x_286);
x_293 = lean_box_float(x_291);
x_294 = lean_box_float(x_292);
if (lean_is_scalar(x_288)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_288;
}
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_284);
lean_ctor_set(x_296, 1, x_295);
x_189 = x_296;
x_190 = x_287;
goto block_254;
}
}
else
{
uint8_t x_297; 
x_297 = !lean_is_exclusive(x_258);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_298 = lean_ctor_get(x_258, 0);
x_299 = lean_ctor_get(x_258, 1);
x_300 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_300, 0, x_298);
x_301 = lean_io_get_num_heartbeats(x_299);
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; double x_307; double x_308; lean_object* x_309; lean_object* x_310; 
x_303 = lean_ctor_get(x_301, 0);
x_304 = lean_ctor_get(x_301, 1);
x_305 = 0;
x_306 = lean_unsigned_to_nat(0u);
x_307 = l_Float_ofScientific(x_256, x_305, x_306);
lean_dec(x_256);
x_308 = l_Float_ofScientific(x_303, x_305, x_306);
lean_dec(x_303);
x_309 = lean_box_float(x_307);
x_310 = lean_box_float(x_308);
lean_ctor_set(x_301, 1, x_310);
lean_ctor_set(x_301, 0, x_309);
lean_ctor_set_tag(x_258, 0);
lean_ctor_set(x_258, 1, x_301);
lean_ctor_set(x_258, 0, x_300);
x_189 = x_258;
x_190 = x_304;
goto block_254;
}
else
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; double x_315; double x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_311 = lean_ctor_get(x_301, 0);
x_312 = lean_ctor_get(x_301, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_301);
x_313 = 0;
x_314 = lean_unsigned_to_nat(0u);
x_315 = l_Float_ofScientific(x_256, x_313, x_314);
lean_dec(x_256);
x_316 = l_Float_ofScientific(x_311, x_313, x_314);
lean_dec(x_311);
x_317 = lean_box_float(x_315);
x_318 = lean_box_float(x_316);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
lean_ctor_set_tag(x_258, 0);
lean_ctor_set(x_258, 1, x_319);
lean_ctor_set(x_258, 0, x_300);
x_189 = x_258;
x_190 = x_312;
goto block_254;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; double x_329; double x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_320 = lean_ctor_get(x_258, 0);
x_321 = lean_ctor_get(x_258, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_258);
x_322 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_322, 0, x_320);
x_323 = lean_io_get_num_heartbeats(x_321);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_326 = x_323;
} else {
 lean_dec_ref(x_323);
 x_326 = lean_box(0);
}
x_327 = 0;
x_328 = lean_unsigned_to_nat(0u);
x_329 = l_Float_ofScientific(x_256, x_327, x_328);
lean_dec(x_256);
x_330 = l_Float_ofScientific(x_324, x_327, x_328);
lean_dec(x_324);
x_331 = lean_box_float(x_329);
x_332 = lean_box_float(x_330);
if (lean_is_scalar(x_326)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_326;
}
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_322);
lean_ctor_set(x_334, 1, x_333);
x_189 = x_334;
x_190 = x_325;
goto block_254;
}
}
block_254:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_242; uint8_t x_243; 
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 0);
lean_inc(x_192);
lean_dec(x_189);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_dec(x_191);
x_242 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__2;
x_243 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_242);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = 0;
x_195 = x_244;
goto block_241;
}
else
{
double x_245; double x_246; double x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; double x_252; uint8_t x_253; 
x_245 = lean_unbox_float(x_194);
x_246 = lean_unbox_float(x_193);
x_247 = lean_float_sub(x_245, x_246);
x_248 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__3;
x_249 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_248);
x_250 = 0;
x_251 = lean_unsigned_to_nat(0u);
x_252 = l_Float_ofScientific(x_249, x_250, x_251);
lean_dec(x_249);
x_253 = lean_float_decLt(x_252, x_247);
x_195 = x_253;
goto block_241;
}
block_241:
{
if (x_6 == 0)
{
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_196 = lean_st_ref_take(x_16, x_190);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = !lean_is_exclusive(x_197);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_197, 3);
x_201 = l_Lean_PersistentArray_append___rarg(x_19, x_200);
lean_dec(x_200);
lean_ctor_set(x_197, 3, x_201);
x_202 = lean_st_ref_set(x_16, x_197, x_198);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_evalTactic___spec__6(x_192, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_203);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_192);
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
return x_204;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_204, 0);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_204);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
else
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_204);
if (x_209 == 0)
{
return x_204;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_204, 0);
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_204);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_213 = lean_ctor_get(x_197, 0);
x_214 = lean_ctor_get(x_197, 1);
x_215 = lean_ctor_get(x_197, 2);
x_216 = lean_ctor_get(x_197, 3);
x_217 = lean_ctor_get(x_197, 4);
x_218 = lean_ctor_get(x_197, 5);
x_219 = lean_ctor_get(x_197, 6);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_197);
x_220 = l_Lean_PersistentArray_append___rarg(x_19, x_216);
lean_dec(x_216);
x_221 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_221, 0, x_213);
lean_ctor_set(x_221, 1, x_214);
lean_ctor_set(x_221, 2, x_215);
lean_ctor_set(x_221, 3, x_220);
lean_ctor_set(x_221, 4, x_217);
lean_ctor_set(x_221, 5, x_218);
lean_ctor_set(x_221, 6, x_219);
x_222 = lean_st_ref_set(x_16, x_221, x_198);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_evalTactic___spec__6(x_192, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_223);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_192);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_227 = x_224;
} else {
 lean_dec_ref(x_224);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_224, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_224, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_231 = x_224;
} else {
 lean_dec_ref(x_224);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
}
else
{
lean_object* x_233; double x_234; double x_235; lean_object* x_236; 
x_233 = lean_box(0);
x_234 = lean_unbox_float(x_193);
lean_dec(x_193);
x_235 = lean_unbox_float(x_194);
lean_dec(x_194);
x_236 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3(x_2, x_3, x_4, x_19, x_192, x_1, x_195, x_234, x_235, x_5, x_233, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_190);
return x_236;
}
}
else
{
lean_object* x_237; double x_238; double x_239; lean_object* x_240; 
x_237 = lean_box(0);
x_238 = lean_unbox_float(x_193);
lean_dec(x_193);
x_239 = lean_unbox_float(x_194);
lean_dec(x_194);
x_240 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3(x_2, x_3, x_4, x_19, x_192, x_1, x_195, x_238, x_239, x_5, x_237, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_190);
return x_240;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
lean_inc(x_1);
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__2;
x_21 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_15, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_apply_9(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_19);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_box(0);
x_32 = lean_unbox(x_17);
lean_dec(x_17);
x_33 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4(x_15, x_1, x_4, x_5, x_2, x_32, x_3, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_19);
lean_dec(x_15);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_box(0);
x_36 = lean_unbox(x_17);
lean_dec(x_17);
x_37 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4(x_15, x_1, x_4, x_5, x_2, x_36, x_3, x_35, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_34);
lean_dec(x_15);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTactic___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Elab_Tactic_evalTactic(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_17;
x_13 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_13);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__2;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Elab_Tactic_evalTactic___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_apply_8(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = l_Lean_profileitIOUnsafe___rarg(x_1, x_2, x_14, x_4, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Elab_Tactic_evalTactic___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_profileitM___at_Lean_Elab_Tactic_evalTactic___spec__9___rarg___boxed), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_MessageData_ofSyntax(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Elab_Tactic_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__2;
x_18 = l_Lean_Elab_Tactic_evalTactic_expandEval(x_1, x_15, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_macroAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic '", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has not been implemented", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_16 = l_Lean_Syntax_getKind(x_1);
x_17 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__1;
x_18 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_17, x_15, x_16);
lean_dec(x_15);
x_19 = lean_st_ref_get(x_9, x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__2;
x_25 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_24, x_23, x_16);
lean_dec(x_23);
x_26 = l_List_isEmpty___rarg(x_18);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_19);
lean_dec(x_16);
lean_free_object(x_11);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Tactic_evalTactic___lambda__3(x_1, x_25, x_18, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l_List_isEmpty___rarg(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_19);
lean_dec(x_16);
lean_free_object(x_11);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Tactic_evalTactic___lambda__3(x_1, x_25, x_18, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_25);
lean_dec(x_18);
x_32 = l_Lean_MessageData_ofName(x_16);
x_33 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__4;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_32);
lean_ctor_set(x_19, 0, x_33);
x_34 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__6;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_34);
lean_ctor_set(x_11, 0, x_19);
x_35 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic___spec__1(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_19);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__2;
x_44 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_43, x_42, x_16);
lean_dec(x_42);
x_45 = l_List_isEmpty___rarg(x_18);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_16);
lean_free_object(x_11);
x_46 = lean_box(0);
x_47 = l_Lean_Elab_Tactic_evalTactic___lambda__3(x_1, x_44, x_18, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = l_List_isEmpty___rarg(x_44);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_16);
lean_free_object(x_11);
x_49 = lean_box(0);
x_50 = l_Lean_Elab_Tactic_evalTactic___lambda__3(x_1, x_44, x_18, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_44);
lean_dec(x_18);
x_51 = l_Lean_MessageData_ofName(x_16);
x_52 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__4;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__6;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_54);
lean_ctor_set(x_11, 0, x_53);
x_55 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic___spec__1(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_60 = lean_ctor_get(x_11, 0);
x_61 = lean_ctor_get(x_11, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_11);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_1);
x_63 = l_Lean_Syntax_getKind(x_1);
x_64 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__1;
x_65 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_64, x_62, x_63);
lean_dec(x_62);
x_66 = lean_st_ref_get(x_9, x_61);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_71 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__2;
x_72 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_71, x_70, x_63);
lean_dec(x_70);
x_73 = l_List_isEmpty___rarg(x_65);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_69);
lean_dec(x_63);
x_74 = lean_box(0);
x_75 = l_Lean_Elab_Tactic_evalTactic___lambda__3(x_1, x_72, x_65, x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
return x_75;
}
else
{
uint8_t x_76; 
x_76 = l_List_isEmpty___rarg(x_72);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_69);
lean_dec(x_63);
x_77 = lean_box(0);
x_78 = l_Lean_Elab_Tactic_evalTactic___lambda__3(x_1, x_72, x_65, x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_72);
lean_dec(x_65);
x_79 = l_Lean_MessageData_ofName(x_63);
x_80 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__4;
if (lean_is_scalar(x_69)) {
 x_81 = lean_alloc_ctor(7, 2, 0);
} else {
 x_81 = x_69;
 lean_ctor_set_tag(x_81, 7);
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__6;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic___spec__1(x_1, x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("step", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
x_2 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lambda__5___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected tactic", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_15 = lean_ctor_get(x_8, 3);
x_16 = lean_ctor_get(x_8, 4);
x_17 = lean_ctor_get(x_8, 5);
x_18 = lean_ctor_get(x_8, 6);
x_19 = lean_ctor_get(x_8, 7);
x_20 = lean_ctor_get(x_8, 8);
x_21 = lean_ctor_get(x_8, 9);
x_22 = lean_ctor_get(x_8, 10);
x_23 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_24 = lean_ctor_get(x_8, 11);
x_25 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
x_26 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_26);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_ctor_set(x_8, 5, x_26);
x_27 = lean_nat_dec_eq(x_15, x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_8);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_15, x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_13);
lean_ctor_set(x_30, 2, x_14);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_16);
lean_ctor_set(x_30, 5, x_26);
lean_ctor_set(x_30, 6, x_18);
lean_ctor_set(x_30, 7, x_19);
lean_ctor_set(x_30, 8, x_20);
lean_ctor_set(x_30, 9, x_21);
lean_ctor_set(x_30, 10, x_22);
lean_ctor_set(x_30, 11, x_24);
lean_ctor_set_uint8(x_30, sizeof(void*)*12, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*12 + 1, x_25);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__1;
x_32 = l_Lean_Core_withFreshMacroScope___rarg(x_31, x_30, x_9, x_10);
return x_32;
}
case 1:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__3;
x_35 = lean_name_eq(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_1);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lambda__2___boxed), 11, 1);
lean_closure_set(x_36, 0, x_1);
lean_inc(x_1);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lambda__4), 10, 1);
lean_closure_set(x_37, 0, x_1);
x_38 = l_Lean_Syntax_getKind(x_1);
x_39 = 1;
x_40 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__4;
x_41 = l_Lean_Name_toString(x_38, x_39, x_40);
x_42 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__5;
x_43 = lean_box(x_39);
x_44 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___boxed), 14, 11);
lean_closure_set(x_44, 0, x_42);
lean_closure_set(x_44, 1, x_36);
lean_closure_set(x_44, 2, x_37);
lean_closure_set(x_44, 3, x_43);
lean_closure_set(x_44, 4, x_41);
lean_closure_set(x_44, 5, x_2);
lean_closure_set(x_44, 6, x_3);
lean_closure_set(x_44, 7, x_4);
lean_closure_set(x_44, 8, x_5);
lean_closure_set(x_44, 9, x_6);
lean_closure_set(x_44, 10, x_7);
x_45 = l_Lean_Core_withFreshMacroScope___rarg(x_44, x_30, x_9, x_10);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = l_Lean_Syntax_getArgs(x_1);
x_47 = lean_array_get_size(x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_lt(x_48, x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
lean_dec(x_46);
x_50 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__6;
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 2);
lean_closure_set(x_51, 0, x_1);
lean_closure_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_box(x_52);
x_54 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___boxed), 11, 8);
lean_closure_set(x_54, 0, x_53);
lean_closure_set(x_54, 1, x_51);
lean_closure_set(x_54, 2, x_2);
lean_closure_set(x_54, 3, x_3);
lean_closure_set(x_54, 4, x_4);
lean_closure_set(x_54, 5, x_5);
lean_closure_set(x_54, 6, x_6);
lean_closure_set(x_54, 7, x_7);
x_55 = l_Lean_Core_withFreshMacroScope___rarg(x_54, x_30, x_9, x_10);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_47, x_47);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_47);
lean_dec(x_46);
x_57 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__6;
x_58 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 2);
lean_closure_set(x_58, 0, x_1);
lean_closure_set(x_58, 1, x_57);
x_59 = 1;
x_60 = lean_box(x_59);
x_61 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___boxed), 11, 8);
lean_closure_set(x_61, 0, x_60);
lean_closure_set(x_61, 1, x_58);
lean_closure_set(x_61, 2, x_2);
lean_closure_set(x_61, 3, x_3);
lean_closure_set(x_61, 4, x_4);
lean_closure_set(x_61, 5, x_5);
lean_closure_set(x_61, 6, x_6);
lean_closure_set(x_61, 7, x_7);
x_62 = l_Lean_Core_withFreshMacroScope___rarg(x_61, x_30, x_9, x_10);
return x_62;
}
else
{
size_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_64 = lean_box(0);
x_65 = l_Lean_Elab_Tactic_evalTactic___lambda__6___boxed__const__1;
x_66 = lean_box_usize(x_63);
x_67 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTactic___spec__7___boxed), 13, 4);
lean_closure_set(x_67, 0, x_46);
lean_closure_set(x_67, 1, x_65);
lean_closure_set(x_67, 2, x_66);
lean_closure_set(x_67, 3, x_64);
x_68 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 2);
lean_closure_set(x_68, 0, x_1);
lean_closure_set(x_68, 1, x_67);
x_69 = 1;
x_70 = lean_box(x_69);
x_71 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___boxed), 11, 8);
lean_closure_set(x_71, 0, x_70);
lean_closure_set(x_71, 1, x_68);
lean_closure_set(x_71, 2, x_2);
lean_closure_set(x_71, 3, x_3);
lean_closure_set(x_71, 4, x_4);
lean_closure_set(x_71, 5, x_5);
lean_closure_set(x_71, 6, x_6);
lean_closure_set(x_71, 7, x_7);
x_72 = l_Lean_Core_withFreshMacroScope___rarg(x_71, x_30, x_9, x_10);
return x_72;
}
}
}
}
case 2:
{
lean_object* x_73; uint8_t x_74; 
lean_inc(x_1);
x_73 = l_Lean_MessageData_ofSyntax(x_1);
x_74 = !lean_is_exclusive(x_1);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_1, 1);
lean_dec(x_75);
x_76 = lean_ctor_get(x_1, 0);
lean_dec(x_76);
x_77 = l_Lean_indentD(x_73);
x_78 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__8;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_78);
x_79 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2___boxed), 10, 7);
lean_closure_set(x_81, 0, x_80);
lean_closure_set(x_81, 1, x_2);
lean_closure_set(x_81, 2, x_3);
lean_closure_set(x_81, 3, x_4);
lean_closure_set(x_81, 4, x_5);
lean_closure_set(x_81, 5, x_6);
lean_closure_set(x_81, 6, x_7);
x_82 = l_Lean_Core_withFreshMacroScope___rarg(x_81, x_30, x_9, x_10);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_1);
x_83 = l_Lean_indentD(x_73);
x_84 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__8;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2___boxed), 10, 7);
lean_closure_set(x_88, 0, x_87);
lean_closure_set(x_88, 1, x_2);
lean_closure_set(x_88, 2, x_3);
lean_closure_set(x_88, 3, x_4);
lean_closure_set(x_88, 4, x_5);
lean_closure_set(x_88, 5, x_6);
lean_closure_set(x_88, 6, x_7);
x_89 = l_Lean_Core_withFreshMacroScope___rarg(x_88, x_30, x_9, x_10);
return x_89;
}
}
default: 
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = l_Lean_MessageData_ofSyntax(x_1);
x_91 = l_Lean_indentD(x_90);
x_92 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__8;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2___boxed), 10, 7);
lean_closure_set(x_96, 0, x_95);
lean_closure_set(x_96, 1, x_2);
lean_closure_set(x_96, 2, x_3);
lean_closure_set(x_96, 3, x_4);
lean_closure_set(x_96, 4, x_5);
lean_closure_set(x_96, 5, x_6);
lean_closure_set(x_96, 6, x_7);
x_97 = l_Lean_Core_withFreshMacroScope___rarg(x_96, x_30, x_9, x_10);
return x_97;
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_98 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic___spec__8(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_99 = lean_ctor_get(x_8, 0);
x_100 = lean_ctor_get(x_8, 1);
x_101 = lean_ctor_get(x_8, 2);
x_102 = lean_ctor_get(x_8, 3);
x_103 = lean_ctor_get(x_8, 4);
x_104 = lean_ctor_get(x_8, 5);
x_105 = lean_ctor_get(x_8, 6);
x_106 = lean_ctor_get(x_8, 7);
x_107 = lean_ctor_get(x_8, 8);
x_108 = lean_ctor_get(x_8, 9);
x_109 = lean_ctor_get(x_8, 10);
x_110 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_111 = lean_ctor_get(x_8, 11);
x_112 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_111);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_8);
x_113 = l_Lean_replaceRef(x_1, x_104);
lean_dec(x_104);
lean_inc(x_111);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_113);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_114 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_114, 0, x_99);
lean_ctor_set(x_114, 1, x_100);
lean_ctor_set(x_114, 2, x_101);
lean_ctor_set(x_114, 3, x_102);
lean_ctor_set(x_114, 4, x_103);
lean_ctor_set(x_114, 5, x_113);
lean_ctor_set(x_114, 6, x_105);
lean_ctor_set(x_114, 7, x_106);
lean_ctor_set(x_114, 8, x_107);
lean_ctor_set(x_114, 9, x_108);
lean_ctor_set(x_114, 10, x_109);
lean_ctor_set(x_114, 11, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*12, x_110);
lean_ctor_set_uint8(x_114, sizeof(void*)*12 + 1, x_112);
x_115 = lean_nat_dec_eq(x_102, x_103);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_114);
x_116 = lean_unsigned_to_nat(1u);
x_117 = lean_nat_add(x_102, x_116);
lean_dec(x_102);
x_118 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_118, 0, x_99);
lean_ctor_set(x_118, 1, x_100);
lean_ctor_set(x_118, 2, x_101);
lean_ctor_set(x_118, 3, x_117);
lean_ctor_set(x_118, 4, x_103);
lean_ctor_set(x_118, 5, x_113);
lean_ctor_set(x_118, 6, x_105);
lean_ctor_set(x_118, 7, x_106);
lean_ctor_set(x_118, 8, x_107);
lean_ctor_set(x_118, 9, x_108);
lean_ctor_set(x_118, 10, x_109);
lean_ctor_set(x_118, 11, x_111);
lean_ctor_set_uint8(x_118, sizeof(void*)*12, x_110);
lean_ctor_set_uint8(x_118, sizeof(void*)*12 + 1, x_112);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__1;
x_120 = l_Lean_Core_withFreshMacroScope___rarg(x_119, x_118, x_9, x_10);
return x_120;
}
case 1:
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_121 = lean_ctor_get(x_1, 1);
lean_inc(x_121);
x_122 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__3;
x_123 = lean_name_eq(x_121, x_122);
lean_dec(x_121);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_inc(x_1);
x_124 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lambda__2___boxed), 11, 1);
lean_closure_set(x_124, 0, x_1);
lean_inc(x_1);
x_125 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lambda__4), 10, 1);
lean_closure_set(x_125, 0, x_1);
x_126 = l_Lean_Syntax_getKind(x_1);
x_127 = 1;
x_128 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__4;
x_129 = l_Lean_Name_toString(x_126, x_127, x_128);
x_130 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__5;
x_131 = lean_box(x_127);
x_132 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___boxed), 14, 11);
lean_closure_set(x_132, 0, x_130);
lean_closure_set(x_132, 1, x_124);
lean_closure_set(x_132, 2, x_125);
lean_closure_set(x_132, 3, x_131);
lean_closure_set(x_132, 4, x_129);
lean_closure_set(x_132, 5, x_2);
lean_closure_set(x_132, 6, x_3);
lean_closure_set(x_132, 7, x_4);
lean_closure_set(x_132, 8, x_5);
lean_closure_set(x_132, 9, x_6);
lean_closure_set(x_132, 10, x_7);
x_133 = l_Lean_Core_withFreshMacroScope___rarg(x_132, x_118, x_9, x_10);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = l_Lean_Syntax_getArgs(x_1);
x_135 = lean_array_get_size(x_134);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_nat_dec_lt(x_136, x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_135);
lean_dec(x_134);
x_138 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__6;
x_139 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 2);
lean_closure_set(x_139, 0, x_1);
lean_closure_set(x_139, 1, x_138);
x_140 = 1;
x_141 = lean_box(x_140);
x_142 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___boxed), 11, 8);
lean_closure_set(x_142, 0, x_141);
lean_closure_set(x_142, 1, x_139);
lean_closure_set(x_142, 2, x_2);
lean_closure_set(x_142, 3, x_3);
lean_closure_set(x_142, 4, x_4);
lean_closure_set(x_142, 5, x_5);
lean_closure_set(x_142, 6, x_6);
lean_closure_set(x_142, 7, x_7);
x_143 = l_Lean_Core_withFreshMacroScope___rarg(x_142, x_118, x_9, x_10);
return x_143;
}
else
{
uint8_t x_144; 
x_144 = lean_nat_dec_le(x_135, x_135);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_135);
lean_dec(x_134);
x_145 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__6;
x_146 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 2);
lean_closure_set(x_146, 0, x_1);
lean_closure_set(x_146, 1, x_145);
x_147 = 1;
x_148 = lean_box(x_147);
x_149 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___boxed), 11, 8);
lean_closure_set(x_149, 0, x_148);
lean_closure_set(x_149, 1, x_146);
lean_closure_set(x_149, 2, x_2);
lean_closure_set(x_149, 3, x_3);
lean_closure_set(x_149, 4, x_4);
lean_closure_set(x_149, 5, x_5);
lean_closure_set(x_149, 6, x_6);
lean_closure_set(x_149, 7, x_7);
x_150 = l_Lean_Core_withFreshMacroScope___rarg(x_149, x_118, x_9, x_10);
return x_150;
}
else
{
size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_151 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_152 = lean_box(0);
x_153 = l_Lean_Elab_Tactic_evalTactic___lambda__6___boxed__const__1;
x_154 = lean_box_usize(x_151);
x_155 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTactic___spec__7___boxed), 13, 4);
lean_closure_set(x_155, 0, x_134);
lean_closure_set(x_155, 1, x_153);
lean_closure_set(x_155, 2, x_154);
lean_closure_set(x_155, 3, x_152);
x_156 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 2);
lean_closure_set(x_156, 0, x_1);
lean_closure_set(x_156, 1, x_155);
x_157 = 1;
x_158 = lean_box(x_157);
x_159 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___boxed), 11, 8);
lean_closure_set(x_159, 0, x_158);
lean_closure_set(x_159, 1, x_156);
lean_closure_set(x_159, 2, x_2);
lean_closure_set(x_159, 3, x_3);
lean_closure_set(x_159, 4, x_4);
lean_closure_set(x_159, 5, x_5);
lean_closure_set(x_159, 6, x_6);
lean_closure_set(x_159, 7, x_7);
x_160 = l_Lean_Core_withFreshMacroScope___rarg(x_159, x_118, x_9, x_10);
return x_160;
}
}
}
}
case 2:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_inc(x_1);
x_161 = l_Lean_MessageData_ofSyntax(x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_162 = x_1;
} else {
 lean_dec_ref(x_1);
 x_162 = lean_box(0);
}
x_163 = l_Lean_indentD(x_161);
x_164 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__8;
if (lean_is_scalar(x_162)) {
 x_165 = lean_alloc_ctor(7, 2, 0);
} else {
 x_165 = x_162;
 lean_ctor_set_tag(x_165, 7);
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
x_166 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2___boxed), 10, 7);
lean_closure_set(x_168, 0, x_167);
lean_closure_set(x_168, 1, x_2);
lean_closure_set(x_168, 2, x_3);
lean_closure_set(x_168, 3, x_4);
lean_closure_set(x_168, 4, x_5);
lean_closure_set(x_168, 5, x_6);
lean_closure_set(x_168, 6, x_7);
x_169 = l_Lean_Core_withFreshMacroScope___rarg(x_168, x_118, x_9, x_10);
return x_169;
}
default: 
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_170 = l_Lean_MessageData_ofSyntax(x_1);
x_171 = l_Lean_indentD(x_170);
x_172 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__8;
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
x_174 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2___boxed), 10, 7);
lean_closure_set(x_176, 0, x_175);
lean_closure_set(x_176, 1, x_2);
lean_closure_set(x_176, 2, x_3);
lean_closure_set(x_176, 3, x_4);
lean_closure_set(x_176, 4, x_5);
lean_closure_set(x_176, 5, x_6);
lean_closure_set(x_176, 6, x_7);
x_177 = l_Lean_Core_withFreshMacroScope___rarg(x_176, x_118, x_9, x_10);
return x_177;
}
}
}
else
{
lean_object* x_178; 
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_1);
x_178 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic___spec__8(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_114, x_9, x_10);
lean_dec(x_9);
lean_dec(x_114);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_178;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic execution", 16, 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lambda__6), 10, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_Syntax_getKind(x_1);
x_14 = l_Lean_Elab_Tactic_evalTactic___closed__1;
x_15 = l_Lean_profileitM___at_Lean_Elab_Tactic_evalTactic___spec__9___rarg(x_14, x_11, x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalTactic___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Elab_Tactic_evalTactic___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Elab_Tactic_evalTactic___spec__4___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Elab_Tactic_evalTactic___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Elab_Tactic_evalTactic___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_evalTactic___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_evalTactic___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; double x_23; double x_24; lean_object* x_25; 
x_21 = lean_unbox(x_2);
lean_dec(x_2);
x_22 = lean_unbox(x_8);
lean_dec(x_8);
x_23 = lean_unbox_float(x_9);
lean_dec(x_9);
x_24 = lean_unbox_float(x_10);
lean_dec(x_10);
x_25 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_22, x_23, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; double x_23; double x_24; lean_object* x_25; 
x_21 = lean_unbox(x_2);
lean_dec(x_2);
x_22 = lean_unbox(x_7);
lean_dec(x_7);
x_23 = lean_unbox_float(x_8);
lean_dec(x_8);
x_24 = lean_unbox_float(x_9);
lean_dec(x_9);
x_25 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3(x_1, x_21, x_3, x_4, x_5, x_6, x_22, x_23, x_24, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_11);
lean_dec(x_6);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4(x_1, x_2, x_18, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTactic___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTactic___spec__7(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Elab_Tactic_evalTactic___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_profileitM___at_Lean_Elab_Tactic_evalTactic___spec__9___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalTactic___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalTactic___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalTactic___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalTactic___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no goals to be solved", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__2;
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalTactic_handleEx___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_done(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_List_isEmpty___rarg(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_free_object(x_10);
x_15 = l_Lean_Elab_Term_reportUnsolvedGoals(x_12, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg(x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = lean_box(0);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = l_List_isEmpty___rarg(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Elab_Term_reportUnsolvedGoals(x_23, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg(x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_31 = x_26;
} else {
 lean_dec_ref(x_26);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_done___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_done(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_box(0);
lean_ctor_set(x_12, 1, x_18);
x_19 = l_Lean_Elab_Tactic_setGoals(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_appendTR___rarg(x_25, x_17);
x_28 = l_Lean_Elab_Tactic_setGoals(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_22);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_Tactic_setGoals(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_43 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_List_appendTR___rarg(x_47, x_38);
x_50 = l_Lean_Elab_Tactic_setGoals(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_38);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_56 = x_43;
} else {
 lean_dec_ref(x_43);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focus(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focus___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Tactic_done(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focusAndDone___rarg___lambda__1), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_focus___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focusAndDone___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_10 = lean_ctor_get(x_7, 6);
x_11 = lean_ctor_get(x_7, 7);
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = 0;
x_15 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_16 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_4);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_5);
x_17 = lean_st_ref_take(x_8, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 5);
x_22 = l_Lean_MessageLog_add(x_16, x_21);
lean_ctor_set(x_18, 5, x_22);
x_23 = lean_st_ref_set(x_8, x_18, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 2);
x_33 = lean_ctor_get(x_18, 3);
x_34 = lean_ctor_get(x_18, 4);
x_35 = lean_ctor_get(x_18, 5);
x_36 = lean_ctor_get(x_18, 6);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_37 = l_Lean_MessageLog_add(x_16, x_35);
x_38 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_31);
lean_ctor_set(x_38, 2, x_32);
lean_ctor_set(x_38, 3, x_33);
lean_ctor_set(x_38, 4, x_34);
lean_ctor_set(x_38, 5, x_37);
lean_ctor_set(x_38, 6, x_36);
x_39 = lean_st_ref_set(x_8, x_38, x_19);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_9 = lean_string_dec_eq(x_5, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__2;
x_12 = lean_string_dec_eq(x_4, x_11);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__2___closed__1;
x_14 = lean_string_dec_eq(x_4, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_188; uint8_t x_189; 
x_188 = 2;
x_189 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_106_(x_3, x_188);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_box(0);
x_13 = x_190;
goto block_187;
}
else
{
lean_object* x_191; uint8_t x_192; 
lean_inc(x_2);
x_191 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_192 = lean_unbox(x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_box(0);
x_13 = x_193;
goto block_187;
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_10);
lean_dec(x_2);
x_194 = lean_box(0);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_12);
return x_195;
}
}
block_187:
{
uint8_t x_14; lean_object* x_181; uint8_t x_182; uint8_t x_183; 
lean_dec(x_13);
x_181 = lean_ctor_get(x_10, 2);
lean_inc(x_181);
x_182 = 1;
x_183 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_106_(x_3, x_182);
if (x_183 == 0)
{
lean_dec(x_181);
x_14 = x_3;
goto block_180;
}
else
{
lean_object* x_184; uint8_t x_185; 
x_184 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__2;
x_185 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_181, x_184);
lean_dec(x_181);
if (x_185 == 0)
{
x_14 = x_3;
goto block_180;
}
else
{
uint8_t x_186; 
x_186 = 2;
x_14 = x_186;
goto block_180;
}
}
block_180:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 5);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_10, sizeof(void*)*12 + 1);
x_19 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_20 = 0;
x_21 = l_Lean_Syntax_getPos_x3f(x_19, x_20);
x_22 = l_Lean_Syntax_getTailPos_x3f(x_19, x_20);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_FileMap_toPosition(x_16, x_27);
lean_inc(x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
if (x_18 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_23);
x_30 = lean_box(0);
x_31 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_25, x_15, x_28, x_29, x_14, x_30, x_10, x_11, x_26);
lean_dec(x_10);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1;
lean_inc(x_25);
x_33 = l_Lean_MessageData_hasTag(x_32, x_25);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_10);
x_34 = lean_box(0);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_free_object(x_23);
x_35 = lean_box(0);
x_36 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_25, x_15, x_28, x_29, x_14, x_35, x_10, x_11, x_26);
lean_dec(x_10);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_FileMap_toPosition(x_16, x_39);
lean_inc(x_40);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
if (x_18 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_37, x_15, x_40, x_41, x_14, x_42, x_10, x_11, x_38);
lean_dec(x_10);
return x_43;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1;
lean_inc(x_37);
x_45 = l_Lean_MessageData_hasTag(x_44, x_37);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_15);
lean_dec(x_10);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
x_49 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_37, x_15, x_40, x_41, x_14, x_48, x_10, x_11, x_38);
lean_dec(x_10);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_22);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_22, 0);
x_52 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
x_57 = l_Lean_FileMap_toPosition(x_16, x_56);
x_58 = l_Lean_FileMap_toPosition(x_16, x_51);
lean_dec(x_51);
lean_ctor_set(x_22, 0, x_58);
if (x_18 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_free_object(x_52);
x_59 = lean_box(0);
x_60 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_54, x_15, x_57, x_22, x_14, x_59, x_10, x_11, x_55);
lean_dec(x_10);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1;
lean_inc(x_54);
x_62 = l_Lean_MessageData_hasTag(x_61, x_54);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_22);
lean_dec(x_57);
lean_dec(x_54);
lean_dec(x_15);
lean_dec(x_10);
x_63 = lean_box(0);
lean_ctor_set(x_52, 0, x_63);
return x_52;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_free_object(x_52);
x_64 = lean_box(0);
x_65 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_54, x_15, x_57, x_22, x_14, x_64, x_10, x_11, x_55);
lean_dec(x_10);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_52, 0);
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_52);
x_68 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
x_69 = l_Lean_FileMap_toPosition(x_16, x_68);
x_70 = l_Lean_FileMap_toPosition(x_16, x_51);
lean_dec(x_51);
lean_ctor_set(x_22, 0, x_70);
if (x_18 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_box(0);
x_72 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_66, x_15, x_69, x_22, x_14, x_71, x_10, x_11, x_67);
lean_dec(x_10);
return x_72;
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1;
lean_inc(x_66);
x_74 = l_Lean_MessageData_hasTag(x_73, x_66);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_22);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_15);
lean_dec(x_10);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_67);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_box(0);
x_78 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_66, x_15, x_69, x_22, x_14, x_77, x_10, x_11, x_67);
lean_dec(x_10);
return x_78;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_22, 0);
lean_inc(x_79);
lean_dec(x_22);
x_80 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
x_85 = l_Lean_FileMap_toPosition(x_16, x_84);
x_86 = l_Lean_FileMap_toPosition(x_16, x_79);
lean_dec(x_79);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
if (x_18 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_83);
x_88 = lean_box(0);
x_89 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_81, x_15, x_85, x_87, x_14, x_88, x_10, x_11, x_82);
lean_dec(x_10);
return x_89;
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1;
lean_inc(x_81);
x_91 = l_Lean_MessageData_hasTag(x_90, x_81);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_81);
lean_dec(x_15);
lean_dec(x_10);
x_92 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_83;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_82);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_83);
x_94 = lean_box(0);
x_95 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_81, x_15, x_85, x_87, x_14, x_94, x_10, x_11, x_82);
lean_dec(x_10);
return x_95;
}
}
}
}
}
else
{
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_21);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_21, 0);
x_98 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
x_102 = l_Lean_FileMap_toPosition(x_16, x_97);
lean_dec(x_97);
lean_inc(x_102);
lean_ctor_set(x_21, 0, x_102);
if (x_18 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_free_object(x_98);
x_103 = lean_box(0);
x_104 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_100, x_15, x_102, x_21, x_14, x_103, x_10, x_11, x_101);
lean_dec(x_10);
return x_104;
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1;
lean_inc(x_100);
x_106 = l_Lean_MessageData_hasTag(x_105, x_100);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_21);
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_15);
lean_dec(x_10);
x_107 = lean_box(0);
lean_ctor_set(x_98, 0, x_107);
return x_98;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_free_object(x_98);
x_108 = lean_box(0);
x_109 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_100, x_15, x_102, x_21, x_14, x_108, x_10, x_11, x_101);
lean_dec(x_10);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_98, 0);
x_111 = lean_ctor_get(x_98, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_98);
x_112 = l_Lean_FileMap_toPosition(x_16, x_97);
lean_dec(x_97);
lean_inc(x_112);
lean_ctor_set(x_21, 0, x_112);
if (x_18 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_box(0);
x_114 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_110, x_15, x_112, x_21, x_14, x_113, x_10, x_11, x_111);
lean_dec(x_10);
return x_114;
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1;
lean_inc(x_110);
x_116 = l_Lean_MessageData_hasTag(x_115, x_110);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_21);
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_15);
lean_dec(x_10);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_111);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_box(0);
x_120 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_110, x_15, x_112, x_21, x_14, x_119, x_10, x_11, x_111);
lean_dec(x_10);
return x_120;
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_121 = lean_ctor_get(x_21, 0);
lean_inc(x_121);
lean_dec(x_21);
x_122 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = l_Lean_FileMap_toPosition(x_16, x_121);
lean_dec(x_121);
lean_inc(x_126);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
if (x_18 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
x_128 = lean_box(0);
x_129 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_123, x_15, x_126, x_127, x_14, x_128, x_10, x_11, x_124);
lean_dec(x_10);
return x_129;
}
else
{
lean_object* x_130; uint8_t x_131; 
x_130 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1;
lean_inc(x_123);
x_131 = l_Lean_MessageData_hasTag(x_130, x_123);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_123);
lean_dec(x_15);
lean_dec(x_10);
x_132 = lean_box(0);
if (lean_is_scalar(x_125)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_125;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_124);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_125);
x_134 = lean_box(0);
x_135 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_123, x_15, x_126, x_127, x_14, x_134, x_10, x_11, x_124);
lean_dec(x_10);
return x_135;
}
}
}
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_21, 0);
lean_inc(x_136);
lean_dec(x_21);
x_137 = !lean_is_exclusive(x_22);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_22, 0);
x_139 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_16);
x_143 = l_Lean_FileMap_toPosition(x_16, x_136);
lean_dec(x_136);
x_144 = l_Lean_FileMap_toPosition(x_16, x_138);
lean_dec(x_138);
lean_ctor_set(x_22, 0, x_144);
if (x_18 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_free_object(x_139);
x_145 = lean_box(0);
x_146 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_141, x_15, x_143, x_22, x_14, x_145, x_10, x_11, x_142);
lean_dec(x_10);
return x_146;
}
else
{
lean_object* x_147; uint8_t x_148; 
x_147 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1;
lean_inc(x_141);
x_148 = l_Lean_MessageData_hasTag(x_147, x_141);
if (x_148 == 0)
{
lean_object* x_149; 
lean_dec(x_22);
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_15);
lean_dec(x_10);
x_149 = lean_box(0);
lean_ctor_set(x_139, 0, x_149);
return x_139;
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_free_object(x_139);
x_150 = lean_box(0);
x_151 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_141, x_15, x_143, x_22, x_14, x_150, x_10, x_11, x_142);
lean_dec(x_10);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_139, 0);
x_153 = lean_ctor_get(x_139, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_139);
lean_inc(x_16);
x_154 = l_Lean_FileMap_toPosition(x_16, x_136);
lean_dec(x_136);
x_155 = l_Lean_FileMap_toPosition(x_16, x_138);
lean_dec(x_138);
lean_ctor_set(x_22, 0, x_155);
if (x_18 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_box(0);
x_157 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_152, x_15, x_154, x_22, x_14, x_156, x_10, x_11, x_153);
lean_dec(x_10);
return x_157;
}
else
{
lean_object* x_158; uint8_t x_159; 
x_158 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1;
lean_inc(x_152);
x_159 = l_Lean_MessageData_hasTag(x_158, x_152);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_22);
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_15);
lean_dec(x_10);
x_160 = lean_box(0);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_153);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_box(0);
x_163 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_152, x_15, x_154, x_22, x_14, x_162, x_10, x_11, x_153);
lean_dec(x_10);
return x_163;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_164 = lean_ctor_get(x_22, 0);
lean_inc(x_164);
lean_dec(x_22);
x_165 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
lean_inc(x_16);
x_169 = l_Lean_FileMap_toPosition(x_16, x_136);
lean_dec(x_136);
x_170 = l_Lean_FileMap_toPosition(x_16, x_164);
lean_dec(x_164);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
if (x_18 == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_168);
x_172 = lean_box(0);
x_173 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_166, x_15, x_169, x_171, x_14, x_172, x_10, x_11, x_167);
lean_dec(x_10);
return x_173;
}
else
{
lean_object* x_174; uint8_t x_175; 
x_174 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1;
lean_inc(x_166);
x_175 = l_Lean_MessageData_hasTag(x_174, x_166);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_166);
lean_dec(x_15);
lean_dec(x_10);
x_176 = lean_box(0);
if (lean_is_scalar(x_168)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_168;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_167);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_168);
x_178 = lean_box(0);
x_179 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_166, x_15, x_169, x_171, x_14, x_178, x_10, x_11, x_167);
lean_dec(x_10);
return x_179;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 5);
lean_inc(x_12);
x_13 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_interruptExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal exception: ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = 2;
x_14 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(x_11, x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = l_Lean_Elab_isAbortExceptionId(x_16);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1;
x_20 = lean_nat_dec_eq(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_8, 5);
lean_inc(x_21);
x_22 = l_Lean_InternalExceptionId_getName(x_16, x_10);
lean_dec(x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
lean_dec(x_21);
lean_free_object(x_1);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_MessageData_ofName(x_23);
x_26 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__3;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = 2;
x_31 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_29, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_8);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_io_error_to_string(x_33);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_MessageData_ofFormat(x_35);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_21);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = lean_io_error_to_string(x_37);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_MessageData_ofFormat(x_40);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_41);
lean_ctor_set(x_1, 0, x_21);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_free_object(x_1);
lean_dec(x_16);
lean_dec(x_8);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_10);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_1);
lean_dec(x_16);
lean_dec(x_8);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_10);
return x_46;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = l_Lean_Elab_isAbortExceptionId(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1;
x_50 = lean_nat_dec_eq(x_47, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_8, 5);
lean_inc(x_51);
x_52 = l_Lean_InternalExceptionId_getName(x_47, x_10);
lean_dec(x_47);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_MessageData_ofName(x_53);
x_56 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__3;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = 2;
x_61 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_59, x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_54);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_8);
x_62 = lean_ctor_get(x_52, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_64 = x_52;
} else {
 lean_dec_ref(x_52);
 x_64 = lean_box(0);
}
x_65 = lean_io_error_to_string(x_62);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = l_Lean_MessageData_ofFormat(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_51);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_47);
lean_dec(x_8);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_10);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_47);
lean_dec(x_8);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_10);
return x_73;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_inc(x_11);
x_16 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Elab_admitGoal(x_8, x_6, x_7, x_11, x_12, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Tactic_setGoals(x_9, x_1, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Elab_Tactic_focusAndDone___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l_Lean_Exception_isInterrupt(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_18);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Tactic_closeUsingOrAdmit___lambda__1(x_2, x_20, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_23, x_8, x_9, x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = l_Lean_Exception_isInterrupt(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Tactic_closeUsingOrAdmit___lambda__1(x_2, x_25, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_28, x_8, x_9, x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_closeUsingOrAdmit___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_saveState___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___lambda__1___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1;
x_2 = l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Exception_isInterrupt(x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isRuntime(x_17);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_21 = 0;
x_22 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_apply_10(x_2, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
return x_24;
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = l_Lean_Exception_isInterrupt(x_25);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_Exception_isRuntime(x_25);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = 0;
x_30 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_apply_10(x_2, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tryCatch___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Elab_Tactic_saveState___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = lean_apply_9(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_18);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_16);
x_22 = 0;
x_23 = l_Lean_Elab_Tactic_SavedState_restore(x_14, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_10(x_3, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
return x_25;
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = l_Lean_Exception_isInterrupt(x_26);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isRuntime(x_26);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = 0;
x_31 = l_Lean_Elab_Tactic_SavedState_restore(x_14, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_apply_10(x_3, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__1___boxed), 11, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__2), 12, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1;
x_2 = l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withoutRecover___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_12);
x_13 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_apply_9(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withoutRecover(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_orElse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Exception_isInterrupt(x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isRuntime(x_17);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_15);
lean_dec(x_17);
x_21 = 0;
x_22 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_apply_10(x_2, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
return x_25;
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = l_Lean_Exception_isInterrupt(x_26);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isRuntime(x_26);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
x_30 = 0;
x_31 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = lean_apply_10(x_2, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_orElse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_orElse___rarg), 11, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instOrElseTacticM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_orElse___rarg), 11, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instOrElseTacticM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_instOrElseTacticM___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_instAlternativeTacticM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_instAlternativeTacticM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Tactic_instAlternativeTacticM___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___closed__2;
x_12 = l_Lean_throwError___at_Lean_Elab_Tactic_instAlternativeTacticM___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Elab_Tactic_saveState___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_18);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_16);
lean_dec(x_18);
x_22 = 0;
x_23 = l_Lean_Elab_Tactic_SavedState_restore(x_14, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = lean_apply_10(x_3, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
return x_26;
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = l_Lean_Exception_isInterrupt(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_27);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_27);
x_31 = 0;
x_32 = l_Lean_Elab_Tactic_SavedState_restore(x_14, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = lean_apply_10(x_3, x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_33);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_28);
return x_37;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__2), 12, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_instMonadTacticM___closed__3;
x_2 = l_Lean_Elab_Tactic_instAlternativeTacticM___closed__1;
x_3 = l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_instAlternativeTacticM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_instAlternativeTacticM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_instAlternativeTacticM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l_Lean_Syntax_getPos_x3f(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg___boxed), 10, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg___lambda__1), 11, 1);
lean_closure_set(x_20, 0, x_18);
x_21 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_evalTactic_eval___spec__2(x_16, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_withMacroExpansion___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 6);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg(x_10, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_10, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 6);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_10);
x_30 = lean_apply_10(x_2, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_take(x_10, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_34, 6);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
lean_ctor_set(x_35, 1, x_41);
x_42 = lean_st_ref_set(x_10, x_34, x_36);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_23);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_47);
lean_ctor_set(x_34, 6, x_50);
x_51 = lean_st_ref_set(x_10, x_34, x_36);
lean_dec(x_10);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_23);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
x_57 = lean_ctor_get(x_34, 2);
x_58 = lean_ctor_get(x_34, 3);
x_59 = lean_ctor_get(x_34, 4);
x_60 = lean_ctor_get(x_34, 5);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
x_61 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_63 = x_35;
} else {
 lean_dec_ref(x_35);
 x_63 = lean_box(0);
}
x_64 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 1);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_61);
x_66 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_56);
lean_ctor_set(x_66, 2, x_57);
lean_ctor_set(x_66, 3, x_58);
lean_ctor_set(x_66, 4, x_59);
lean_ctor_set(x_66, 5, x_60);
lean_ctor_set(x_66, 6, x_65);
x_67 = lean_st_ref_set(x_10, x_66, x_36);
lean_dec(x_10);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_23);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_10);
x_71 = !lean_is_exclusive(x_30);
if (x_71 == 0)
{
return x_30;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_30, 0);
x_73 = lean_ctor_get(x_30, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_30);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_22, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_22, 1);
lean_inc(x_76);
lean_dec(x_22);
x_77 = lean_st_ref_get(x_10, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 6);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
lean_inc(x_10);
x_82 = lean_apply_10(x_2, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_take(x_10, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_86, 6);
lean_dec(x_90);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_87, 1);
lean_dec(x_92);
x_93 = l_Lean_PersistentArray_push___rarg(x_20, x_83);
lean_ctor_set(x_87, 1, x_93);
x_94 = lean_st_ref_set(x_10, x_86, x_88);
lean_dec(x_10);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
lean_ctor_set_tag(x_94, 1);
lean_ctor_set(x_94, 0, x_75);
return x_94;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_75);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
x_100 = lean_ctor_get(x_87, 0);
lean_inc(x_100);
lean_dec(x_87);
x_101 = l_Lean_PersistentArray_push___rarg(x_20, x_83);
x_102 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_99);
lean_ctor_set(x_86, 6, x_102);
x_103 = lean_st_ref_set(x_10, x_86, x_88);
lean_dec(x_10);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
 lean_ctor_set_tag(x_106, 1);
}
lean_ctor_set(x_106, 0, x_75);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_107 = lean_ctor_get(x_86, 0);
x_108 = lean_ctor_get(x_86, 1);
x_109 = lean_ctor_get(x_86, 2);
x_110 = lean_ctor_get(x_86, 3);
x_111 = lean_ctor_get(x_86, 4);
x_112 = lean_ctor_get(x_86, 5);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_86);
x_113 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
x_114 = lean_ctor_get(x_87, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_115 = x_87;
} else {
 lean_dec_ref(x_87);
 x_115 = lean_box(0);
}
x_116 = l_Lean_PersistentArray_push___rarg(x_20, x_83);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 1);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_113);
x_118 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_118, 0, x_107);
lean_ctor_set(x_118, 1, x_108);
lean_ctor_set(x_118, 2, x_109);
lean_ctor_set(x_118, 3, x_110);
lean_ctor_set(x_118, 4, x_111);
lean_ctor_set(x_118, 5, x_112);
lean_ctor_set(x_118, 6, x_117);
x_119 = lean_st_ref_set(x_10, x_118, x_88);
lean_dec(x_10);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
 lean_ctor_set_tag(x_122, 1);
}
lean_ctor_set(x_122, 0, x_75);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_dec(x_75);
lean_dec(x_20);
lean_dec(x_10);
x_123 = !lean_is_exclusive(x_82);
if (x_123 == 0)
{
return x_82;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_82, 0);
x_125 = lean_ctor_get(x_82, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_82);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_withMacroExpansion___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_withMacroExpansion___spec__2___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_2);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg___lambda__1___boxed), 12, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_withMacroExpansion___spec__2___rarg(x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_6, 2, x_16);
x_17 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*9);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*9 + 1);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*9 + 2);
x_24 = lean_ctor_get(x_6, 3);
x_25 = lean_ctor_get(x_6, 4);
x_26 = lean_ctor_get(x_6, 5);
x_27 = lean_ctor_get(x_6, 6);
x_28 = lean_ctor_get_uint8(x_6, sizeof(void*)*9 + 3);
x_29 = lean_ctor_get_uint8(x_6, sizeof(void*)*9 + 4);
x_30 = lean_ctor_get_uint8(x_6, sizeof(void*)*9 + 5);
x_31 = lean_ctor_get_uint8(x_6, sizeof(void*)*9 + 6);
x_32 = lean_ctor_get_uint8(x_6, sizeof(void*)*9 + 7);
x_33 = lean_ctor_get(x_6, 7);
x_34 = lean_ctor_get(x_6, 8);
x_35 = lean_ctor_get_uint8(x_6, sizeof(void*)*9 + 8);
x_36 = lean_ctor_get_uint8(x_6, sizeof(void*)*9 + 9);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_2);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_20);
x_39 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_19);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_24);
lean_ctor_set(x_39, 4, x_25);
lean_ctor_set(x_39, 5, x_26);
lean_ctor_set(x_39, 6, x_27);
lean_ctor_set(x_39, 7, x_33);
lean_ctor_set(x_39, 8, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*9, x_21);
lean_ctor_set_uint8(x_39, sizeof(void*)*9 + 1, x_22);
lean_ctor_set_uint8(x_39, sizeof(void*)*9 + 2, x_23);
lean_ctor_set_uint8(x_39, sizeof(void*)*9 + 3, x_28);
lean_ctor_set_uint8(x_39, sizeof(void*)*9 + 4, x_29);
lean_ctor_set_uint8(x_39, sizeof(void*)*9 + 5, x_30);
lean_ctor_set_uint8(x_39, sizeof(void*)*9 + 6, x_31);
lean_ctor_set_uint8(x_39, sizeof(void*)*9 + 7, x_32);
lean_ctor_set_uint8(x_39, sizeof(void*)*9 + 8, x_35);
lean_ctor_set_uint8(x_39, sizeof(void*)*9 + 9, x_36);
x_40 = lean_apply_9(x_3, x_4, x_5, x_39, x_7, x_8, x_9, x_10, x_11, x_12);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMacroExpansion___rarg___lambda__1), 12, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
x_14 = l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMacroExpansion___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg___lambda__1___boxed), 12, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_evalTactic_eval___spec__2(x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_adaptExpander___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_5, 2, x_15);
x_16 = l_Lean_Elab_Tactic_evalTactic(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_23 = lean_ctor_get(x_5, 3);
x_24 = lean_ctor_get(x_5, 4);
x_25 = lean_ctor_get(x_5, 5);
x_26 = lean_ctor_get(x_5, 6);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_31 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_32 = lean_ctor_get(x_5, 7);
x_33 = lean_ctor_get(x_5, 8);
x_34 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_35 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
lean_inc(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_2);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_19);
x_38 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_18);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_23);
lean_ctor_set(x_38, 4, x_24);
lean_ctor_set(x_38, 5, x_25);
lean_ctor_set(x_38, 6, x_26);
lean_ctor_set(x_38, 7, x_32);
lean_ctor_set(x_38, 8, x_33);
lean_ctor_set_uint8(x_38, sizeof(void*)*9, x_20);
lean_ctor_set_uint8(x_38, sizeof(void*)*9 + 1, x_21);
lean_ctor_set_uint8(x_38, sizeof(void*)*9 + 2, x_22);
lean_ctor_set_uint8(x_38, sizeof(void*)*9 + 3, x_27);
lean_ctor_set_uint8(x_38, sizeof(void*)*9 + 4, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*9 + 5, x_29);
lean_ctor_set_uint8(x_38, sizeof(void*)*9 + 6, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*9 + 7, x_31);
lean_ctor_set_uint8(x_38, sizeof(void*)*9 + 8, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*9 + 9, x_35);
x_39 = l_Lean_Elab_Tactic_evalTactic(x_2, x_3, x_4, x_38, x_6, x_7, x_8, x_9, x_10, x_11);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_adaptExpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = lean_apply_10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_adaptExpander___lambda__1), 11, 2);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(x_2, x_13, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_appendGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_List_appendTR___rarg(x_12, x_1);
x_15 = lean_st_ref_set(x_3, x_14, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_appendGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_appendGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_getGoals___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_st_ref_take(x_3, x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_List_appendTR___rarg(x_1, x_16);
x_20 = lean_st_ref_set(x_3, x_19, x_18);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_replaceMainGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_replaceMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = l_Lean_MVarId_isAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_13);
x_19 = l_Lean_Elab_Tactic_setGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_13);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_free_object(x_1);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_1 = x_14;
x_10 = x_24;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_28 = l_Lean_MVarId_isAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
lean_inc(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
x_33 = l_Lean_Elab_Tactic_setGoals(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
x_1 = x_27;
x_10 = x_37;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Elab_Tactic_getGoals___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_getMainGoal_loop(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_MVarId_getDecl(x_11, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainTag(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_st_ref_get(x_7, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_instantiateMVarsCore(x_16, x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_take(x_7, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
lean_ctor_set(x_21, 0, x_19);
x_25 = lean_st_ref_set(x_7, x_21, x_22);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_18);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_21, 1);
x_31 = lean_ctor_get(x_21, 2);
x_32 = lean_ctor_get(x_21, 3);
x_33 = lean_ctor_get(x_21, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_32);
lean_ctor_set(x_34, 4, x_33);
x_35 = lean_st_ref_set(x_7, x_34, x_22);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMainContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTacticAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_box(0);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_16);
lean_ctor_set(x_12, 0, x_2);
x_17 = l_Lean_Elab_Tactic_setGoals(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Tactic_evalTactic(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Tactic_setGoals(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = l_Lean_Elab_Tactic_setGoals(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_Tactic_setGoals(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_44 = l_Lean_Elab_Tactic_evalTactic(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Elab_Tactic_setGoals(x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_44, 1);
lean_inc(x_56);
lean_dec(x_44);
x_57 = l_Lean_Elab_Tactic_setGoals(x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
 lean_ctor_set_tag(x_60, 1);
}
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTacticAtRaw(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Tactic_setGoals(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Elab_Tactic_evalTactic(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic failed, resulting expression contains metavariables", 58, 58);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_15 = l_Lean_Meta_getMVars(x_13, x_6, x_7, x_8, x_9, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_17, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Lean_Expr_hasExprMVar(x_13);
if (x_24 == 0)
{
lean_object* x_25; 
lean_free_object(x_15);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = lean_box(0);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_20);
x_26 = l_Lean_indentExpr(x_13);
x_27 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_26);
lean_ctor_set(x_15, 0, x_27);
x_28 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_28);
lean_ctor_set(x_11, 0, x_15);
x_29 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_Lean_Expr_hasExprMVar(x_13);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_free_object(x_15);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = l_Lean_indentExpr(x_13);
x_35 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_34);
lean_ctor_set(x_15, 0, x_35);
x_36 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_36);
lean_ctor_set(x_11, 0, x_15);
x_37 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_15);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_15);
x_44 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_45 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_42, x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = l_Lean_Expr_hasExprMVar(x_13);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
x_51 = l_Lean_indentExpr(x_13);
x_52 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_54);
lean_ctor_set(x_11, 0, x_53);
x_55 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_ctor_get(x_45, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_45, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_58 = x_45;
} else {
 lean_dec_ref(x_45);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_11, 0);
x_61 = lean_ctor_get(x_11, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_11);
lean_inc(x_60);
x_62 = l_Lean_Meta_getMVars(x_60, x_6, x_7, x_8, x_9, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_67 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_63, x_66, x_4, x_5, x_6, x_7, x_8, x_9, x_64);
lean_dec(x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = l_Lean_Expr_hasExprMVar(x_60);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_65);
lean_dec(x_60);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_69);
x_73 = l_Lean_indentExpr(x_60);
x_74 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2;
if (lean_is_scalar(x_65)) {
 x_75 = lean_alloc_ctor(7, 2, 0);
} else {
 x_75 = x_65;
 lean_ctor_set_tag(x_75, 7);
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_65);
lean_dec(x_60);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_79 = lean_ctor_get(x_67, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_67, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_81 = x_67;
} else {
 lean_dec_ref(x_67);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_ensureHasNoMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attempting to close the goal using", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nthis is often due occurs-check failure", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_14);
x_16 = lean_checked_assign(x_14, x_1, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_indentExpr(x_1);
x_21 = l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_14, x_25, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Tactic_replaceMainGoal(x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
return x_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_3 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Elab_Tactic_closeMainGoal___lambda__1(x_2, x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_15 = l_Lean_Elab_Tactic_ensureHasNoMVars(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Tactic_closeMainGoal___lambda__1(x_2, x_1, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_closeMainGoal___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_Tactic_closeMainGoal(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaMAtMain___rarg___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaMAtMain___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaMAtMain___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Elab_Tactic_replaceMainGoal(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_17);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_replaceMainGoal(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Tactic_replaceMainGoal(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Elab_Tactic_replaceMainGoal(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic1___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaTactic1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Tactic_replaceMainGoal(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaFinishingTactic___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaFinishingTactic___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Elab_Tactic_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = l_Lean_Exception_isInterrupt(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Exception_isRuntime(x_23);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; uint8_t x_29; 
lean_free_object(x_14);
lean_dec(x_23);
x_27 = 0;
x_28 = l_Lean_Elab_Tactic_SavedState_restore(x_12, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = l_Lean_Exception_isInterrupt(x_35);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Exception_isRuntime(x_35);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_35);
x_39 = 0;
x_40 = l_Lean_Elab_Tactic_SavedState_restore(x_12, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_36);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tryTactic_x3f___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Elab_Tactic_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
x_26 = l_Lean_Exception_isInterrupt(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isRuntime(x_24);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; uint8_t x_30; 
lean_free_object(x_14);
lean_dec(x_24);
x_28 = 0;
x_29 = l_Lean_Elab_Tactic_SavedState_restore(x_12, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(x_28);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = l_Lean_Exception_isInterrupt(x_36);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_Exception_isRuntime(x_36);
if (x_39 == 0)
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_36);
x_40 = 0;
x_41 = l_Lean_Elab_Tactic_SavedState_restore(x_12, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_box(x_40);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_37);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tryTactic___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_16 = l_Lean_MetavarContext_isAnonymousMVar(x_1, x_14);
if (x_16 == 0)
{
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_2 = x_15;
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = l_Lean_MetavarContext_isAnonymousMVar(x_10, x_6);
if (x_11 == 0)
{
lean_dec(x_6);
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_free_object(x_5);
x_13 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1;
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_9);
lean_inc(x_2);
x_16 = lean_name_append_index_after(x_2, x_9);
lean_inc(x_1);
x_17 = l_Lean_Name_append(x_1, x_16);
x_18 = l_Lean_MetavarContext_setMVarUserName(x_10, x_6, x_17);
x_19 = lean_box(0);
x_20 = lean_apply_3(x_13, x_9, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_4 = x_7;
x_5 = x_22;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_1);
x_24 = l_Lean_MetavarContext_setMVarUserName(x_10, x_6, x_1);
x_25 = lean_box(0);
x_26 = lean_apply_3(x_13, x_9, x_24, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_4 = x_7;
x_5 = x_28;
goto _start;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
lean_inc(x_31);
x_32 = l_Lean_MetavarContext_isAnonymousMVar(x_31, x_6);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
x_4 = x_7;
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1;
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_dec_eq(x_3, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_inc(x_30);
lean_inc(x_2);
x_38 = lean_name_append_index_after(x_2, x_30);
lean_inc(x_1);
x_39 = l_Lean_Name_append(x_1, x_38);
x_40 = l_Lean_MetavarContext_setMVarUserName(x_31, x_6, x_39);
x_41 = lean_box(0);
x_42 = lean_apply_3(x_35, x_30, x_40, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_4 = x_7;
x_5 = x_44;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_1);
x_46 = l_Lean_MetavarContext_setMVarUserName(x_31, x_6, x_1);
x_47 = lean_box(0);
x_48 = lean_apply_3(x_35, x_30, x_46, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_4 = x_7;
x_5 = x_50;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_st_ref_get(x_9, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(x_16, x_3, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_take(x_9, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_21, 1, x_26);
lean_ctor_set(x_21, 0, x_27);
x_28 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(x_1, x_2, x_19, x_3, x_21);
lean_dec(x_19);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_ctor_set(x_23, 0, x_29);
x_30 = lean_st_ref_set(x_9, x_23, x_25);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_21, 1);
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
x_40 = lean_ctor_get(x_23, 2);
x_41 = lean_ctor_get(x_23, 3);
x_42 = lean_ctor_get(x_23, 4);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_43 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_21, 1, x_38);
lean_ctor_set(x_21, 0, x_43);
x_44 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(x_1, x_2, x_19, x_3, x_21);
lean_dec(x_19);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_40);
lean_ctor_set(x_46, 3, x_41);
lean_ctor_set(x_46, 4, x_42);
x_47 = lean_st_ref_set(x_9, x_46, x_37);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_52 = lean_ctor_get(x_21, 0);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_21);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 4);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_54);
x_62 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(x_1, x_2, x_19, x_3, x_61);
lean_dec(x_19);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(0, 5, 0);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_55);
lean_ctor_set(x_64, 2, x_56);
lean_ctor_set(x_64, 3, x_57);
lean_ctor_set(x_64, 4, x_58);
x_65 = lean_st_ref_set(x_9, x_64, x_53);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isIdent(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__2;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getId(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getNameOfIdent_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_replaceRef(x_1, x_4);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_3(x_6, lean_box(0), x_5, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_array_mk(x_8);
x_10 = lean_box(2);
x_11 = l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__3;
x_12 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_9);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withCaseRef___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_5);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withCaseRef___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_withCaseRef___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__2;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__3;
x_2 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__4;
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__6;
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__8;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__9;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__10;
x_2 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Basic", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__11;
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__13;
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__15;
x_2 = lean_unsigned_to_nat(8297u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__1;
x_3 = 0;
x_4 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__16;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8339____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__15;
x_2 = lean_unsigned_to_nat(8339u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8339_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__2;
x_3 = 0;
x_4 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8339____closed__1;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_goalsToMessageData___closed__1 = _init_l_Lean_Elab_goalsToMessageData___closed__1();
lean_mark_persistent(l_Lean_Elab_goalsToMessageData___closed__1);
l_Lean_Elab_goalsToMessageData___closed__2 = _init_l_Lean_Elab_goalsToMessageData___closed__2();
lean_mark_persistent(l_Lean_Elab_goalsToMessageData___closed__2);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__1 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__1);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__2 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__2);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__3 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__3);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__4 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__4);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__5 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__5);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__6 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__6);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__7 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__7);
l_Lean_Elab_Tactic_Context_recover___default = _init_l_Lean_Elab_Tactic_Context_recover___default();
l_Lean_Elab_Tactic_instMonadTacticM___closed__1 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__1);
l_Lean_Elab_Tactic_instMonadTacticM___closed__2 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__2);
l_Lean_Elab_Tactic_instMonadTacticM___closed__3 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__3);
l_Lean_Elab_Tactic_instMonadTacticM___closed__4 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__4);
l_Lean_Elab_Tactic_instMonadTacticM___closed__5 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__5);
l_Lean_Elab_Tactic_instMonadTacticM___closed__6 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__6);
l_Lean_Elab_Tactic_instMonadTacticM = _init_l_Lean_Elab_Tactic_instMonadTacticM();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM);
l_Lean_Elab_Tactic_instInhabitedTacticM___rarg___closed__1 = _init_l_Lean_Elab_Tactic_instInhabitedTacticM___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_instInhabitedTacticM___rarg___closed__1);
l_Lean_Elab_Tactic_instInhabitedTacticM___rarg___closed__2 = _init_l_Lean_Elab_Tactic_instInhabitedTacticM___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_instInhabitedTacticM___rarg___closed__2);
l_Lean_Elab_Tactic_run___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_run___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_run___lambda__1___closed__1);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__1 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__1);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__2 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__2);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__3 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__3);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__4 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__4);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__5 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__5);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__6 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__6);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__7 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__7);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__8 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__8);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__9 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__9);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__10 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__10);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__11 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__11);
if (builtin) {res = l_Lean_Elab_Tactic_mkTacticAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_tacticElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute);
lean_dec_ref(res);
}l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__1 = _init_l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__1);
l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__2 = _init_l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__2);
l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__3 = _init_l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg___closed__3);
l_Lean_Elab_Tactic_evalTactic_throwExs___closed__1 = _init_l_Lean_Elab_Tactic_evalTactic_throwExs___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic_throwExs___closed__1);
l_Lean_Elab_Tactic_evalTactic_throwExs___closed__2 = _init_l_Lean_Elab_Tactic_evalTactic_throwExs___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic_throwExs___closed__2);
l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__1___closed__1);
l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__1 = _init_l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__1();
l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__2 = _init_l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__2___closed__2);
l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__1);
l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Tactic_evalTactic_handleEx___spec__4___closed__2);
l_Lean_Elab_Tactic_evalTactic_handleEx___closed__1 = _init_l_Lean_Elab_Tactic_evalTactic_handleEx___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic_handleEx___closed__1);
l_Lean_Elab_Tactic_evalTactic_handleEx___closed__2 = _init_l_Lean_Elab_Tactic_evalTactic_handleEx___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic_handleEx___closed__2);
l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__1 = _init_l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__1);
l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__2 = _init_l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_isIncrementalElab___at_Lean_Elab_Tactic_evalTactic_eval___spec__1___closed__2);
l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__1 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__1);
l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__2 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__2);
l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__3 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__3);
l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__4 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__3___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__5___closed__2);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic_expandEval___spec__6___rarg___closed__1);
l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__1);
l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__2);
l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__3 = _init_l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__3);
l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__4 = _init_l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__4);
l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__5 = _init_l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__5);
l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__6 = _init_l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic_expandEval___lambda__3___closed__6);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__2___closed__1);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___closed__1);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__3___closed__2);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__1);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__2);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__3 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__3();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__3);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__4 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__4();
l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__5 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_evalTactic___spec__3___lambda__4___closed__5();
l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__1);
l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__2);
l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__3);
l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__4 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__4);
l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__5 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__5);
l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__6 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__4___closed__6);
l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__1 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__1);
l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__2 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__2);
l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__3 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__3);
l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__4 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__4);
l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__5 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__5);
l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__6 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__6);
l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__7 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__7);
l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__8 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__6___closed__8);
l_Lean_Elab_Tactic_evalTactic___lambda__6___boxed__const__1 = _init_l_Lean_Elab_Tactic_evalTactic___lambda__6___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___lambda__6___boxed__const__1);
l_Lean_Elab_Tactic_evalTactic___closed__1 = _init_l_Lean_Elab_Tactic_evalTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___closed__1);
l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__1 = _init_l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__1);
l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__2 = _init_l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__2);
l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg___closed__1);
l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__2___closed__1 = _init_l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__2___closed__1();
lean_mark_persistent(l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___lambda__2___closed__1);
l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1 = _init_l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1();
lean_mark_persistent(l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__1);
l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__2 = _init_l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__2();
lean_mark_persistent(l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___closed__2);
l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1 = _init_l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1);
l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2 = _init_l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2);
l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__3 = _init_l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__3();
lean_mark_persistent(l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__3);
l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1 = _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1);
l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__2 = _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__2);
l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__3 = _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__3);
l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM = _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM);
l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1 = _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1);
l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2 = _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2);
l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__3 = _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__3);
l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM = _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM);
l_Lean_Elab_Tactic_instOrElseTacticM___closed__1 = _init_l_Lean_Elab_Tactic_instOrElseTacticM___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_instOrElseTacticM___closed__1);
l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___closed__1);
l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_instAlternativeTacticM___lambda__1___closed__2);
l_Lean_Elab_Tactic_instAlternativeTacticM___closed__1 = _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_instAlternativeTacticM___closed__1);
l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2 = _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2);
l_Lean_Elab_Tactic_instAlternativeTacticM___closed__3 = _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_instAlternativeTacticM___closed__3);
l_Lean_Elab_Tactic_instAlternativeTacticM = _init_l_Lean_Elab_Tactic_instAlternativeTacticM();
lean_mark_persistent(l_Lean_Elab_Tactic_instAlternativeTacticM);
l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1 = _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1);
l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2 = _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2);
l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__1);
l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__2);
l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__3);
l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_closeMainGoal___lambda__1___closed__4);
l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1);
l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__1 = _init_l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__1);
l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__2 = _init_l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__2);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__1 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__1);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__2 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__2);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__3 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__3);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__4 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__4);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__5 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__5);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__6 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__6);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__7 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__7);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__8 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__8);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__9 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__9);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__10 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__10);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__11 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__11);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__12 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__12);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__13 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__13);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__14 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__14);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__15 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__15);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__16 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297____closed__16);
if (builtin) {res = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8297_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8339____closed__1 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8339____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8339____closed__1);
if (builtin) {res = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_8339_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

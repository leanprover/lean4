// Lean compiler output
// Module: Lean.Meta.SynthInstance
// Imports: Init.Data.Array.InsertionSort Lean.Meta.Basic Lean.Meta.Instances Lean.Meta.AbstractMVars Lean.Meta.Check Lean.Util.Profile
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
extern lean_object* l_Lean_Meta_isDefEqStuckExceptionId;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkSystem___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__4;
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__3;
lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_recordSynthPendingFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SynthInstance_isNewAnswer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkSystem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SynthInstance_isNewAnswer(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__5;
static lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkGeneratorNode_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_83_;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__0;
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__8;
static lean_object* l_Lean_Meta_SynthInstance_resume___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedConsumerNode;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_SynthInstance_consume_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedInstance;
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__0;
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getSubgoals___closed__0;
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_SynthInstance_getInstances_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_9910_;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__3;
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__10;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__6;
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__1;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_StateT_get(lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_synth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_9910_;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_isNewAnswer___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__2;
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__5;
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_44_;
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at___Lean_Meta_SynthInstance_getInstances_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__4;
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__0;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__2;
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SynthInstance_generate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_SynthInstance_getInstances_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_9910_;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__0;
static lean_object* l_Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5___closed__0;
uint8_t lean_float_decLt(double, double);
static lean_object* l_panic___at___Lean_Meta_SynthInstance_getInstances_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_trySynthInstance___closed__0;
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getMaxHeartbeats___boxed(lean_object*);
lean_object* l_Option_toLOption___redArg(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_main___lam__0___closed__6;
static lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__1;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SynthInstance_getInstances_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_hashSynthInstanceCacheKey____x40_Lean_Meta_Basic___hyg_1583_(lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_83_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_main_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__0;
static lean_object* l_Lean_Meta_synthInstanceCore_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__4;
static lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__7;
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___lam__0___closed__0;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_SynthInstance_getInstances_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_SynthInstance_getInstances_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkSystem___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_9910_;
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__5;
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__0;
static lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__8;
lean_object* l_Lean_Meta_hashSynthInstanceCacheKey____x40_Lean_Meta_Basic___hyg_1583____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_83_;
static lean_object* l_Lean_Meta_SynthInstance_resume___lam__3___closed__1;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_SynthInstance_getInstances_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_SynthInstance_getSubgoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_9910_;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_withIncRecDepth___at___Lean_Meta_transformWithCache_visit___at___Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0_spec__0_spec__9_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFailedToSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__1;
static lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_44_;
static lean_object* l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_SynthInstance___hyg_9910_;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__6;
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_SynthInstance_resume_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__0;
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__3;
static lean_object* l_Lean_Meta_SynthInstance_main___lam__0___closed__7;
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_5_;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___lam__3___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___Lean_Meta_SynthInstance_consume_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__1(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__1;
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_5_;
static lean_object* l_Lean_Meta_SynthInstance_checkSystem___redArg___closed__0;
static lean_object* l_Lean_Meta_SynthInstance_generate___lam__0___closed__3;
static lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getInstances_spec__8(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__1;
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_5_;
lean_object* l_Lean_MetavarContext_getLevelDepth(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__3;
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__0;
LEAN_EXPORT uint8_t l_Lean_Meta_SynthInstance_Waiter_isRoot(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_main___lam__0___closed__4;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_SynthInstance_consume_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_resume___lam__0___closed__3;
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_SynthInstance_getInstances_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__0;
static lean_object* l_Lean_Meta_SynthInstance_main___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__5;
static double l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_SynthInstance___hyg_9910_;
lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getSubgoals___closed__1;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___redArg(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__5;
LEAN_EXPORT uint8_t l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_hasUnusedArguments(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SynthInstance_getInstances_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFailedToSynthesize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_main___lam__0___closed__5;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_synth_pending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__0;
static lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__1;
lean_object* lean_array_to_list(lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedAnswer;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__0;
lean_object* lean_io_mono_nanos_now(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__2;
uint8_t l_Lean_Level_hasMVar(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getSubgoals_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__9;
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__2;
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__3;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__0;
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__4;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__1;
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_44_;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__4;
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__0___closed__0;
extern lean_object* l_Lean_trace_profiler_threshold;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__3;
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_consume_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_44_;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__6;
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_83_;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getMaxHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_maxSize;
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_9910_;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_wakeUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_SynthInstance_getInstances_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__2;
static lean_object* l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_SynthInstance___hyg_5_;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__0;
static lean_object* l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_SynthInstance___hyg_9910_;
static lean_object* l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__0;
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__1;
lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Meta_SynthInstance_main_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_RecDepth___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkSystem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_SynthInstance_getInstances_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_addAnswer_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_AbstractMVarsResult_numMVars(lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__2;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstanceCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4;
static lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_9910_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_main___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_83_;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode;
static lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__3;
lean_object* l_Lean_exceptOptionEmoji___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_hashLevelMVarId____x40_Lean_Level___hyg_490_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_83_;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_maxSynthPendingDepth;
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_Waiter_isRoot___boxed(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_main_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_addAnswer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_recordInstance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__0;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_Meta_SynthInstance_MkTableKey_normExpr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Meta_SynthInstance_main_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_generate___lam__1___closed__0;
static lean_object* l_Lean_Meta_SynthInstance_getNextToResume___redArg___closed__0;
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___lam__0___closed__1;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__2;
static lean_object* l_Lean_Meta_SynthInstance_generate___closed__0;
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__9;
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__0;
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SynthInstance_generate_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_synthInstanceCore_x3f_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_generate___lam__0___closed__2;
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__1;
static lean_object* l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_SynthInstance___hyg_9910_;
static double l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__5;
static lean_object* l_Lean_Meta_synthInstance_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__6;
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__0;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SynthInstance_isNewAnswer_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_applyAbstractResult_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__2;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__3;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__0;
static lean_object* l_Lean_Meta_SynthInstance_main___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_9910_;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__10;
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__6;
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isDelayedAssigned___at___Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_9910_;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_maxHeartbeats;
static lean_object* l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg___closed__0;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__6;
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_SynthInstance_getEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_83_;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg___closed__0;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Meta_SynthInstance_main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_83_;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_backward_synthInstance_canonInstances;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_wakeUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_consume_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_panic___at___Lean_Meta_SynthInstance_getEntry_spec__0___closed__0;
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___lam__0___closed__4;
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_Meta_beqSynthInstanceCacheKey____x40_Lean_Meta_Basic___hyg_1633____boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_useDiagnosticMsg;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_hasUnusedArguments___boxed(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__7;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_synthInstanceCore_x3f_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_5_(lean_object*);
lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getSubgoals_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_SynthInstance_consume_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__5;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__11;
static lean_object* l_Lean_Meta_SynthInstance_generate___lam__0___closed__0;
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_hashMVarId____x40_Lean_Expr___hyg_1840_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_SynthInstance_getInstances_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__4;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_SynthInstance_consume_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__9;
static lean_object* l_Lean_Meta_SynthInstance_generate___lam__0___closed__1;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_applyCachedAbstractResult_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__4;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2;
static lean_object* l_Lean_Meta_SynthInstance_main___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___redArg___boxed(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__4;
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___Lean_Meta_SynthInstance_consume_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_44_(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__7;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SynthInstance_MkTableKey_normExpr_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_SynthInstance___hyg_9910_;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getInstances_spec__8___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
static lean_object* l_Lean_Meta_SynthInstance_resume___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_sub(double, double);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__5;
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_44_;
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_containsOnBranch_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthInstance", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxHeartbeats", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_5_;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum amount of heartbeats per typeclass resolution problem. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit", 147, 147);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_5_;
x_2 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = lean_unsigned_to_nat(20000u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_SynthInstance___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_5_;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_4 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_5_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_5_;
x_4 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_SynthInstance___hyg_5_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_RecDepth___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxSize", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_44_;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum number of instances used to construct a solution in the type class instance synthesis procedure", 103, 103);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_44_;
x_2 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = lean_unsigned_to_nat(128u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_44_;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_4 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_5_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_44_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_44_;
x_3 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_44_;
x_4 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_44_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_RecDepth___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_83_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backward", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_83_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("canonInstances", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_83_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_83_;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_83_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_83_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backward compatibility", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_83_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("use optimization that relies on 'morally canonical' instances during type class resolution", 90, 90);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_83_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_83_;
x_2 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_83_;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_83_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_83_;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_83_;
x_4 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_5 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_5_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_83_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_83_;
x_3 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_83_;
x_4 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_83_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_synthInstance_maxHeartbeats;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getMaxHeartbeats(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__0;
x_3 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_1, x_2);
x_4 = lean_unsigned_to_nat(1000u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getMaxHeartbeats___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_getMaxHeartbeats(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__3;
x_2 = l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedInstance() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__6;
x_2 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__5;
x_3 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4;
x_4 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3;
x_5 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2;
x_6 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set(x_8, 8, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__9() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_4 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__7;
x_5 = l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__2;
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__7;
x_4 = l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__2;
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedConsumerNode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SynthInstance_Waiter_isRoot(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_Waiter_isRoot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SynthInstance_Waiter_isRoot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 3, x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_1, x_11);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__1;
x_2 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__5;
x_2 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__4;
x_3 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__3;
x_4 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__2;
x_5 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__6;
x_2 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__9;
x_2 = lean_alloc_closure((void*)(l_StateT_get), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lam__1), 2, 0);
x_3 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__9;
x_4 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__10;
x_5 = lean_alloc_closure((void*)(l_StateT_bind), 8, 7);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, lean_box(0));
lean_closure_set(x_5, 4, lean_box(0));
lean_closure_set(x_5, 5, x_4);
lean_closure_set(x_5, 6, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_tc", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Level_hasMVar(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_inc(x_5);
x_6 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_5, x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_10 = lean_ptr_addr(x_8);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = l_Lean_Level_succ___override(x_8);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
}
else
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_16 = lean_ptr_addr(x_13);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = l_Lean_Level_succ___override(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; size_t x_36; size_t x_37; uint8_t x_38; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
x_23 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_21, x_2);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc(x_22);
x_26 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_22, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_36 = lean_ptr_addr(x_21);
lean_dec(x_21);
x_37 = lean_ptr_addr(x_24);
x_38 = lean_usize_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_dec(x_22);
x_30 = x_38;
goto block_35;
}
else
{
size_t x_39; size_t x_40; uint8_t x_41; 
x_39 = lean_ptr_addr(x_22);
lean_dec(x_22);
x_40 = lean_ptr_addr(x_27);
x_41 = lean_usize_dec_eq(x_39, x_40);
x_30 = x_41;
goto block_35;
}
block_35:
{
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = l_Lean_mkLevelMax_x27(x_24, x_27);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_simpLevelMax_x27(x_24, x_27, x_1);
lean_dec(x_1);
lean_dec(x_27);
lean_dec(x_24);
if (lean_is_scalar(x_29)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_29;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
}
case 3:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; size_t x_57; size_t x_58; uint8_t x_59; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
lean_inc(x_42);
x_44 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_42, x_2);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
lean_inc(x_43);
x_47 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_43, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_57 = lean_ptr_addr(x_42);
lean_dec(x_42);
x_58 = lean_ptr_addr(x_45);
x_59 = lean_usize_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_dec(x_43);
x_51 = x_59;
goto block_56;
}
else
{
size_t x_60; size_t x_61; uint8_t x_62; 
x_60 = lean_ptr_addr(x_43);
lean_dec(x_43);
x_61 = lean_ptr_addr(x_48);
x_62 = lean_usize_dec_eq(x_60, x_61);
x_51 = x_62;
goto block_56;
}
block_56:
{
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
x_52 = l_Lean_mkLevelIMax_x27(x_45, x_48);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_simpLevelIMax_x27(x_45, x_48, x_1);
lean_dec(x_1);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
case 5:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_63 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
lean_inc(x_64);
lean_inc_ref(x_63);
x_69 = l_Lean_MetavarContext_getLevelDepth(x_63, x_64);
x_70 = lean_nat_dec_eq(x_69, x_68);
lean_dec(x_68);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec_ref(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_2);
return x_71;
}
else
{
uint8_t x_72; 
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_66);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; size_t x_83; size_t x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; lean_object* x_89; 
x_73 = lean_ctor_get(x_66, 0);
x_74 = lean_ctor_get(x_66, 1);
x_75 = lean_array_get_size(x_74);
x_76 = l_Lean_hashLevelMVarId____x40_Lean_Level___hyg_490_(x_64);
x_77 = 32;
x_78 = lean_uint64_shift_right(x_76, x_77);
x_79 = lean_uint64_xor(x_76, x_78);
x_80 = 16;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = lean_uint64_to_usize(x_82);
x_84 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_85 = 1;
x_86 = lean_usize_sub(x_84, x_85);
x_87 = lean_usize_land(x_83, x_86);
x_88 = lean_array_uget(x_74, x_87);
x_89 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(x_64, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_100; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_90 = x_2;
} else {
 lean_dec_ref(x_2);
 x_90 = lean_box(0);
}
x_91 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1;
lean_inc(x_65);
x_92 = l_Lean_Name_num___override(x_91, x_65);
x_93 = l_Lean_Level_param___override(x_92);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_65, x_94);
lean_dec(x_65);
x_100 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(x_64, x_88);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_101 = lean_nat_add(x_73, x_94);
lean_dec(x_73);
lean_inc(x_93);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_64);
lean_ctor_set(x_102, 1, x_93);
lean_ctor_set(x_102, 2, x_88);
x_103 = lean_array_uset(x_74, x_87, x_102);
x_104 = lean_unsigned_to_nat(4u);
x_105 = lean_nat_mul(x_101, x_104);
x_106 = lean_unsigned_to_nat(3u);
x_107 = lean_nat_div(x_105, x_106);
lean_dec(x_105);
x_108 = lean_array_get_size(x_103);
x_109 = lean_nat_dec_le(x_107, x_108);
lean_dec(x_108);
lean_dec(x_107);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(x_103);
lean_ctor_set(x_66, 1, x_110);
lean_ctor_set(x_66, 0, x_101);
x_96 = x_66;
goto block_99;
}
else
{
lean_ctor_set(x_66, 1, x_103);
lean_ctor_set(x_66, 0, x_101);
x_96 = x_66;
goto block_99;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_box(0);
x_112 = lean_array_uset(x_74, x_87, x_111);
lean_inc(x_93);
x_113 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__5___redArg(x_64, x_93, x_88);
x_114 = lean_array_uset(x_112, x_87, x_113);
lean_ctor_set(x_66, 1, x_114);
x_96 = x_66;
goto block_99;
}
block_99:
{
lean_object* x_97; lean_object* x_98; 
if (lean_is_scalar(x_90)) {
 x_97 = lean_alloc_ctor(0, 4, 0);
} else {
 x_97 = x_90;
}
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_67);
lean_ctor_set(x_97, 3, x_63);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_88);
lean_free_object(x_66);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
x_115 = lean_ctor_get(x_89, 0);
lean_inc(x_115);
lean_dec(x_89);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_2);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint64_t x_120; uint64_t x_121; uint64_t x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; size_t x_127; size_t x_128; size_t x_129; size_t x_130; size_t x_131; lean_object* x_132; lean_object* x_133; 
x_117 = lean_ctor_get(x_66, 0);
x_118 = lean_ctor_get(x_66, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_66);
x_119 = lean_array_get_size(x_118);
x_120 = l_Lean_hashLevelMVarId____x40_Lean_Level___hyg_490_(x_64);
x_121 = 32;
x_122 = lean_uint64_shift_right(x_120, x_121);
x_123 = lean_uint64_xor(x_120, x_122);
x_124 = 16;
x_125 = lean_uint64_shift_right(x_123, x_124);
x_126 = lean_uint64_xor(x_123, x_125);
x_127 = lean_uint64_to_usize(x_126);
x_128 = lean_usize_of_nat(x_119);
lean_dec(x_119);
x_129 = 1;
x_130 = lean_usize_sub(x_128, x_129);
x_131 = lean_usize_land(x_127, x_130);
x_132 = lean_array_uget(x_118, x_131);
x_133 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(x_64, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_144; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_134 = x_2;
} else {
 lean_dec_ref(x_2);
 x_134 = lean_box(0);
}
x_135 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1;
lean_inc(x_65);
x_136 = l_Lean_Name_num___override(x_135, x_65);
x_137 = l_Lean_Level_param___override(x_136);
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_nat_add(x_65, x_138);
lean_dec(x_65);
x_144 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(x_64, x_132);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_145 = lean_nat_add(x_117, x_138);
lean_dec(x_117);
lean_inc(x_137);
x_146 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_146, 0, x_64);
lean_ctor_set(x_146, 1, x_137);
lean_ctor_set(x_146, 2, x_132);
x_147 = lean_array_uset(x_118, x_131, x_146);
x_148 = lean_unsigned_to_nat(4u);
x_149 = lean_nat_mul(x_145, x_148);
x_150 = lean_unsigned_to_nat(3u);
x_151 = lean_nat_div(x_149, x_150);
lean_dec(x_149);
x_152 = lean_array_get_size(x_147);
x_153 = lean_nat_dec_le(x_151, x_152);
lean_dec(x_152);
lean_dec(x_151);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(x_147);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_145);
lean_ctor_set(x_155, 1, x_154);
x_140 = x_155;
goto block_143;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_145);
lean_ctor_set(x_156, 1, x_147);
x_140 = x_156;
goto block_143;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_box(0);
x_158 = lean_array_uset(x_118, x_131, x_157);
lean_inc(x_137);
x_159 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__5___redArg(x_64, x_137, x_132);
x_160 = lean_array_uset(x_158, x_131, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_117);
lean_ctor_set(x_161, 1, x_160);
x_140 = x_161;
goto block_143;
}
block_143:
{
lean_object* x_141; lean_object* x_142; 
if (lean_is_scalar(x_134)) {
 x_141 = lean_alloc_ctor(0, 4, 0);
} else {
 x_141 = x_134;
}
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_67);
lean_ctor_set(x_141, 3, x_63);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_132);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec_ref(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
x_162 = lean_ctor_get(x_133, 0);
lean_inc(x_162);
lean_dec(x_133);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_2);
return x_163;
}
}
}
}
default: 
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_1);
lean_ctor_set(x_164, 1, x_2);
return x_164;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_Meta_SynthInstance_MkTableKey_normExpr_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_3);
lean_inc_ref(x_3);
x_4 = l_Lean_MetavarContext_getDecl(x_3, x_1);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SynthInstance_MkTableKey_normExpr_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_reverse___redArg(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_7, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_10);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_2 = x_11;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_13, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
x_1 = x_14;
x_2 = x_18;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasMVar(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_inc(x_5);
x_6 = l_Lean_MVarId_isAssignable___at___Lean_Meta_SynthInstance_MkTableKey_normExpr_spec__0(x_5, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_14 = x_6;
} else {
 lean_dec_ref(x_6);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_13, 3);
lean_inc_ref(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_hashMVarId____x40_Lean_Expr___hyg_1840_(x_5);
x_24 = 32;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = 16;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = 1;
x_33 = lean_usize_sub(x_31, x_32);
x_34 = lean_usize_land(x_30, x_33);
x_35 = lean_array_uget(x_21, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___redArg(x_5, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_47; 
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_37 = x_13;
} else {
 lean_dec_ref(x_13);
 x_37 = lean_box(0);
}
x_38 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1;
lean_inc(x_16);
x_39 = l_Lean_Name_num___override(x_38, x_16);
x_40 = l_Lean_Expr_fvar___override(x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_16, x_41);
lean_dec(x_16);
x_47 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(x_5, x_35);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_48 = lean_nat_add(x_20, x_41);
lean_dec(x_20);
lean_inc_ref(x_40);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_35);
x_50 = lean_array_uset(x_21, x_34, x_49);
x_51 = lean_unsigned_to_nat(4u);
x_52 = lean_nat_mul(x_48, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_div(x_52, x_53);
lean_dec(x_52);
x_55 = lean_array_get_size(x_50);
x_56 = lean_nat_dec_le(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(x_50);
lean_ctor_set(x_15, 1, x_57);
lean_ctor_set(x_15, 0, x_48);
x_43 = x_15;
goto block_46;
}
else
{
lean_ctor_set(x_15, 1, x_50);
lean_ctor_set(x_15, 0, x_48);
x_43 = x_15;
goto block_46;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_box(0);
x_59 = lean_array_uset(x_21, x_34, x_58);
lean_inc_ref(x_40);
x_60 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6___redArg(x_5, x_40, x_35);
x_61 = lean_array_uset(x_59, x_34, x_60);
lean_ctor_set(x_15, 1, x_61);
x_43 = x_15;
goto block_46;
}
block_46:
{
lean_object* x_44; lean_object* x_45; 
if (lean_is_scalar(x_37)) {
 x_44 = lean_alloc_ctor(0, 4, 0);
} else {
 x_44 = x_37;
}
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_17);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_18);
if (lean_is_scalar(x_14)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_14;
}
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_35);
lean_free_object(x_15);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_5);
x_62 = lean_ctor_get(x_36, 0);
lean_inc(x_62);
lean_dec(x_36);
if (lean_is_scalar(x_14)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_14;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_13);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; size_t x_74; size_t x_75; size_t x_76; size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; 
x_64 = lean_ctor_get(x_15, 0);
x_65 = lean_ctor_get(x_15, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_15);
x_66 = lean_array_get_size(x_65);
x_67 = l_Lean_hashMVarId____x40_Lean_Expr___hyg_1840_(x_5);
x_68 = 32;
x_69 = lean_uint64_shift_right(x_67, x_68);
x_70 = lean_uint64_xor(x_67, x_69);
x_71 = 16;
x_72 = lean_uint64_shift_right(x_70, x_71);
x_73 = lean_uint64_xor(x_70, x_72);
x_74 = lean_uint64_to_usize(x_73);
x_75 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_76 = 1;
x_77 = lean_usize_sub(x_75, x_76);
x_78 = lean_usize_land(x_74, x_77);
x_79 = lean_array_uget(x_65, x_78);
x_80 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___redArg(x_5, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_91; 
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_81 = x_13;
} else {
 lean_dec_ref(x_13);
 x_81 = lean_box(0);
}
x_82 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1;
lean_inc(x_16);
x_83 = l_Lean_Name_num___override(x_82, x_16);
x_84 = l_Lean_Expr_fvar___override(x_83);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_16, x_85);
lean_dec(x_16);
x_91 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(x_5, x_79);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_92 = lean_nat_add(x_64, x_85);
lean_dec(x_64);
lean_inc_ref(x_84);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_5);
lean_ctor_set(x_93, 1, x_84);
lean_ctor_set(x_93, 2, x_79);
x_94 = lean_array_uset(x_65, x_78, x_93);
x_95 = lean_unsigned_to_nat(4u);
x_96 = lean_nat_mul(x_92, x_95);
x_97 = lean_unsigned_to_nat(3u);
x_98 = lean_nat_div(x_96, x_97);
lean_dec(x_96);
x_99 = lean_array_get_size(x_94);
x_100 = lean_nat_dec_le(x_98, x_99);
lean_dec(x_99);
lean_dec(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(x_94);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_92);
lean_ctor_set(x_102, 1, x_101);
x_87 = x_102;
goto block_90;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_92);
lean_ctor_set(x_103, 1, x_94);
x_87 = x_103;
goto block_90;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_box(0);
x_105 = lean_array_uset(x_65, x_78, x_104);
lean_inc_ref(x_84);
x_106 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6___redArg(x_5, x_84, x_79);
x_107 = lean_array_uset(x_105, x_78, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_64);
lean_ctor_set(x_108, 1, x_107);
x_87 = x_108;
goto block_90;
}
block_90:
{
lean_object* x_88; lean_object* x_89; 
if (lean_is_scalar(x_81)) {
 x_88 = lean_alloc_ctor(0, 4, 0);
} else {
 x_88 = x_81;
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_17);
lean_ctor_set(x_88, 2, x_87);
lean_ctor_set(x_88, 3, x_18);
if (lean_is_scalar(x_14)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_14;
}
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_79);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_5);
x_109 = lean_ctor_get(x_80, 0);
lean_inc(x_109);
lean_dec(x_80);
if (lean_is_scalar(x_14)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_14;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_13);
return x_110;
}
}
}
}
case 3:
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
lean_inc(x_111);
x_112 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_111, x_2);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; size_t x_115; size_t x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_ptr_addr(x_111);
lean_dec(x_111);
x_116 = lean_ptr_addr(x_114);
x_117 = lean_usize_dec_eq(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec_ref(x_1);
x_118 = l_Lean_Expr_sort___override(x_114);
lean_ctor_set(x_112, 0, x_118);
return x_112;
}
else
{
lean_dec(x_114);
lean_ctor_set(x_112, 0, x_1);
return x_112;
}
}
else
{
lean_object* x_119; lean_object* x_120; size_t x_121; size_t x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_112, 0);
x_120 = lean_ctor_get(x_112, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_112);
x_121 = lean_ptr_addr(x_111);
lean_dec(x_111);
x_122 = lean_ptr_addr(x_119);
x_123 = lean_usize_dec_eq(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec_ref(x_1);
x_124 = l_Lean_Expr_sort___override(x_119);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_120);
return x_125;
}
else
{
lean_object* x_126; 
lean_dec(x_119);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_120);
return x_126;
}
}
}
case 4:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_127 = lean_ctor_get(x_1, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_1, 1);
lean_inc(x_128);
x_129 = lean_box(0);
lean_inc(x_128);
x_130 = l_List_mapM_loop___at___Lean_Meta_SynthInstance_MkTableKey_normExpr_spec__1(x_128, x_129, x_2);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = l_ptrEqList___redArg(x_128, x_132);
lean_dec(x_128);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec_ref(x_1);
x_134 = l_Lean_Expr_const___override(x_127, x_132);
lean_ctor_set(x_130, 0, x_134);
return x_130;
}
else
{
lean_dec(x_132);
lean_dec(x_127);
lean_ctor_set(x_130, 0, x_1);
return x_130;
}
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_130, 0);
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_130);
x_137 = l_ptrEqList___redArg(x_128, x_135);
lean_dec(x_128);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec_ref(x_1);
x_138 = l_Lean_Expr_const___override(x_127, x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
return x_139;
}
else
{
lean_object* x_140; 
lean_dec(x_135);
lean_dec(x_127);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_136);
return x_140;
}
}
}
case 5:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; size_t x_155; size_t x_156; uint8_t x_157; 
x_141 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_142);
lean_inc_ref(x_141);
x_143 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_141, x_2);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec_ref(x_143);
lean_inc_ref(x_142);
x_146 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_142, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_155 = lean_ptr_addr(x_141);
lean_dec_ref(x_141);
x_156 = lean_ptr_addr(x_144);
x_157 = lean_usize_dec_eq(x_155, x_156);
if (x_157 == 0)
{
lean_dec_ref(x_142);
x_150 = x_157;
goto block_154;
}
else
{
size_t x_158; size_t x_159; uint8_t x_160; 
x_158 = lean_ptr_addr(x_142);
lean_dec_ref(x_142);
x_159 = lean_ptr_addr(x_147);
x_160 = lean_usize_dec_eq(x_158, x_159);
x_150 = x_160;
goto block_154;
}
block_154:
{
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
lean_dec_ref(x_1);
x_151 = l_Lean_Expr_app___override(x_144, x_147);
if (lean_is_scalar(x_149)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_149;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_148);
return x_152;
}
else
{
lean_object* x_153; 
lean_dec(x_147);
lean_dec(x_144);
if (lean_is_scalar(x_149)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_149;
}
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_148);
return x_153;
}
}
}
case 6:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; size_t x_180; size_t x_181; uint8_t x_182; 
x_161 = lean_ctor_get(x_1, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_163);
x_164 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc_ref(x_162);
x_165 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_162, x_2);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec_ref(x_165);
lean_inc_ref(x_163);
x_168 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_163, x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_180 = lean_ptr_addr(x_162);
lean_dec_ref(x_162);
x_181 = lean_ptr_addr(x_166);
x_182 = lean_usize_dec_eq(x_180, x_181);
if (x_182 == 0)
{
lean_dec_ref(x_163);
x_172 = x_182;
goto block_179;
}
else
{
size_t x_183; size_t x_184; uint8_t x_185; 
x_183 = lean_ptr_addr(x_163);
lean_dec_ref(x_163);
x_184 = lean_ptr_addr(x_169);
x_185 = lean_usize_dec_eq(x_183, x_184);
x_172 = x_185;
goto block_179;
}
block_179:
{
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_1);
x_173 = l_Lean_Expr_lam___override(x_161, x_166, x_169, x_164);
if (lean_is_scalar(x_171)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_171;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_170);
return x_174;
}
else
{
uint8_t x_175; 
x_175 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_164, x_164);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
lean_dec_ref(x_1);
x_176 = l_Lean_Expr_lam___override(x_161, x_166, x_169, x_164);
if (lean_is_scalar(x_171)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_171;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_170);
return x_177;
}
else
{
lean_object* x_178; 
lean_dec(x_169);
lean_dec(x_166);
lean_dec(x_161);
if (lean_is_scalar(x_171)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_171;
}
lean_ctor_set(x_178, 0, x_1);
lean_ctor_set(x_178, 1, x_170);
return x_178;
}
}
}
}
case 7:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; size_t x_205; size_t x_206; uint8_t x_207; 
x_186 = lean_ctor_get(x_1, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_187);
x_188 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_188);
x_189 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc_ref(x_187);
x_190 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_187, x_2);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec_ref(x_190);
lean_inc_ref(x_188);
x_193 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_188, x_192);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
x_205 = lean_ptr_addr(x_187);
lean_dec_ref(x_187);
x_206 = lean_ptr_addr(x_191);
x_207 = lean_usize_dec_eq(x_205, x_206);
if (x_207 == 0)
{
lean_dec_ref(x_188);
x_197 = x_207;
goto block_204;
}
else
{
size_t x_208; size_t x_209; uint8_t x_210; 
x_208 = lean_ptr_addr(x_188);
lean_dec_ref(x_188);
x_209 = lean_ptr_addr(x_194);
x_210 = lean_usize_dec_eq(x_208, x_209);
x_197 = x_210;
goto block_204;
}
block_204:
{
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec_ref(x_1);
x_198 = l_Lean_Expr_forallE___override(x_186, x_191, x_194, x_189);
if (lean_is_scalar(x_196)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_196;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_195);
return x_199;
}
else
{
uint8_t x_200; 
x_200 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_189, x_189);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
lean_dec_ref(x_1);
x_201 = l_Lean_Expr_forallE___override(x_186, x_191, x_194, x_189);
if (lean_is_scalar(x_196)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_196;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_195);
return x_202;
}
else
{
lean_object* x_203; 
lean_dec(x_194);
lean_dec(x_191);
lean_dec(x_186);
if (lean_is_scalar(x_196)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_196;
}
lean_ctor_set(x_203, 0, x_1);
lean_ctor_set(x_203, 1, x_195);
return x_203;
}
}
}
}
case 8:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; size_t x_236; size_t x_237; uint8_t x_238; 
x_211 = lean_ctor_get(x_1, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_212);
x_213 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_213);
x_214 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_214);
x_215 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_inc_ref(x_212);
x_216 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_212, x_2);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec_ref(x_216);
lean_inc_ref(x_213);
x_219 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_213, x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec_ref(x_219);
lean_inc_ref(x_214);
x_222 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_214, x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
x_236 = lean_ptr_addr(x_212);
lean_dec_ref(x_212);
x_237 = lean_ptr_addr(x_217);
x_238 = lean_usize_dec_eq(x_236, x_237);
if (x_238 == 0)
{
lean_dec_ref(x_213);
x_226 = x_238;
goto block_235;
}
else
{
size_t x_239; size_t x_240; uint8_t x_241; 
x_239 = lean_ptr_addr(x_213);
lean_dec_ref(x_213);
x_240 = lean_ptr_addr(x_220);
x_241 = lean_usize_dec_eq(x_239, x_240);
x_226 = x_241;
goto block_235;
}
block_235:
{
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
lean_dec_ref(x_214);
lean_dec_ref(x_1);
x_227 = l_Lean_Expr_letE___override(x_211, x_217, x_220, x_223, x_215);
if (lean_is_scalar(x_225)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_225;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_224);
return x_228;
}
else
{
size_t x_229; size_t x_230; uint8_t x_231; 
x_229 = lean_ptr_addr(x_214);
lean_dec_ref(x_214);
x_230 = lean_ptr_addr(x_223);
x_231 = lean_usize_dec_eq(x_229, x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; 
lean_dec_ref(x_1);
x_232 = l_Lean_Expr_letE___override(x_211, x_217, x_220, x_223, x_215);
if (lean_is_scalar(x_225)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_225;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_224);
return x_233;
}
else
{
lean_object* x_234; 
lean_dec(x_223);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_211);
if (lean_is_scalar(x_225)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_225;
}
lean_ctor_set(x_234, 0, x_1);
lean_ctor_set(x_234, 1, x_224);
return x_234;
}
}
}
}
case 10:
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_242 = lean_ctor_get(x_1, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_243);
lean_inc_ref(x_243);
x_244 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_243, x_2);
x_245 = !lean_is_exclusive(x_244);
if (x_245 == 0)
{
lean_object* x_246; size_t x_247; size_t x_248; uint8_t x_249; 
x_246 = lean_ctor_get(x_244, 0);
x_247 = lean_ptr_addr(x_243);
lean_dec_ref(x_243);
x_248 = lean_ptr_addr(x_246);
x_249 = lean_usize_dec_eq(x_247, x_248);
if (x_249 == 0)
{
lean_object* x_250; 
lean_dec_ref(x_1);
x_250 = l_Lean_Expr_mdata___override(x_242, x_246);
lean_ctor_set(x_244, 0, x_250);
return x_244;
}
else
{
lean_dec(x_246);
lean_dec(x_242);
lean_ctor_set(x_244, 0, x_1);
return x_244;
}
}
else
{
lean_object* x_251; lean_object* x_252; size_t x_253; size_t x_254; uint8_t x_255; 
x_251 = lean_ctor_get(x_244, 0);
x_252 = lean_ctor_get(x_244, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_244);
x_253 = lean_ptr_addr(x_243);
lean_dec_ref(x_243);
x_254 = lean_ptr_addr(x_251);
x_255 = lean_usize_dec_eq(x_253, x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
lean_dec_ref(x_1);
x_256 = l_Lean_Expr_mdata___override(x_242, x_251);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_252);
return x_257;
}
else
{
lean_object* x_258; 
lean_dec(x_251);
lean_dec(x_242);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_1);
lean_ctor_set(x_258, 1, x_252);
return x_258;
}
}
}
case 11:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_259 = lean_ctor_get(x_1, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_1, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_261);
lean_inc_ref(x_261);
x_262 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_261, x_2);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; size_t x_265; size_t x_266; uint8_t x_267; 
x_264 = lean_ctor_get(x_262, 0);
x_265 = lean_ptr_addr(x_261);
lean_dec_ref(x_261);
x_266 = lean_ptr_addr(x_264);
x_267 = lean_usize_dec_eq(x_265, x_266);
if (x_267 == 0)
{
lean_object* x_268; 
lean_dec_ref(x_1);
x_268 = l_Lean_Expr_proj___override(x_259, x_260, x_264);
lean_ctor_set(x_262, 0, x_268);
return x_262;
}
else
{
lean_dec(x_264);
lean_dec(x_260);
lean_dec(x_259);
lean_ctor_set(x_262, 0, x_1);
return x_262;
}
}
else
{
lean_object* x_269; lean_object* x_270; size_t x_271; size_t x_272; uint8_t x_273; 
x_269 = lean_ctor_get(x_262, 0);
x_270 = lean_ctor_get(x_262, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_262);
x_271 = lean_ptr_addr(x_261);
lean_dec_ref(x_261);
x_272 = lean_ptr_addr(x_269);
x_273 = lean_usize_dec_eq(x_271, x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; 
lean_dec_ref(x_1);
x_274 = l_Lean_Expr_proj___override(x_259, x_260, x_269);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_270);
return x_275;
}
else
{
lean_object* x_276; 
lean_dec(x_269);
lean_dec(x_260);
lean_dec(x_259);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_1);
lean_ctor_set(x_276, 1, x_270);
return x_276;
}
}
}
default: 
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_1);
lean_ctor_set(x_277, 1, x_2);
return x_277;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__4;
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_5);
x_9 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_1, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 3);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_apply_1(x_3, x_14);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2), 5, 4);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_7);
lean_closure_set(x_9, 3, x_5);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SynthInstance_mkTableKey___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__2;
x_2 = l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__0;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__2;
x_3 = l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_checkSystem___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeclass", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkSystem___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 11);
if (lean_obj_tag(x_10) == 0)
{
x_4 = x_3;
goto block_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_st_ref_get(x_11, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_4 = x_15;
goto block_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec_ref(x_12);
x_17 = l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(x_16);
return x_17;
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Meta_SynthInstance_checkSystem___redArg___closed__0;
x_7 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_5_;
x_8 = l_Lean_Core_checkMaxHeartbeatsCore___redArg(x_6, x_7, x_5, x_2, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkSystem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_checkSystem___redArg(x_1, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkSystem___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_checkSystem___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkSystem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_checkSystem(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___closed__0;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___closed__1;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_SynthInstance_getInstances_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_9, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_9, 0);
lean_dec(x_19);
x_20 = lean_array_fget(x_11, x_12);
lean_inc_ref(x_4);
x_21 = l_Lean_Meta_getFVarLocalDecl___redArg(x_20, x_4, x_5, x_6, x_7);
lean_dec_ref(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_9, 1, x_33);
x_34 = l_Lean_LocalDecl_binderInfo(x_22);
lean_dec(x_22);
x_35 = 3;
x_36 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_34, x_35);
if (x_36 == 0)
{
x_25 = x_2;
goto block_31;
}
else
{
lean_object* x_37; 
lean_inc(x_3);
x_37 = lean_array_push(x_10, x_3);
lean_ctor_set(x_2, 1, x_37);
x_25 = x_2;
goto block_31;
}
block_31:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
lean_dec(x_3);
x_28 = lean_nat_dec_lt(x_27, x_1);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec_ref(x_4);
if (lean_is_scalar(x_24)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_24;
}
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
else
{
lean_dec(x_24);
x_2 = x_25;
x_3 = x_27;
x_7 = x_23;
goto _start;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_9);
x_42 = lean_array_fget(x_11, x_12);
lean_inc_ref(x_4);
x_43 = l_Lean_Meta_getFVarLocalDecl___redArg(x_42, x_4, x_5, x_6, x_7);
lean_dec_ref(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_12, x_54);
lean_dec(x_12);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_11);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_13);
x_57 = l_Lean_LocalDecl_binderInfo(x_44);
lean_dec(x_44);
x_58 = 3;
x_59 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_57, x_58);
if (x_59 == 0)
{
lean_ctor_set(x_2, 0, x_56);
x_47 = x_2;
goto block_53;
}
else
{
lean_object* x_60; 
lean_inc(x_3);
x_60 = lean_array_push(x_10, x_3);
lean_ctor_set(x_2, 1, x_60);
lean_ctor_set(x_2, 0, x_56);
x_47 = x_2;
goto block_53;
}
block_53:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_3, x_48);
lean_dec(x_3);
x_50 = lean_nat_dec_lt(x_49, x_1);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_49);
lean_dec_ref(x_4);
if (lean_is_scalar(x_46)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_46;
}
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
else
{
lean_dec(x_46);
x_2 = x_47;
x_3 = x_49;
x_7 = x_45;
goto _start;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec(x_3);
x_61 = lean_ctor_get(x_43, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_43, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_63 = x_43;
} else {
 lean_dec_ref(x_43);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_2);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc(x_69);
x_70 = lean_nat_dec_lt(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_4);
lean_dec(x_3);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_66);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_7);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
 x_73 = lean_box(0);
}
x_74 = lean_array_fget(x_67, x_68);
lean_inc_ref(x_4);
x_75 = l_Lean_Meta_getFVarLocalDecl___redArg(x_74, x_4, x_5, x_6, x_7);
lean_dec_ref(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_68, x_86);
lean_dec(x_68);
if (lean_is_scalar(x_73)) {
 x_88 = lean_alloc_ctor(0, 3, 0);
} else {
 x_88 = x_73;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_69);
x_89 = l_Lean_LocalDecl_binderInfo(x_76);
lean_dec(x_76);
x_90 = 3;
x_91 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_89, x_90);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_66);
x_79 = x_92;
goto block_85;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_inc(x_3);
x_93 = lean_array_push(x_66, x_3);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_93);
x_79 = x_94;
goto block_85;
}
block_85:
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_3, x_80);
lean_dec(x_3);
x_82 = lean_nat_dec_lt(x_81, x_1);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec(x_81);
lean_dec_ref(x_4);
if (lean_is_scalar(x_78)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_78;
}
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
else
{
lean_dec(x_78);
x_2 = x_79;
x_3 = x_81;
x_7 = x_77;
goto _start;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_73);
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_75, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_75, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_97 = x_75;
} else {
 lean_dec_ref(x_75);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_SynthInstance_getInstances_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_SynthInstance_getInstances_spec__0___redArg(x_5, x_7, x_8, x_11, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SynthInstance_getInstances_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_11;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_2);
x_1 = x_17;
x_2 = x_21;
x_7 = x_20;
goto _start;
}
}
}
}
static lean_object* _init_l_panic___at___Lean_Meta_SynthInstance_getInstances_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_SynthInstance_getInstances_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___Lean_Meta_SynthInstance_getInstances_spec__2___closed__0;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_SynthInstance_getInstances_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_array_fget(x_1, x_2);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = lean_array_fget(x_1, x_8);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
if (x_11 == 0)
{
lean_dec(x_8);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fswap(x_1, x_2, x_8);
lean_dec(x_2);
x_1 = x_12;
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_SynthInstance_getInstances_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_SynthInstance_getInstances_spec__3_spec__3___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at___Lean_Meta_SynthInstance_getInstances_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
lean_inc(x_2);
x_10 = l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_SynthInstance_getInstances_spec__3_spec__3___redArg(x_1, x_2);
x_11 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_11;
x_3 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.SynthInstance", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.SynthInstance.getInstances", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("global instance is not a constant", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__2;
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_unsigned_to_nat(224u);
x_4 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__1;
x_5 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; uint8_t x_21; 
x_21 = lean_usize_dec_eq(x_3, x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_array_uget(x_2, x_3);
x_23 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_23);
if (lean_obj_tag(x_23) == 4)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 4);
lean_inc_ref(x_24);
lean_dec_ref(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc_ref(x_1);
x_27 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_containsOnBranch_spec__0_spec__0___redArg(x_1, x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_36; 
x_28 = lean_box(0);
lean_inc(x_26);
x_29 = l_List_mapM_loop___at___Lean_Meta_SynthInstance_getInstances_spec__1(x_26, x_28, x_6, x_7, x_8, x_9, x_10);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_36 = l_ptrEqList___redArg(x_26, x_30);
lean_dec(x_26);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec_ref(x_23);
x_37 = l_Lean_Expr_const___override(x_25, x_30);
x_33 = x_37;
goto block_35;
}
else
{
lean_dec(x_30);
lean_dec(x_25);
x_33 = x_23;
goto block_35;
}
block_35:
{
lean_object* x_34; 
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
x_17 = x_34;
x_18 = x_31;
goto block_20;
}
}
else
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
x_11 = x_5;
x_12 = x_10;
goto block_16;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_23);
lean_dec_ref(x_22);
x_38 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__3;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_39 = l_panic___at___Lean_Meta_SynthInstance_getInstances_spec__2(x_38, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_11 = x_5;
x_12 = x_41;
goto block_16;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec_ref(x_39);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_17 = x_43;
x_18 = x_42;
goto block_20;
}
}
else
{
uint8_t x_44; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_10);
return x_48;
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_11;
x_10 = x_12;
goto _start;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_array_push(x_5, x_17);
x_11 = x_19;
x_12 = x_18;
goto block_16;
}
}
}
static lean_object* _init_l_Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5___closed__0;
x_11 = lean_nat_dec_lt(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_le(x_4, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_3);
x_17 = lean_usize_of_nat(x_4);
x_18 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5(x_1, x_2, x_16, x_17, x_10, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_SynthInstance_getInstances_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_5, x_4);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_uget(x_3, x_5);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_name_eq(x_22, x_1);
lean_dec(x_22);
if (x_24 == 0)
{
lean_free_object(x_20);
lean_dec_ref(x_23);
x_12 = x_6;
x_13 = x_11;
goto block_17;
}
else
{
lean_object* x_25; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_23);
x_25 = lean_infer_type(x_23, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_29 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_26, x_2, x_28, x_28, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
lean_ctor_set(x_20, 1, x_30);
lean_ctor_set(x_20, 0, x_23);
x_32 = lean_array_push(x_6, x_20);
x_12 = x_32;
x_13 = x_31;
goto block_17;
}
else
{
uint8_t x_33; 
lean_free_object(x_20);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_20);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_25);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_name_eq(x_41, x_1);
lean_dec(x_41);
if (x_43 == 0)
{
lean_dec_ref(x_42);
x_12 = x_6;
x_13 = x_11;
goto block_17;
}
else
{
lean_object* x_44; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_42);
x_44 = lean_infer_type(x_42, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_48 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_45, x_2, x_47, x_47, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_array_push(x_6, x_51);
x_12 = x_52;
x_13 = x_50;
goto block_17;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_42);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_55 = x_48;
} else {
 lean_dec_ref(x_48);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_42);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_59 = x_44;
} else {
 lean_dec_ref(x_44);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
x_6 = x_12;
x_11 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getInstances_spec__8(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___redArg(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Meta_SynthInstance_getInstances___lam__0___closed__0;
x_12 = lean_nat_dec_lt(x_10, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_9);
x_14 = l_Array_toSubarray___redArg(x_1, x_10, x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
x_16 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_SynthInstance_getInstances_spec__0___redArg(x_9, x_15, x_10, x_3, x_5, x_6, x_7);
lean_dec(x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_28 = l_Lean_Meta_SynthInstance_getInstances___lam__0___closed__0;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type class instance expected", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instances", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__3;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_10 = l_Lean_Meta_isClass_x3f(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__1;
x_14 = l_Lean_indentExpr(x_4);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_17, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec_ref(x_10);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = l_Lean_Meta_getGlobalInstancesIndex___redArg(x_8, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_24 = l_Lean_Meta_DiscrTree_getUnify___redArg(x_22, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Lean_Meta_getErasedInstances___redArg(x_8, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_25);
x_32 = l_Array_insertionSort_traverse___at___Lean_Meta_SynthInstance_getInstances_spec__3(x_25, x_30, x_31);
x_33 = lean_array_get_size(x_32);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_34 = l_Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5(x_28, x_32, x_30, x_33, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_33);
lean_dec_ref(x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_array_size(x_1);
x_38 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_39 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_SynthInstance_getInstances_spec__7(x_20, x_2, x_1, x_37, x_38, x_35, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_20);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__4;
x_43 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_7, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
uint8_t x_46; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_43, 0);
lean_dec(x_47);
lean_ctor_set(x_43, 0, x_40);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec_ref(x_43);
x_51 = lean_array_size(x_40);
lean_inc(x_40);
x_52 = l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getInstances_spec__8(x_51, x_38, x_40);
x_53 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__7;
x_54 = l_Lean_MessageData_arrayExpr_toMessageData(x_52, x_30, x_53);
lean_dec_ref(x_52);
x_55 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_54, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_40);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_40);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_39;
}
}
else
{
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_34;
}
}
else
{
uint8_t x_60; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_24);
if (x_60 == 0)
{
return x_24;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_24, 0);
x_62 = lean_ctor_get(x_24, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_24);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_10);
if (x_64 == 0)
{
return x_10;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_10, 0);
x_66 = lean_ctor_get(x_10, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_10);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_7 = l_Lean_Meta_getLocalInstances___redArg(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getInstances___lam__0___boxed), 7, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getInstances___lam__1___boxed), 9, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
x_12 = 0;
x_13 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_1, x_11, x_12, x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_SynthInstance_getInstances_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_SynthInstance_getInstances_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_SynthInstance_getInstances_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
x_17 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_SynthInstance_getInstances_spec__0(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SynthInstance_getInstances_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___Lean_Meta_SynthInstance_getInstances_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_SynthInstance_getInstances_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_SynthInstance_getInstances_spec__7(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getInstances_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getInstances_spec__8(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_getInstances___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_getInstances___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkGeneratorNode_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_9, x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_4);
lean_inc(x_12);
x_14 = l_Lean_Meta_SynthInstance_getInstances(x_12, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Array_isEmpty___redArg(x_16);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_free_object(x_14);
x_19 = lean_st_ref_get(x_4, x_17);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
lean_dec(x_21);
x_23 = lean_array_get_size(x_16);
x_24 = l_Lean_Expr_hasMVar(x_12);
lean_dec(x_12);
x_25 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_1);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_16);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_19, 0, x_26);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_29);
lean_dec(x_27);
x_30 = lean_array_get_size(x_16);
x_31 = l_Lean_Expr_hasMVar(x_12);
lean_dec(x_12);
x_32 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_1);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_16);
lean_ctor_set(x_32, 4, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*5, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = lean_box(0);
lean_ctor_set(x_14, 0, x_35);
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
x_38 = l_Array_isEmpty___redArg(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_st_ref_get(x_4, x_37);
lean_dec(x_4);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_43);
lean_dec(x_40);
x_44 = lean_array_get_size(x_36);
x_45 = l_Lean_Expr_hasMVar(x_12);
lean_dec(x_12);
x_46 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_1);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_36);
lean_ctor_set(x_46, 4, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*5, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
if (lean_is_scalar(x_42)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_42;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_36);
lean_dec(x_12);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_37);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_14);
if (x_51 == 0)
{
return x_14;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_14, 0);
x_53 = lean_ctor_get(x_14, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_14);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_55 = !lean_is_exclusive(x_8);
if (x_55 == 0)
{
return x_8;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_8, 0);
x_57 = lean_ctor_get(x_8, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_8);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 12);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg(x_1, x_6, x_8);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__0;
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_5);
x_8 = lean_st_ref_take(x_1, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 4);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__2;
lean_ctor_set(x_10, 0, x_16);
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
uint64_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get_uint64(x_10, sizeof(void*)*1);
lean_dec(x_10);
x_23 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__2;
x_24 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint64(x_24, sizeof(void*)*1, x_22);
lean_ctor_set(x_9, 4, x_24);
x_25 = lean_st_ref_set(x_1, x_9, x_11);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 3);
x_33 = lean_ctor_get(x_9, 5);
x_34 = lean_ctor_get(x_9, 6);
x_35 = lean_ctor_get(x_9, 7);
x_36 = lean_ctor_get(x_9, 8);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_37 = lean_ctor_get_uint64(x_10, sizeof(void*)*1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_38 = x_10;
} else {
 lean_dec_ref(x_10);
 x_38 = lean_box(0);
}
x_39 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__2;
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 1, 8);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint64(x_40, sizeof(void*)*1, x_37);
x_41 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 3, x_32);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_41, 6, x_34);
lean_ctor_set(x_41, 7, x_35);
lean_ctor_set(x_41, 8, x_36);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = lean_st_ref_get(x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_replaceRef(x_3, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_17);
x_18 = l_Lean_PersistentArray_toArray___redArg(x_16);
lean_dec_ref(x_16);
x_19 = lean_array_size(x_18);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(x_19, x_20, x_18);
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_22, 2, x_21);
x_23 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_22, x_5, x_6, x_7, x_8, x_15);
lean_dec_ref(x_7);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_st_ref_take(x_8, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 4);
lean_inc_ref(x_28);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_ctor_get(x_26, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_27, 4);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_28, 0);
lean_dec(x_35);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 0, x_3);
x_36 = l_Lean_PersistentArray_push___redArg(x_1, x_26);
lean_ctor_set(x_28, 0, x_36);
x_37 = lean_st_ref_set(x_8, x_27, x_30);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint64_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
lean_dec(x_28);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 0, x_3);
x_45 = l_Lean_PersistentArray_push___redArg(x_1, x_26);
x_46 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set_uint64(x_46, sizeof(void*)*1, x_44);
lean_ctor_set(x_27, 4, x_46);
x_47 = lean_st_ref_set(x_8, x_27, x_30);
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_52 = lean_ctor_get(x_27, 0);
x_53 = lean_ctor_get(x_27, 1);
x_54 = lean_ctor_get(x_27, 2);
x_55 = lean_ctor_get(x_27, 3);
x_56 = lean_ctor_get(x_27, 5);
x_57 = lean_ctor_get(x_27, 6);
x_58 = lean_ctor_get(x_27, 7);
x_59 = lean_ctor_get(x_27, 8);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_27);
x_60 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_61 = x_28;
} else {
 lean_dec_ref(x_28);
 x_61 = lean_box(0);
}
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 0, x_3);
x_62 = l_Lean_PersistentArray_push___redArg(x_1, x_26);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 1, 8);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint64(x_63, sizeof(void*)*1, x_60);
x_64 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_53);
lean_ctor_set(x_64, 2, x_54);
lean_ctor_set(x_64, 3, x_55);
lean_ctor_set(x_64, 4, x_63);
lean_ctor_set(x_64, 5, x_56);
lean_ctor_set(x_64, 6, x_57);
lean_ctor_set(x_64, 7, x_58);
lean_ctor_set(x_64, 8, x_59);
x_65 = lean_st_ref_set(x_8, x_64, x_30);
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
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint64_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_70 = lean_ctor_get(x_26, 1);
lean_inc(x_70);
lean_dec(x_26);
x_71 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_27, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_27, 2);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_27, 3);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_27, 5);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_27, 6);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_27, 7);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_27, 8);
lean_inc_ref(x_78);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 lean_ctor_release(x_27, 6);
 lean_ctor_release(x_27, 7);
 lean_ctor_release(x_27, 8);
 x_79 = x_27;
} else {
 lean_dec_ref(x_27);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_81 = x_28;
} else {
 lean_dec_ref(x_28);
 x_81 = lean_box(0);
}
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_3);
lean_ctor_set(x_82, 1, x_24);
x_83 = l_Lean_PersistentArray_push___redArg(x_1, x_82);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 1, 8);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set_uint64(x_84, sizeof(void*)*1, x_80);
if (lean_is_scalar(x_79)) {
 x_85 = lean_alloc_ctor(0, 9, 0);
} else {
 x_85 = x_79;
}
lean_ctor_set(x_85, 0, x_71);
lean_ctor_set(x_85, 1, x_72);
lean_ctor_set(x_85, 2, x_73);
lean_ctor_set(x_85, 3, x_74);
lean_ctor_set(x_85, 4, x_84);
lean_ctor_set(x_85, 5, x_75);
lean_ctor_set(x_85, 6, x_76);
lean_ctor_set(x_85, 7, x_77);
lean_ctor_set(x_85, 8, x_78);
x_86 = lean_st_ref_set(x_8, x_85, x_70);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint64_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_91 = lean_ctor_get(x_7, 0);
x_92 = lean_ctor_get(x_7, 1);
x_93 = lean_ctor_get(x_7, 2);
x_94 = lean_ctor_get(x_7, 3);
x_95 = lean_ctor_get(x_7, 4);
x_96 = lean_ctor_get(x_7, 5);
x_97 = lean_ctor_get(x_7, 6);
x_98 = lean_ctor_get(x_7, 7);
x_99 = lean_ctor_get(x_7, 8);
x_100 = lean_ctor_get(x_7, 9);
x_101 = lean_ctor_get(x_7, 10);
x_102 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_103 = lean_ctor_get(x_7, 11);
x_104 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_105 = lean_ctor_get(x_7, 12);
lean_inc(x_105);
lean_inc(x_103);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_7);
x_106 = lean_st_ref_get(x_8, x_9);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 4);
lean_inc_ref(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec_ref(x_106);
x_110 = lean_ctor_get(x_108, 0);
lean_inc_ref(x_110);
lean_dec_ref(x_108);
x_111 = l_Lean_replaceRef(x_3, x_96);
lean_dec(x_96);
x_112 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_112, 0, x_91);
lean_ctor_set(x_112, 1, x_92);
lean_ctor_set(x_112, 2, x_93);
lean_ctor_set(x_112, 3, x_94);
lean_ctor_set(x_112, 4, x_95);
lean_ctor_set(x_112, 5, x_111);
lean_ctor_set(x_112, 6, x_97);
lean_ctor_set(x_112, 7, x_98);
lean_ctor_set(x_112, 8, x_99);
lean_ctor_set(x_112, 9, x_100);
lean_ctor_set(x_112, 10, x_101);
lean_ctor_set(x_112, 11, x_103);
lean_ctor_set(x_112, 12, x_105);
lean_ctor_set_uint8(x_112, sizeof(void*)*13, x_102);
lean_ctor_set_uint8(x_112, sizeof(void*)*13 + 1, x_104);
x_113 = l_Lean_PersistentArray_toArray___redArg(x_110);
lean_dec_ref(x_110);
x_114 = lean_array_size(x_113);
x_115 = 0;
x_116 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18_spec__19_spec__19(x_114, x_115, x_113);
x_117 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_117, 0, x_2);
lean_ctor_set(x_117, 1, x_4);
lean_ctor_set(x_117, 2, x_116);
x_118 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_117, x_5, x_6, x_112, x_8, x_109);
lean_dec_ref(x_112);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec_ref(x_118);
x_121 = lean_st_ref_take(x_8, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_122, 4);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_125 = x_121;
} else {
 lean_dec_ref(x_121);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_122, 0);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 2);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_122, 3);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_122, 5);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_122, 6);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_122, 7);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_122, 8);
lean_inc_ref(x_133);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 lean_ctor_release(x_122, 4);
 lean_ctor_release(x_122, 5);
 lean_ctor_release(x_122, 6);
 lean_ctor_release(x_122, 7);
 lean_ctor_release(x_122, 8);
 x_134 = x_122;
} else {
 lean_dec_ref(x_122);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get_uint64(x_123, sizeof(void*)*1);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_136 = x_123;
} else {
 lean_dec_ref(x_123);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_125;
}
lean_ctor_set(x_137, 0, x_3);
lean_ctor_set(x_137, 1, x_119);
x_138 = l_Lean_PersistentArray_push___redArg(x_1, x_137);
if (lean_is_scalar(x_136)) {
 x_139 = lean_alloc_ctor(0, 1, 8);
} else {
 x_139 = x_136;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set_uint64(x_139, sizeof(void*)*1, x_135);
if (lean_is_scalar(x_134)) {
 x_140 = lean_alloc_ctor(0, 9, 0);
} else {
 x_140 = x_134;
}
lean_ctor_set(x_140, 0, x_126);
lean_ctor_set(x_140, 1, x_127);
lean_ctor_set(x_140, 2, x_128);
lean_ctor_set(x_140, 3, x_129);
lean_ctor_set(x_140, 4, x_139);
lean_ctor_set(x_140, 5, x_130);
lean_ctor_set(x_140, 6, x_131);
lean_ctor_set(x_140, 7, x_132);
lean_ctor_set(x_140, 8, x_133);
x_141 = lean_st_ref_set(x_8, x_140, x_124);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_box(0);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
return x_145;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__3___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg(x_2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__3___redArg(x_1, x_5, x_2, x_3, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg(x_4, x_15);
return x_16;
}
}
static double _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_threshold;
return x_1;
}
}
static double _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__5() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static double _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__6() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_useHeartbeats;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; double x_17; double x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_30; lean_object* x_31; lean_object* x_32; double x_33; lean_object* x_34; uint8_t x_35; double x_36; lean_object* x_47; lean_object* x_48; double x_49; double x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; double x_66; double x_67; uint8_t x_68; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; double x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; double x_88; uint8_t x_89; uint8_t x_90; lean_object* x_129; lean_object* x_130; lean_object* x_131; double x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; double x_136; double x_137; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; double x_167; lean_object* x_168; double x_169; uint8_t x_170; uint8_t x_171; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; double x_215; double x_216; uint8_t x_217; double x_218; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; uint8_t x_273; 
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 5);
lean_inc(x_14);
lean_inc(x_1);
x_79 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg(x_1, x_10, x_12);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_273 = lean_unbox(x_80);
if (x_273 == 0)
{
lean_object* x_274; uint8_t x_275; 
x_274 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__3;
x_275 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_13, x_274);
if (x_275 == 0)
{
lean_object* x_276; 
lean_dec(x_80);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_276 = lean_apply_7(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_81);
return x_276;
}
else
{
goto block_272;
}
}
else
{
goto block_272;
}
block_29:
{
if (x_19 == 0)
{
double x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__0;
x_23 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set_float(x_23, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_23, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 16, x_4);
x_24 = lean_box(0);
x_25 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___lam__0(x_16, x_14, x_20, x_15, x_23, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_18);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_4);
x_27 = lean_box(0);
x_28 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___lam__0(x_16, x_14, x_20, x_15, x_26, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_15);
return x_28;
}
}
block_46:
{
lean_object* x_37; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_37 = lean_apply_8(x_2, x_34, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_37) == 0)
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_15 = x_30;
x_16 = x_31;
x_17 = x_33;
x_18 = x_36;
x_19 = x_35;
x_20 = x_38;
x_21 = x_39;
goto block_29;
}
else
{
uint8_t x_40; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_ctor_set_tag(x_37, 1);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec_ref(x_37);
x_45 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__2;
x_15 = x_30;
x_16 = x_31;
x_17 = x_33;
x_18 = x_36;
x_19 = x_35;
x_20 = x_45;
x_21 = x_44;
goto block_29;
}
}
block_61:
{
if (x_51 == 0)
{
double x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__0;
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_5);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_4);
x_56 = lean_box(0);
x_57 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___lam__0(x_48, x_14, x_52, x_47, x_55, x_56, x_6, x_7, x_8, x_9, x_10, x_11, x_53);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_47);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_5);
lean_ctor_set_float(x_58, sizeof(void*)*2, x_49);
lean_ctor_set_float(x_58, sizeof(void*)*2 + 8, x_50);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 16, x_4);
x_59 = lean_box(0);
x_60 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___lam__0(x_48, x_14, x_52, x_47, x_58, x_59, x_6, x_7, x_8, x_9, x_10, x_11, x_53);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_47);
return x_60;
}
}
block_78:
{
lean_object* x_69; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_69 = lean_apply_8(x_2, x_65, x_6, x_7, x_8, x_9, x_10, x_11, x_64);
if (lean_obj_tag(x_69) == 0)
{
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_47 = x_62;
x_48 = x_63;
x_49 = x_66;
x_50 = x_67;
x_51 = x_68;
x_52 = x_70;
x_53 = x_71;
goto block_61;
}
else
{
uint8_t x_72; 
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
lean_ctor_set_tag(x_69, 1);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
lean_dec_ref(x_69);
x_77 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__2;
x_47 = x_62;
x_48 = x_63;
x_49 = x_66;
x_50 = x_67;
x_51 = x_68;
x_52 = x_77;
x_53 = x_76;
goto block_61;
}
}
block_128:
{
uint8_t x_91; 
x_91 = lean_unbox(x_80);
lean_dec(x_80);
if (x_91 == 0)
{
if (x_90 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec(x_14);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_92 = lean_st_ref_take(x_11, x_85);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 4);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec_ref(x_92);
x_96 = !lean_is_exclusive(x_93);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_93, 4);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_94);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_94, 0);
x_100 = l_Lean_PersistentArray_append___redArg(x_87, x_99);
lean_dec_ref(x_99);
lean_ctor_set(x_94, 0, x_100);
x_101 = lean_st_ref_set(x_11, x_93, x_95);
lean_dec(x_11);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg(x_86, x_102);
lean_dec_ref(x_86);
return x_103;
}
else
{
uint64_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get_uint64(x_94, sizeof(void*)*1);
x_105 = lean_ctor_get(x_94, 0);
lean_inc(x_105);
lean_dec(x_94);
x_106 = l_Lean_PersistentArray_append___redArg(x_87, x_105);
lean_dec_ref(x_105);
x_107 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set_uint64(x_107, sizeof(void*)*1, x_104);
lean_ctor_set(x_93, 4, x_107);
x_108 = lean_st_ref_set(x_11, x_93, x_95);
lean_dec(x_11);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg(x_86, x_109);
lean_dec_ref(x_86);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint64_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_111 = lean_ctor_get(x_93, 0);
x_112 = lean_ctor_get(x_93, 1);
x_113 = lean_ctor_get(x_93, 2);
x_114 = lean_ctor_get(x_93, 3);
x_115 = lean_ctor_get(x_93, 5);
x_116 = lean_ctor_get(x_93, 6);
x_117 = lean_ctor_get(x_93, 7);
x_118 = lean_ctor_get(x_93, 8);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_93);
x_119 = lean_ctor_get_uint64(x_94, sizeof(void*)*1);
x_120 = lean_ctor_get(x_94, 0);
lean_inc_ref(x_120);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_121 = x_94;
} else {
 lean_dec_ref(x_94);
 x_121 = lean_box(0);
}
x_122 = l_Lean_PersistentArray_append___redArg(x_87, x_120);
lean_dec_ref(x_120);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 1, 8);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set_uint64(x_123, sizeof(void*)*1, x_119);
x_124 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_124, 0, x_111);
lean_ctor_set(x_124, 1, x_112);
lean_ctor_set(x_124, 2, x_113);
lean_ctor_set(x_124, 3, x_114);
lean_ctor_set(x_124, 4, x_123);
lean_ctor_set(x_124, 5, x_115);
lean_ctor_set(x_124, 6, x_116);
lean_ctor_set(x_124, 7, x_117);
lean_ctor_set(x_124, 8, x_118);
x_125 = lean_st_ref_set(x_11, x_124, x_95);
lean_dec(x_11);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg(x_86, x_126);
lean_dec_ref(x_86);
return x_127;
}
}
else
{
lean_dec_ref(x_87);
x_30 = x_82;
x_31 = x_83;
x_32 = x_85;
x_33 = x_84;
x_34 = x_86;
x_35 = x_89;
x_36 = x_88;
goto block_46;
}
}
else
{
lean_dec_ref(x_87);
x_30 = x_82;
x_31 = x_83;
x_32 = x_85;
x_33 = x_84;
x_34 = x_86;
x_35 = x_89;
x_36 = x_88;
goto block_46;
}
}
block_140:
{
double x_138; uint8_t x_139; 
x_138 = lean_float_sub(x_132, x_136);
x_139 = lean_float_decLt(x_137, x_138);
x_82 = x_129;
x_83 = x_130;
x_84 = x_132;
x_85 = x_131;
x_86 = x_133;
x_87 = x_134;
x_88 = x_136;
x_89 = x_135;
x_90 = x_139;
goto block_128;
}
block_162:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; double x_150; double x_151; lean_object* x_152; uint8_t x_153; 
x_147 = lean_io_get_num_heartbeats(x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec_ref(x_147);
x_150 = lean_float_of_nat(x_142);
x_151 = lean_float_of_nat(x_148);
x_152 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__3;
x_153 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_13, x_152);
if (x_153 == 0)
{
lean_dec(x_13);
lean_inc_ref(x_145);
x_82 = x_145;
x_83 = x_141;
x_84 = x_151;
x_85 = x_149;
x_86 = x_145;
x_87 = x_143;
x_88 = x_150;
x_89 = x_153;
x_90 = x_153;
goto block_128;
}
else
{
if (x_144 == 0)
{
lean_object* x_154; lean_object* x_155; double x_156; double x_157; double x_158; 
x_154 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__4;
x_155 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_13, x_154);
lean_dec(x_13);
x_156 = lean_float_of_nat(x_155);
x_157 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__5;
x_158 = lean_float_div(x_156, x_157);
lean_inc_ref(x_145);
x_129 = x_145;
x_130 = x_141;
x_131 = x_149;
x_132 = x_151;
x_133 = x_145;
x_134 = x_143;
x_135 = x_153;
x_136 = x_150;
x_137 = x_158;
goto block_140;
}
else
{
lean_object* x_159; lean_object* x_160; double x_161; 
x_159 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__4;
x_160 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_13, x_159);
lean_dec(x_13);
x_161 = lean_float_of_nat(x_160);
lean_inc_ref(x_145);
x_129 = x_145;
x_130 = x_141;
x_131 = x_149;
x_132 = x_151;
x_133 = x_145;
x_134 = x_143;
x_135 = x_153;
x_136 = x_150;
x_137 = x_161;
goto block_140;
}
}
}
block_209:
{
uint8_t x_172; 
x_172 = lean_unbox(x_80);
lean_dec(x_80);
if (x_172 == 0)
{
if (x_171 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
lean_dec_ref(x_164);
lean_dec_ref(x_163);
lean_dec(x_14);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_st_ref_take(x_11, x_165);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_174, 4);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec_ref(x_173);
x_177 = !lean_is_exclusive(x_174);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_174, 4);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_175);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_175, 0);
x_181 = l_Lean_PersistentArray_append___redArg(x_168, x_180);
lean_dec_ref(x_180);
lean_ctor_set(x_175, 0, x_181);
x_182 = lean_st_ref_set(x_11, x_174, x_176);
lean_dec(x_11);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec_ref(x_182);
x_184 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg(x_166, x_183);
lean_dec_ref(x_166);
return x_184;
}
else
{
uint64_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_185 = lean_ctor_get_uint64(x_175, sizeof(void*)*1);
x_186 = lean_ctor_get(x_175, 0);
lean_inc(x_186);
lean_dec(x_175);
x_187 = l_Lean_PersistentArray_append___redArg(x_168, x_186);
lean_dec_ref(x_186);
x_188 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set_uint64(x_188, sizeof(void*)*1, x_185);
lean_ctor_set(x_174, 4, x_188);
x_189 = lean_st_ref_set(x_11, x_174, x_176);
lean_dec(x_11);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec_ref(x_189);
x_191 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg(x_166, x_190);
lean_dec_ref(x_166);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint64_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_192 = lean_ctor_get(x_174, 0);
x_193 = lean_ctor_get(x_174, 1);
x_194 = lean_ctor_get(x_174, 2);
x_195 = lean_ctor_get(x_174, 3);
x_196 = lean_ctor_get(x_174, 5);
x_197 = lean_ctor_get(x_174, 6);
x_198 = lean_ctor_get(x_174, 7);
x_199 = lean_ctor_get(x_174, 8);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_174);
x_200 = lean_ctor_get_uint64(x_175, sizeof(void*)*1);
x_201 = lean_ctor_get(x_175, 0);
lean_inc_ref(x_201);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_202 = x_175;
} else {
 lean_dec_ref(x_175);
 x_202 = lean_box(0);
}
x_203 = l_Lean_PersistentArray_append___redArg(x_168, x_201);
lean_dec_ref(x_201);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 1, 8);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set_uint64(x_204, sizeof(void*)*1, x_200);
x_205 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_205, 0, x_192);
lean_ctor_set(x_205, 1, x_193);
lean_ctor_set(x_205, 2, x_194);
lean_ctor_set(x_205, 3, x_195);
lean_ctor_set(x_205, 4, x_204);
lean_ctor_set(x_205, 5, x_196);
lean_ctor_set(x_205, 6, x_197);
lean_ctor_set(x_205, 7, x_198);
lean_ctor_set(x_205, 8, x_199);
x_206 = lean_st_ref_set(x_11, x_205, x_176);
lean_dec(x_11);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec_ref(x_206);
x_208 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg(x_166, x_207);
lean_dec_ref(x_166);
return x_208;
}
}
else
{
lean_dec_ref(x_168);
x_62 = x_163;
x_63 = x_164;
x_64 = x_165;
x_65 = x_166;
x_66 = x_167;
x_67 = x_169;
x_68 = x_170;
goto block_78;
}
}
else
{
lean_dec_ref(x_168);
x_62 = x_163;
x_63 = x_164;
x_64 = x_165;
x_65 = x_166;
x_66 = x_167;
x_67 = x_169;
x_68 = x_170;
goto block_78;
}
}
block_221:
{
double x_219; uint8_t x_220; 
x_219 = lean_float_sub(x_216, x_215);
x_220 = lean_float_decLt(x_218, x_219);
x_163 = x_210;
x_164 = x_211;
x_165 = x_212;
x_166 = x_213;
x_167 = x_215;
x_168 = x_214;
x_169 = x_216;
x_170 = x_217;
x_171 = x_220;
goto block_209;
}
block_246:
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; double x_231; double x_232; double x_233; double x_234; double x_235; lean_object* x_236; uint8_t x_237; 
x_228 = lean_io_mono_nanos_now(x_227);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec_ref(x_228);
x_231 = lean_float_of_nat(x_222);
x_232 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__6;
x_233 = lean_float_div(x_231, x_232);
x_234 = lean_float_of_nat(x_229);
x_235 = lean_float_div(x_234, x_232);
x_236 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__3;
x_237 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_13, x_236);
if (x_237 == 0)
{
lean_dec(x_13);
lean_inc_ref(x_226);
x_163 = x_226;
x_164 = x_223;
x_165 = x_230;
x_166 = x_226;
x_167 = x_233;
x_168 = x_224;
x_169 = x_235;
x_170 = x_237;
x_171 = x_237;
goto block_209;
}
else
{
if (x_225 == 0)
{
lean_object* x_238; lean_object* x_239; double x_240; double x_241; double x_242; 
x_238 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__4;
x_239 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_13, x_238);
lean_dec(x_13);
x_240 = lean_float_of_nat(x_239);
x_241 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__5;
x_242 = lean_float_div(x_240, x_241);
lean_inc_ref(x_226);
x_210 = x_226;
x_211 = x_223;
x_212 = x_230;
x_213 = x_226;
x_214 = x_224;
x_215 = x_233;
x_216 = x_235;
x_217 = x_237;
x_218 = x_242;
goto block_221;
}
else
{
lean_object* x_243; lean_object* x_244; double x_245; 
x_243 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__4;
x_244 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_13, x_243);
lean_dec(x_13);
x_245 = lean_float_of_nat(x_244);
lean_inc_ref(x_226);
x_210 = x_226;
x_211 = x_223;
x_212 = x_230;
x_213 = x_226;
x_214 = x_224;
x_215 = x_233;
x_216 = x_235;
x_217 = x_237;
x_218 = x_245;
goto block_221;
}
}
}
block_272:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_247 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg(x_11, x_81);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec_ref(x_247);
x_250 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__7;
x_251 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_13, x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_io_mono_nanos_now(x_249);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec_ref(x_252);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_255 = lean_apply_7(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_254);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec_ref(x_255);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_256);
lean_inc(x_248);
x_222 = x_253;
x_223 = x_248;
x_224 = x_248;
x_225 = x_251;
x_226 = x_258;
x_227 = x_257;
goto block_246;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_255, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_255, 1);
lean_inc(x_260);
lean_dec_ref(x_255);
x_261 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_261, 0, x_259);
lean_inc(x_248);
x_222 = x_253;
x_223 = x_248;
x_224 = x_248;
x_225 = x_251;
x_226 = x_261;
x_227 = x_260;
goto block_246;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_io_get_num_heartbeats(x_249);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec_ref(x_262);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_265 = lean_apply_7(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_264);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec_ref(x_265);
x_268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_268, 0, x_266);
lean_inc(x_248);
x_141 = x_248;
x_142 = x_263;
x_143 = x_248;
x_144 = x_251;
x_145 = x_268;
x_146 = x_267;
goto block_162;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_265, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_265, 1);
lean_inc(x_270);
lean_dec_ref(x_265);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_269);
lean_inc(x_248);
x_141 = x_248;
x_142 = x_263;
x_143 = x_248;
x_144 = x_251;
x_145 = x_271;
x_146 = x_270;
goto block_162;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = l_Lean_Exception_toMessageData(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 0, x_14);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___redArg___lam__0___boxed), 8, 0);
x_13 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg___lam__0), 8, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___redArg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
return x_11;
}
else
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
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no instances for ", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("new goal ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc_ref(x_1);
x_11 = l_Lean_Meta_SynthInstance_mkGeneratorNode_x3f(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
x_16 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__1;
x_17 = l_Lean_MessageData_ofExpr(x_1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_box(0);
x_24 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__1;
x_25 = l_Lean_MessageData_ofExpr(x_1);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_dec_ref(x_11);
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_st_ref_take(x_5, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 3);
lean_inc_ref(x_35);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_33, 1);
x_38 = lean_ctor_get(x_33, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_34, 2);
lean_inc_ref(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; size_t x_85; lean_object* x_86; uint8_t x_87; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
x_46 = lean_unsigned_to_nat(1u);
x_47 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__2;
x_48 = lean_array_push(x_47, x_3);
x_49 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__3;
lean_ctor_set(x_33, 1, x_49);
lean_ctor_set(x_33, 0, x_48);
x_50 = lean_array_push(x_40, x_32);
x_73 = lean_array_get_size(x_45);
x_74 = l_Lean_Expr_hash(x_1);
x_75 = 32;
x_76 = lean_uint64_shift_right(x_74, x_75);
x_77 = lean_uint64_xor(x_74, x_76);
x_78 = 16;
x_79 = lean_uint64_shift_right(x_77, x_78);
x_80 = lean_uint64_xor(x_77, x_79);
x_81 = lean_uint64_to_usize(x_80);
x_82 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_83 = 1;
x_84 = lean_usize_sub(x_82, x_83);
x_85 = lean_usize_land(x_81, x_84);
x_86 = lean_array_uget(x_45, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_88 = lean_nat_add(x_44, x_46);
lean_dec(x_44);
lean_inc_ref(x_1);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_33);
lean_ctor_set(x_89, 2, x_86);
x_90 = lean_array_uset(x_45, x_85, x_89);
x_91 = lean_unsigned_to_nat(4u);
x_92 = lean_nat_mul(x_88, x_91);
x_93 = lean_unsigned_to_nat(3u);
x_94 = lean_nat_div(x_92, x_93);
lean_dec(x_92);
x_95 = lean_array_get_size(x_90);
x_96 = lean_nat_dec_le(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_90);
lean_ctor_set(x_35, 1, x_97);
lean_ctor_set(x_35, 0, x_88);
x_51 = x_35;
goto block_72;
}
else
{
lean_ctor_set(x_35, 1, x_90);
lean_ctor_set(x_35, 0, x_88);
x_51 = x_35;
goto block_72;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_box(0);
x_99 = lean_array_uset(x_45, x_85, x_98);
lean_inc_ref(x_1);
x_100 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_1, x_33, x_86);
x_101 = lean_array_uset(x_99, x_85, x_100);
lean_ctor_set(x_35, 1, x_101);
x_51 = x_35;
goto block_72;
}
block_72:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(0, 4, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_39);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_41);
lean_ctor_set(x_52, 3, x_51);
x_53 = lean_st_ref_set(x_5, x_52, x_37);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
x_56 = lean_box(0);
x_57 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__5;
x_58 = l_Lean_MessageData_ofExpr(x_1);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_53, 0, x_62);
return x_53;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_dec(x_53);
x_64 = lean_box(0);
x_65 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__5;
x_66 = l_Lean_MessageData_ofExpr(x_1);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_63);
return x_71;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; uint64_t x_130; size_t x_131; size_t x_132; size_t x_133; size_t x_134; size_t x_135; lean_object* x_136; uint8_t x_137; 
x_102 = lean_ctor_get(x_35, 0);
x_103 = lean_ctor_get(x_35, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_35);
x_104 = lean_unsigned_to_nat(1u);
x_105 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__2;
x_106 = lean_array_push(x_105, x_3);
x_107 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__3;
lean_ctor_set(x_33, 1, x_107);
lean_ctor_set(x_33, 0, x_106);
x_108 = lean_array_push(x_40, x_32);
x_123 = lean_array_get_size(x_103);
x_124 = l_Lean_Expr_hash(x_1);
x_125 = 32;
x_126 = lean_uint64_shift_right(x_124, x_125);
x_127 = lean_uint64_xor(x_124, x_126);
x_128 = 16;
x_129 = lean_uint64_shift_right(x_127, x_128);
x_130 = lean_uint64_xor(x_127, x_129);
x_131 = lean_uint64_to_usize(x_130);
x_132 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_133 = 1;
x_134 = lean_usize_sub(x_132, x_133);
x_135 = lean_usize_land(x_131, x_134);
x_136 = lean_array_uget(x_103, x_135);
x_137 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1, x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_138 = lean_nat_add(x_102, x_104);
lean_dec(x_102);
lean_inc_ref(x_1);
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_1);
lean_ctor_set(x_139, 1, x_33);
lean_ctor_set(x_139, 2, x_136);
x_140 = lean_array_uset(x_103, x_135, x_139);
x_141 = lean_unsigned_to_nat(4u);
x_142 = lean_nat_mul(x_138, x_141);
x_143 = lean_unsigned_to_nat(3u);
x_144 = lean_nat_div(x_142, x_143);
lean_dec(x_142);
x_145 = lean_array_get_size(x_140);
x_146 = lean_nat_dec_le(x_144, x_145);
lean_dec(x_145);
lean_dec(x_144);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_140);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
x_109 = x_148;
goto block_122;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_138);
lean_ctor_set(x_149, 1, x_140);
x_109 = x_149;
goto block_122;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_box(0);
x_151 = lean_array_uset(x_103, x_135, x_150);
lean_inc_ref(x_1);
x_152 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_1, x_33, x_136);
x_153 = lean_array_uset(x_151, x_135, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_102);
lean_ctor_set(x_154, 1, x_153);
x_109 = x_154;
goto block_122;
}
block_122:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
if (lean_is_scalar(x_42)) {
 x_110 = lean_alloc_ctor(0, 4, 0);
} else {
 x_110 = x_42;
}
lean_ctor_set(x_110, 0, x_39);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set(x_110, 2, x_41);
lean_ctor_set(x_110, 3, x_109);
x_111 = lean_st_ref_set(x_5, x_110, x_37);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = lean_box(0);
x_115 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__5;
x_116 = l_Lean_MessageData_ofExpr(x_1);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_119);
if (lean_is_scalar(x_113)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_113;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_112);
return x_121;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; uint64_t x_187; uint64_t x_188; uint64_t x_189; uint64_t x_190; size_t x_191; size_t x_192; size_t x_193; size_t x_194; size_t x_195; lean_object* x_196; uint8_t x_197; 
x_155 = lean_ctor_get(x_33, 1);
lean_inc(x_155);
lean_dec(x_33);
x_156 = lean_ctor_get(x_34, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_34, 2);
lean_inc_ref(x_158);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 x_159 = x_34;
} else {
 lean_dec_ref(x_34);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_35, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_35, 1);
lean_inc_ref(x_161);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_162 = x_35;
} else {
 lean_dec_ref(x_35);
 x_162 = lean_box(0);
}
x_163 = lean_unsigned_to_nat(1u);
x_164 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__2;
x_165 = lean_array_push(x_164, x_3);
x_166 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__3;
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_array_push(x_157, x_32);
x_183 = lean_array_get_size(x_161);
x_184 = l_Lean_Expr_hash(x_1);
x_185 = 32;
x_186 = lean_uint64_shift_right(x_184, x_185);
x_187 = lean_uint64_xor(x_184, x_186);
x_188 = 16;
x_189 = lean_uint64_shift_right(x_187, x_188);
x_190 = lean_uint64_xor(x_187, x_189);
x_191 = lean_uint64_to_usize(x_190);
x_192 = lean_usize_of_nat(x_183);
lean_dec(x_183);
x_193 = 1;
x_194 = lean_usize_sub(x_192, x_193);
x_195 = lean_usize_land(x_191, x_194);
x_196 = lean_array_uget(x_161, x_195);
x_197 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_198 = lean_nat_add(x_160, x_163);
lean_dec(x_160);
lean_inc_ref(x_1);
x_199 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_199, 0, x_1);
lean_ctor_set(x_199, 1, x_167);
lean_ctor_set(x_199, 2, x_196);
x_200 = lean_array_uset(x_161, x_195, x_199);
x_201 = lean_unsigned_to_nat(4u);
x_202 = lean_nat_mul(x_198, x_201);
x_203 = lean_unsigned_to_nat(3u);
x_204 = lean_nat_div(x_202, x_203);
lean_dec(x_202);
x_205 = lean_array_get_size(x_200);
x_206 = lean_nat_dec_le(x_204, x_205);
lean_dec(x_205);
lean_dec(x_204);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_200);
if (lean_is_scalar(x_162)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_162;
}
lean_ctor_set(x_208, 0, x_198);
lean_ctor_set(x_208, 1, x_207);
x_169 = x_208;
goto block_182;
}
else
{
lean_object* x_209; 
if (lean_is_scalar(x_162)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_162;
}
lean_ctor_set(x_209, 0, x_198);
lean_ctor_set(x_209, 1, x_200);
x_169 = x_209;
goto block_182;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_210 = lean_box(0);
x_211 = lean_array_uset(x_161, x_195, x_210);
lean_inc_ref(x_1);
x_212 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_1, x_167, x_196);
x_213 = lean_array_uset(x_211, x_195, x_212);
if (lean_is_scalar(x_162)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_162;
}
lean_ctor_set(x_214, 0, x_160);
lean_ctor_set(x_214, 1, x_213);
x_169 = x_214;
goto block_182;
}
block_182:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
if (lean_is_scalar(x_159)) {
 x_170 = lean_alloc_ctor(0, 4, 0);
} else {
 x_170 = x_159;
}
lean_ctor_set(x_170, 0, x_156);
lean_ctor_set(x_170, 1, x_168);
lean_ctor_set(x_170, 2, x_158);
lean_ctor_set(x_170, 3, x_169);
x_171 = lean_st_ref_set(x_5, x_170, x_155);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
x_174 = lean_box(0);
x_175 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__5;
x_176 = l_Lean_MessageData_ofExpr(x_1);
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_174);
lean_ctor_set(x_180, 1, x_179);
if (lean_is_scalar(x_173)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_173;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_172);
return x_181;
}
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_215 = !lean_is_exclusive(x_11);
if (x_215 == 0)
{
return x_11;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_11, 0);
x_217 = lean_ctor_get(x_11, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_11);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_2 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_newSubgoal___lam__0___boxed), 10, 3);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
x_13 = l_Lean_Meta_SynthInstance_newSubgoal___closed__0;
x_14 = 1;
x_15 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_16 = lean_box(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___boxed), 12, 5);
lean_closure_set(x_17, 0, lean_box(0));
lean_closure_set(x_17, 1, x_13);
lean_closure_set(x_17, 2, x_12);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_15);
x_18 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
x_14 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
x_15 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
x_13 = l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___redArg(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
x_14 = l_Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_SynthInstance_newSubgoal___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_6);
x_10 = lean_array_get_size(x_9);
x_11 = l_Lean_Expr_hash(x_1);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_9, x_22);
lean_dec_ref(x_9);
x_24 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(x_1, x_23);
lean_dec(x_23);
lean_ctor_set(x_4, 0, x_24);
return x_4;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_6);
x_27 = lean_array_get_size(x_26);
x_28 = l_Lean_Expr_hash(x_1);
x_29 = 32;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget(x_26, x_39);
lean_dec_ref(x_26);
x_41 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(x_1, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_25);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_findEntry_x3f___redArg(x_1, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_findEntry_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_SynthInstance_getEntry_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_SynthInstance_getEntry_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___Lean_Meta_SynthInstance_getEntry_spec__0___closed__0;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.SynthInstance.getEntry", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid key at synthInstance", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_SynthInstance_getEntry___closed__1;
x_2 = lean_unsigned_to_nat(18u);
x_3 = lean_unsigned_to_nat(272u);
x_4 = l_Lean_Meta_SynthInstance_getEntry___closed__0;
x_5 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Meta_SynthInstance_findEntry_x3f___redArg(x_1, x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_Meta_SynthInstance_getEntry___closed__2;
x_13 = l_panic___at___Lean_Meta_SynthInstance_getEntry_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getEntry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_getEntry(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_2, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_1, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__4;
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
x_11 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_1, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_2, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_14);
x_20 = lean_st_ref_set(x_2, x_16, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_13);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_16, 1);
x_26 = lean_ctor_get(x_16, 2);
x_27 = lean_ctor_get(x_16, 3);
x_28 = lean_ctor_get(x_16, 4);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_st_ref_set(x_2, x_29, x_17);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1___redArg(x_1, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_10, x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1___redArg(x_13, x_5, x_14);
lean_dec(x_5);
return x_15;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKeyFor___lam__0___boxed), 8, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_mkTableKeyFor___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_SynthInstance_getSubgoals_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_dec(x_15);
if (lean_obj_tag(x_14) == 7)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
x_22 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_23);
lean_dec(x_14);
x_24 = lean_expr_instantiate_rev(x_22, x_21);
lean_dec_ref(x_22);
x_25 = 0;
x_26 = 1;
x_27 = 1;
lean_inc_ref(x_1);
x_28 = l_Lean_Meta_mkForallFVars(x_1, x_24, x_25, x_26, x_26, x_27, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = 0;
x_32 = lean_box(0);
x_33 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_34 = l_Lean_Meta_mkFreshExprMVarAt(x_2, x_3, x_29, x_31, x_32, x_33, x_6, x_7, x_8, x_9, x_30);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
lean_inc(x_35);
x_37 = l_Lean_mkAppN(x_35, x_1);
lean_inc_ref(x_37);
x_38 = lean_array_push(x_21, x_37);
x_39 = l_Lean_Expr_app___override(x_17, x_37);
x_40 = lean_array_push(x_20, x_35);
lean_ctor_set(x_12, 1, x_38);
lean_ctor_set(x_12, 0, x_40);
lean_ctor_set(x_11, 0, x_39);
lean_ctor_set(x_5, 0, x_23);
x_10 = x_36;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec_ref(x_23);
lean_free_object(x_12);
lean_dec(x_21);
lean_dec(x_20);
lean_free_object(x_11);
lean_dec(x_17);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_28);
if (x_42 == 0)
{
return x_28;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_28, 0);
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_28);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_12, 0);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_12);
x_48 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_49);
lean_dec(x_14);
x_50 = lean_expr_instantiate_rev(x_48, x_47);
lean_dec_ref(x_48);
x_51 = 0;
x_52 = 1;
x_53 = 1;
lean_inc_ref(x_1);
x_54 = l_Lean_Meta_mkForallFVars(x_1, x_50, x_51, x_52, x_52, x_53, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = 0;
x_58 = lean_box(0);
x_59 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_60 = l_Lean_Meta_mkFreshExprMVarAt(x_2, x_3, x_55, x_57, x_58, x_59, x_6, x_7, x_8, x_9, x_56);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
lean_inc(x_61);
x_63 = l_Lean_mkAppN(x_61, x_1);
lean_inc_ref(x_63);
x_64 = lean_array_push(x_47, x_63);
x_65 = l_Lean_Expr_app___override(x_17, x_63);
x_66 = lean_array_push(x_46, x_61);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_11, 1, x_67);
lean_ctor_set(x_11, 0, x_65);
lean_ctor_set(x_5, 0, x_49);
x_10 = x_62;
goto _start;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_free_object(x_11);
lean_dec(x_17);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_69 = lean_ctor_get(x_54, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_54, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_71 = x_54;
} else {
 lean_dec_ref(x_54);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_11, 0);
lean_inc(x_73);
lean_dec(x_11);
x_74 = lean_ctor_get(x_12, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_12, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_76 = x_12;
} else {
 lean_dec_ref(x_12);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_78);
lean_dec(x_14);
x_79 = lean_expr_instantiate_rev(x_77, x_75);
lean_dec_ref(x_77);
x_80 = 0;
x_81 = 1;
x_82 = 1;
lean_inc_ref(x_1);
x_83 = l_Lean_Meta_mkForallFVars(x_1, x_79, x_80, x_81, x_81, x_82, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = 0;
x_87 = lean_box(0);
x_88 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_89 = l_Lean_Meta_mkFreshExprMVarAt(x_2, x_3, x_84, x_86, x_87, x_88, x_6, x_7, x_8, x_9, x_85);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec_ref(x_89);
lean_inc(x_90);
x_92 = l_Lean_mkAppN(x_90, x_1);
lean_inc_ref(x_92);
x_93 = lean_array_push(x_75, x_92);
x_94 = l_Lean_Expr_app___override(x_73, x_92);
x_95 = lean_array_push(x_74, x_90);
if (lean_is_scalar(x_76)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_76;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_5, 1, x_97);
lean_ctor_set(x_5, 0, x_78);
x_10 = x_91;
goto _start;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_78);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_99 = lean_ctor_get(x_83, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_83, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_101 = x_83;
} else {
 lean_dec_ref(x_83);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_11);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_11, 0);
x_105 = lean_ctor_get(x_11, 1);
lean_dec(x_105);
x_106 = !lean_is_exclusive(x_12);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_12, 0);
x_108 = lean_ctor_get(x_12, 1);
x_109 = lean_expr_instantiate_rev(x_14, x_108);
lean_dec(x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_110 = lean_whnf(x_109, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_ctor_get(x_110, 1);
x_114 = lean_expr_instantiate_rev(x_104, x_108);
lean_dec(x_108);
lean_dec(x_104);
x_115 = l_Lean_Expr_isForall(x_112);
if (x_115 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_11, 0, x_114);
lean_ctor_set(x_5, 0, x_112);
lean_ctor_set(x_110, 0, x_5);
return x_110;
}
else
{
lean_free_object(x_110);
lean_inc_ref(x_4);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_11, 0, x_114);
lean_ctor_set(x_5, 0, x_112);
x_10 = x_113;
goto _start;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_117 = lean_ctor_get(x_110, 0);
x_118 = lean_ctor_get(x_110, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_110);
x_119 = lean_expr_instantiate_rev(x_104, x_108);
lean_dec(x_108);
lean_dec(x_104);
x_120 = l_Lean_Expr_isForall(x_117);
if (x_120 == 0)
{
lean_object* x_121; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_11, 0, x_119);
lean_ctor_set(x_5, 0, x_117);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_5);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
else
{
lean_inc_ref(x_4);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_11, 0, x_119);
lean_ctor_set(x_5, 0, x_117);
x_10 = x_118;
goto _start;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_12);
lean_dec(x_108);
lean_dec(x_107);
lean_free_object(x_11);
lean_dec(x_104);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_123 = !lean_is_exclusive(x_110);
if (x_123 == 0)
{
return x_110;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_110, 0);
x_125 = lean_ctor_get(x_110, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_110);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_12, 0);
x_128 = lean_ctor_get(x_12, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_12);
x_129 = lean_expr_instantiate_rev(x_14, x_128);
lean_dec(x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_130 = lean_whnf(x_129, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_expr_instantiate_rev(x_104, x_128);
lean_dec(x_128);
lean_dec(x_104);
x_135 = l_Lean_Expr_isForall(x_131);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_4);
lean_ctor_set(x_11, 1, x_136);
lean_ctor_set(x_11, 0, x_134);
lean_ctor_set(x_5, 0, x_131);
if (lean_is_scalar(x_133)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_133;
}
lean_ctor_set(x_137, 0, x_5);
lean_ctor_set(x_137, 1, x_132);
return x_137;
}
else
{
lean_object* x_138; 
lean_dec(x_133);
lean_inc_ref(x_4);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_127);
lean_ctor_set(x_138, 1, x_4);
lean_ctor_set(x_11, 1, x_138);
lean_ctor_set(x_11, 0, x_134);
lean_ctor_set(x_5, 0, x_131);
x_10 = x_132;
goto _start;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_128);
lean_dec(x_127);
lean_free_object(x_11);
lean_dec(x_104);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_140 = lean_ctor_get(x_130, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_130, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_142 = x_130;
} else {
 lean_dec_ref(x_130);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_ctor_get(x_11, 0);
lean_inc(x_144);
lean_dec(x_11);
x_145 = lean_ctor_get(x_12, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_12, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_147 = x_12;
} else {
 lean_dec_ref(x_12);
 x_147 = lean_box(0);
}
x_148 = lean_expr_instantiate_rev(x_14, x_146);
lean_dec(x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_149 = lean_whnf(x_148, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_expr_instantiate_rev(x_144, x_146);
lean_dec(x_146);
lean_dec(x_144);
x_154 = l_Lean_Expr_isForall(x_150);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_scalar(x_147)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_147;
}
lean_ctor_set(x_155, 0, x_145);
lean_ctor_set(x_155, 1, x_4);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set(x_5, 1, x_156);
lean_ctor_set(x_5, 0, x_150);
if (lean_is_scalar(x_152)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_152;
}
lean_ctor_set(x_157, 0, x_5);
lean_ctor_set(x_157, 1, x_151);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_152);
lean_inc_ref(x_4);
if (lean_is_scalar(x_147)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_147;
}
lean_ctor_set(x_158, 0, x_145);
lean_ctor_set(x_158, 1, x_4);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_153);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_5, 1, x_159);
lean_ctor_set(x_5, 0, x_150);
x_10 = x_151;
goto _start;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_161 = lean_ctor_get(x_149, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_149, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_163 = x_149;
} else {
 lean_dec_ref(x_149);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
}
else
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_5, 0);
lean_inc(x_165);
lean_dec(x_5);
if (lean_obj_tag(x_165) == 7)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; lean_object* x_177; 
x_166 = lean_ctor_get(x_11, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_167 = x_11;
} else {
 lean_dec_ref(x_11);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_12, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_12, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_170 = x_12;
} else {
 lean_dec_ref(x_12);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_165, 1);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_165, 2);
lean_inc_ref(x_172);
lean_dec(x_165);
x_173 = lean_expr_instantiate_rev(x_171, x_169);
lean_dec_ref(x_171);
x_174 = 0;
x_175 = 1;
x_176 = 1;
lean_inc_ref(x_1);
x_177 = l_Lean_Meta_mkForallFVars(x_1, x_173, x_174, x_175, x_175, x_176, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec_ref(x_177);
x_180 = 0;
x_181 = lean_box(0);
x_182 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_183 = l_Lean_Meta_mkFreshExprMVarAt(x_2, x_3, x_178, x_180, x_181, x_182, x_6, x_7, x_8, x_9, x_179);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec_ref(x_183);
lean_inc(x_184);
x_186 = l_Lean_mkAppN(x_184, x_1);
lean_inc_ref(x_186);
x_187 = lean_array_push(x_169, x_186);
x_188 = l_Lean_Expr_app___override(x_166, x_186);
x_189 = lean_array_push(x_168, x_184);
if (lean_is_scalar(x_170)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_170;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
if (lean_is_scalar(x_167)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_167;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_172);
lean_ctor_set(x_192, 1, x_191);
x_5 = x_192;
x_10 = x_185;
goto _start;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec_ref(x_172);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_194 = lean_ctor_get(x_177, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_177, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_196 = x_177;
} else {
 lean_dec_ref(x_177);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_198 = lean_ctor_get(x_11, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_199 = x_11;
} else {
 lean_dec_ref(x_11);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_12, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_12, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_202 = x_12;
} else {
 lean_dec_ref(x_12);
 x_202 = lean_box(0);
}
x_203 = lean_expr_instantiate_rev(x_165, x_201);
lean_dec(x_165);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_204 = lean_whnf(x_203, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_expr_instantiate_rev(x_198, x_201);
lean_dec(x_201);
lean_dec(x_198);
x_209 = l_Lean_Expr_isForall(x_205);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_scalar(x_202)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_202;
}
lean_ctor_set(x_210, 0, x_200);
lean_ctor_set(x_210, 1, x_4);
if (lean_is_scalar(x_199)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_199;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_205);
lean_ctor_set(x_212, 1, x_211);
if (lean_is_scalar(x_207)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_207;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_206);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_207);
lean_inc_ref(x_4);
if (lean_is_scalar(x_202)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_202;
}
lean_ctor_set(x_214, 0, x_200);
lean_ctor_set(x_214, 1, x_4);
if (lean_is_scalar(x_199)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_199;
}
lean_ctor_set(x_215, 0, x_208);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_205);
lean_ctor_set(x_216, 1, x_215);
x_5 = x_216;
x_10 = x_206;
goto _start;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_218 = lean_ctor_get(x_204, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_204, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_220 = x_204;
} else {
 lean_dec_ref(x_204);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getSubgoals_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
lean_inc_ref(x_1);
x_10 = lean_array_get(x_1, x_2, x_7);
lean_dec(x_7);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_13 = lean_array_uset(x_9, x_4, x_10);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getSubgoals___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getSubgoals___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_getSubgoals___closed__0;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getSubgoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_11);
x_13 = lean_infer_type(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_SynthInstance_getSubgoals___closed__0;
x_17 = l_Lean_Meta_SynthInstance_getSubgoals___closed__1;
lean_ctor_set(x_4, 1, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_4);
x_19 = l_Lean_Loop_forIn_loop___at___Lean_Meta_SynthInstance_getSubgoals_spec__0(x_3, x_1, x_2, x_16, x_18, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Lean_instInhabitedExpr;
x_30 = lean_array_size(x_12);
x_31 = 0;
x_32 = l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getSubgoals_spec__1(x_29, x_27, x_30, x_31, x_12);
lean_dec(x_27);
x_33 = lean_array_to_list(x_32);
x_34 = lean_expr_instantiate_rev(x_26, x_28);
lean_dec(x_26);
x_35 = lean_expr_instantiate_rev(x_25, x_28);
lean_dec(x_28);
lean_dec(x_25);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_19, 0, x_36);
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_dec(x_19);
x_38 = lean_ctor_get(x_20, 0);
lean_inc(x_38);
lean_dec(x_20);
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
lean_dec(x_21);
x_40 = lean_ctor_get(x_22, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_dec(x_22);
x_42 = l_Lean_instInhabitedExpr;
x_43 = lean_array_size(x_12);
x_44 = 0;
x_45 = l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getSubgoals_spec__1(x_42, x_40, x_43, x_44, x_12);
lean_dec(x_40);
x_46 = lean_array_to_list(x_45);
x_47 = lean_expr_instantiate_rev(x_39, x_41);
lean_dec(x_39);
x_48 = lean_expr_instantiate_rev(x_38, x_41);
lean_dec(x_41);
lean_dec(x_38);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_37);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec_ref(x_12);
x_51 = !lean_is_exclusive(x_19);
if (x_51 == 0)
{
return x_19;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_19);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_free_object(x_4);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
return x_13;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_13, 0);
x_57 = lean_ctor_get(x_13, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_13);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_4, 0);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_59);
x_61 = lean_infer_type(x_59, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = l_Lean_Meta_SynthInstance_getSubgoals___closed__0;
x_65 = l_Lean_Meta_SynthInstance_getSubgoals___closed__1;
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Loop_forIn_loop___at___Lean_Meta_SynthInstance_getSubgoals_spec__0(x_3, x_1, x_2, x_64, x_67, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
lean_dec(x_70);
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_dec(x_71);
x_78 = l_Lean_instInhabitedExpr;
x_79 = lean_array_size(x_60);
x_80 = 0;
x_81 = l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getSubgoals_spec__1(x_78, x_76, x_79, x_80, x_60);
lean_dec(x_76);
x_82 = lean_array_to_list(x_81);
x_83 = lean_expr_instantiate_rev(x_75, x_77);
lean_dec(x_75);
x_84 = lean_expr_instantiate_rev(x_74, x_77);
lean_dec(x_77);
lean_dec(x_74);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_85, 2, x_84);
if (lean_is_scalar(x_73)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_73;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_72);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_60);
x_87 = lean_ctor_get(x_68, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_68, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_89 = x_68;
} else {
 lean_dec_ref(x_68);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_91 = lean_ctor_get(x_61, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_61, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_93 = x_61;
} else {
 lean_dec_ref(x_61);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getSubgoals_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_getSubgoals_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_16 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_12 = x_19;
goto block_15;
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec_ref(x_16);
x_21 = 0;
x_22 = 1;
x_23 = lean_unbox(x_17);
x_24 = lean_unbox(x_17);
x_25 = lean_unbox(x_17);
lean_dec(x_17);
x_26 = l_Lean_Meta_mkLambdaFVars(x_3, x_4, x_21, x_23, x_24, x_25, x_22, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
lean_inc(x_8);
x_29 = l_Lean_Meta_isExprDefEq(x_5, x_27, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_6);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec_ref(x_29);
x_12 = x_32;
goto block_15;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec_ref(x_29);
x_34 = lean_st_ref_get(x_8, x_33);
lean_dec(x_8);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_6);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_6);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_8);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_29);
if (x_46 == 0)
{
return x_29;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_29, 0);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_29);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_50 = !lean_is_exclusive(x_26);
if (x_50 == 0)
{
return x_26;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_26, 0);
x_52 = lean_ctor_get(x_26, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_26);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_54 = !lean_is_exclusive(x_16);
if (x_54 == 0)
{
return x_16;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_16, 0);
x_56 = lean_ctor_get(x_16, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_16);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ≟ ", 5, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_1, x_5, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_2, x_5, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_17 = l_Lean_exceptOptionEmoji___redArg(x_3);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec_ref(x_17);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_18);
lean_ctor_set(x_9, 0, x_16);
x_19 = l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__1;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_MessageData_ofExpr(x_11);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__3;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_MessageData_ofExpr(x_15);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_31 = l_Lean_exceptOptionEmoji___redArg(x_3);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec_ref(x_31);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_32);
lean_ctor_set(x_9, 0, x_30);
x_33 = l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__1;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_9);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_MessageData_ofExpr(x_11);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__3;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_MessageData_ofExpr(x_28);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_30);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_29);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_43 = lean_ctor_get(x_9, 0);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_9);
x_45 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_2, x_5, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_50 = l_Lean_exceptOptionEmoji___redArg(x_3);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec_ref(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__1;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_MessageData_ofExpr(x_43);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__3;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_MessageData_ofExpr(x_46);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_49);
if (lean_is_scalar(x_48)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_48;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_47);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolve___lam__1___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_4);
x_11 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0___redArg(x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tryResolve", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__0;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_5);
x_12 = l_Lean_Meta_SynthInstance_getSubgoals(x_1, x_2, x_5, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_17);
lean_dec(x_13);
x_18 = lean_st_ref_get(x_8, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
lean_inc_ref(x_17);
lean_inc_ref(x_6);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolve___lam__0), 11, 6);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_17);
lean_closure_set(x_22, 2, x_5);
lean_closure_set(x_22, 3, x_16);
lean_closure_set(x_22, 4, x_4);
lean_closure_set(x_22, 5, x_15);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolve___lam__2), 9, 3);
lean_closure_set(x_23, 0, x_6);
lean_closure_set(x_23, 1, x_17);
lean_closure_set(x_23, 2, x_21);
x_24 = l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__1;
x_25 = 1;
x_26 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_27 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0___redArg(x_24, x_23, x_22, x_25, x_26, x_7, x_8, x_9, x_10, x_20);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_isDiagnosticsEnabled___redArg(x_5, x_7);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec_ref(x_28);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_31;
goto block_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec_ref(x_28);
x_33 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_33);
x_34 = l_Lean_Expr_getAppFn(x_33);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 4)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Meta_recordInstance___redArg(x_35, x_4, x_5, x_32);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_37;
goto block_27;
}
else
{
lean_dec_ref(x_34);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_32;
goto block_27;
}
}
block_27:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_13 = lean_infer_type(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_getLocalInstances___redArg(x_8, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_19);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolve___lam__3), 11, 4);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_1);
x_21 = 0;
x_22 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_14, x_20, x_21, x_21, x_8, x_9, x_10, x_11, x_18);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_tryResolve___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_5);
x_10 = l_Lean_Meta_openAbstractMVarsResult(x_1, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
x_15 = l_Lean_Meta_isExprDefEq(x_2, x_14, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_6);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec_ref(x_15);
x_25 = lean_st_ref_get(x_6, x_24);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryAnswer___lam__0___boxed), 9, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_2);
x_13 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_tryAnswer___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc_ref(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 4);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; double x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__0;
x_23 = 0;
x_24 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg___closed__0;
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_8);
x_28 = l_Lean_PersistentArray_push___redArg(x_21, x_12);
lean_ctor_set(x_14, 0, x_28);
x_29 = lean_st_ref_set(x_6, x_13, x_16);
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
uint64_t x_36; lean_object* x_37; double x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__0;
x_39 = 0;
x_40 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_39);
x_42 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg___closed__0;
x_43 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_10);
lean_ctor_set(x_43, 2, x_42);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_43);
lean_ctor_set(x_12, 0, x_8);
x_44 = l_Lean_PersistentArray_push___redArg(x_37, x_12);
x_45 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint64(x_45, sizeof(void*)*1, x_36);
lean_ctor_set(x_13, 4, x_45);
x_46 = lean_st_ref_set(x_6, x_13, x_16);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; double x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
x_53 = lean_ctor_get(x_13, 2);
x_54 = lean_ctor_get(x_13, 3);
x_55 = lean_ctor_get(x_13, 5);
x_56 = lean_ctor_get(x_13, 6);
x_57 = lean_ctor_get(x_13, 7);
x_58 = lean_ctor_get(x_13, 8);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_59 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_60 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_61 = x_14;
} else {
 lean_dec_ref(x_14);
 x_61 = lean_box(0);
}
x_62 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__0;
x_63 = 0;
x_64 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_65 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_float(x_65, sizeof(void*)*2, x_62);
lean_ctor_set_float(x_65, sizeof(void*)*2 + 8, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 16, x_63);
x_66 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg___closed__0;
x_67 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_10);
lean_ctor_set(x_67, 2, x_66);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_67);
lean_ctor_set(x_12, 0, x_8);
x_68 = l_Lean_PersistentArray_push___redArg(x_60, x_12);
if (lean_is_scalar(x_61)) {
 x_69 = lean_alloc_ctor(0, 1, 8);
} else {
 x_69 = x_61;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_uint64(x_69, sizeof(void*)*1, x_59);
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_52);
lean_ctor_set(x_70, 2, x_53);
lean_ctor_set(x_70, 3, x_54);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_55);
lean_ctor_set(x_70, 6, x_56);
lean_ctor_set(x_70, 7, x_57);
lean_ctor_set(x_70, 8, x_58);
x_71 = lean_st_ref_set(x_6, x_70, x_16);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; double x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_dec(x_12);
x_77 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_13, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_13, 3);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_13, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_13, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_13, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_13, 8);
lean_inc_ref(x_84);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 lean_ctor_release(x_13, 6);
 lean_ctor_release(x_13, 7);
 lean_ctor_release(x_13, 8);
 x_85 = x_13;
} else {
 lean_dec_ref(x_13);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_87 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_88 = x_14;
} else {
 lean_dec_ref(x_14);
 x_88 = lean_box(0);
}
x_89 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__0;
x_90 = 0;
x_91 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_92 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_float(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_float(x_92, sizeof(void*)*2 + 8, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 16, x_90);
x_93 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg___closed__0;
x_94 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_10);
lean_ctor_set(x_94, 2, x_93);
lean_inc(x_8);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_8);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_PersistentArray_push___redArg(x_87, x_95);
if (lean_is_scalar(x_88)) {
 x_97 = lean_alloc_ctor(0, 1, 8);
} else {
 x_97 = x_88;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set_uint64(x_97, sizeof(void*)*1, x_86);
if (lean_is_scalar(x_85)) {
 x_98 = lean_alloc_ctor(0, 9, 0);
} else {
 x_98 = x_85;
}
lean_ctor_set(x_98, 0, x_77);
lean_ctor_set(x_98, 1, x_78);
lean_ctor_set(x_98, 2, x_79);
lean_ctor_set(x_98, 3, x_80);
lean_ctor_set(x_98, 4, x_97);
lean_ctor_set(x_98, 5, x_81);
lean_ctor_set(x_98, 6, x_82);
lean_ctor_set(x_98, 7, x_83);
lean_ctor_set(x_98, 8, x_84);
x_99 = lean_st_ref_set(x_6, x_98, x_76);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("skip answer containing metavariables ", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_wakeUp___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_wakeUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec_ref(x_5);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_st_ref_take(x_4, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_10);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 0, x_10);
x_17 = lean_array_push(x_16, x_11);
lean_ctor_set(x_13, 2, x_17);
x_18 = lean_st_ref_set(x_4, x_13, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
x_28 = lean_ctor_get(x_13, 2);
x_29 = lean_ctor_get(x_13, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
lean_inc_ref(x_10);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 0, x_10);
x_30 = lean_array_push(x_28, x_11);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_29);
x_32 = lean_st_ref_set(x_4, x_31, x_25);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_11, 0);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_11);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_37, 2);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_37, 3);
lean_inc_ref(x_42);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_43 = x_37;
} else {
 lean_dec_ref(x_37);
 x_43 = lean_box(0);
}
lean_inc_ref(x_10);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_10);
lean_ctor_set(x_44, 1, x_1);
x_45 = lean_array_push(x_41, x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 4, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_42);
x_47 = lean_st_ref_set(x_4, x_46, x_38);
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_52);
lean_dec_ref(x_1);
x_53 = l_Lean_Meta_AbstractMVarsResult_numMVars(x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_53, x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc_ref(x_5);
x_56 = l_Lean_Meta_openAbstractMVarsResult(x_52, x_5, x_6, x_7, x_8, x_9);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_57, 1);
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec_ref(x_56);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_59, 1);
x_64 = lean_ctor_get(x_59, 0);
lean_dec(x_64);
x_65 = l_Lean_Meta_SynthInstance_newSubgoal___closed__0;
x_66 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg(x_65, x_7, x_61);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
uint8_t x_69; 
lean_free_object(x_59);
lean_dec(x_63);
lean_free_object(x_57);
lean_dec_ref(x_5);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
x_71 = lean_box(0);
lean_ctor_set(x_66, 0, x_71);
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_66, 1);
lean_inc(x_75);
lean_dec_ref(x_66);
x_76 = l_Lean_Meta_SynthInstance_wakeUp___closed__1;
x_77 = l_Lean_MessageData_ofExpr(x_63);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_77);
lean_ctor_set(x_59, 0, x_76);
x_78 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_78);
lean_ctor_set(x_57, 0, x_59);
x_79 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg(x_65, x_57, x_5, x_6, x_7, x_8, x_75);
lean_dec_ref(x_5);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_59, 1);
lean_inc(x_80);
lean_dec(x_59);
x_81 = l_Lean_Meta_SynthInstance_newSubgoal___closed__0;
x_82 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg(x_81, x_7, x_61);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_80);
lean_free_object(x_57);
lean_dec_ref(x_5);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_86 = x_82;
} else {
 lean_dec_ref(x_82);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec_ref(x_82);
x_90 = l_Lean_Meta_SynthInstance_wakeUp___closed__1;
x_91 = l_Lean_MessageData_ofExpr(x_80);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_93);
lean_ctor_set(x_57, 0, x_92);
x_94 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg(x_81, x_57, x_5, x_6, x_7, x_8, x_89);
lean_dec_ref(x_5);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_95 = lean_ctor_get(x_57, 1);
lean_inc(x_95);
lean_dec(x_57);
x_96 = lean_ctor_get(x_56, 1);
lean_inc(x_96);
lean_dec_ref(x_56);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = l_Lean_Meta_SynthInstance_newSubgoal___closed__0;
x_100 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg(x_99, x_7, x_96);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec_ref(x_5);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_104 = x_100;
} else {
 lean_dec_ref(x_100);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_100, 1);
lean_inc(x_107);
lean_dec_ref(x_100);
x_108 = l_Lean_Meta_SynthInstance_wakeUp___closed__1;
x_109 = l_Lean_MessageData_ofExpr(x_97);
if (lean_is_scalar(x_98)) {
 x_110 = lean_alloc_ctor(7, 2, 0);
} else {
 x_110 = x_98;
 lean_ctor_set_tag(x_110, 7);
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg(x_99, x_112, x_5, x_6, x_7, x_8, x_107);
lean_dec_ref(x_5);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec_ref(x_5);
x_114 = lean_st_ref_take(x_4, x_9);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec_ref(x_114);
x_117 = !lean_is_exclusive(x_115);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_118 = lean_ctor_get(x_115, 0);
lean_dec(x_118);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_52);
lean_ctor_set(x_115, 0, x_119);
x_120 = lean_st_ref_set(x_4, x_115, x_116);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_120, 0);
lean_dec(x_122);
x_123 = lean_box(0);
lean_ctor_set(x_120, 0, x_123);
return x_120;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_dec(x_120);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_127 = lean_ctor_get(x_115, 1);
x_128 = lean_ctor_get(x_115, 2);
x_129 = lean_ctor_get(x_115, 3);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_115);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_52);
x_131 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_127);
lean_ctor_set(x_131, 2, x_128);
lean_ctor_set(x_131, 3, x_129);
x_132 = lean_st_ref_set(x_4, x_131, x_116);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
x_135 = lean_box(0);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_wakeUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_wakeUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SynthInstance_isNewAnswer_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_expr_eqv(x_7, x_8);
lean_dec_ref(x_7);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
return x_9;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SynthInstance_isNewAnswer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_anyMUnsafe_any___at___Lean_Meta_SynthInstance_isNewAnswer_spec__0(x_2, x_1, x_7, x_8);
if (x_9 == 0)
{
return x_5;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SynthInstance_isNewAnswer_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Meta_SynthInstance_isNewAnswer_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_isNewAnswer___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SynthInstance_isNewAnswer(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("newAnswer", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__0;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("size: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", val: ", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_1, x_4, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_39 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__1;
x_40 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_39, x_5, x_11);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_free_object(x_8);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec_ref(x_40);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_43;
goto block_38;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_40, 1);
x_46 = lean_ctor_get(x_40, 0);
lean_dec(x_46);
x_47 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__3;
lean_inc(x_2);
x_48 = l_Nat_reprFast(x_2);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_49);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_50);
lean_ctor_set(x_40, 0, x_47);
x_51 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__5;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_51);
lean_ctor_set(x_8, 0, x_40);
lean_inc(x_10);
x_52 = l_Lean_MessageData_ofExpr(x_10);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_8);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_39, x_55, x_3, x_4, x_5, x_6, x_45);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec_ref(x_56);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_57;
goto block_38;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_58 = lean_ctor_get(x_40, 1);
lean_inc(x_58);
lean_dec(x_40);
x_59 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__3;
lean_inc(x_2);
x_60 = l_Nat_reprFast(x_2);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_MessageData_ofFormat(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__5;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_64);
lean_ctor_set(x_8, 0, x_63);
lean_inc(x_10);
x_65 = l_Lean_MessageData_ofExpr(x_10);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_8);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_39, x_68, x_3, x_4, x_5, x_6, x_58);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_70;
goto block_38;
}
}
block_38:
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = 1;
x_18 = l_Lean_Meta_abstractMVars___redArg(x_10, x_17, x_12, x_13, x_15, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 2);
lean_inc_ref(x_21);
x_22 = lean_infer_type(x_21, x_12, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_2, x_30);
lean_dec(x_2);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_19);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_71 = lean_ctor_get(x_8, 0);
x_72 = lean_ctor_get(x_8, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_8);
x_96 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__1;
x_97 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_96, x_5, x_72);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec_ref(x_97);
x_73 = x_3;
x_74 = x_4;
x_75 = x_5;
x_76 = x_6;
x_77 = x_100;
goto block_95;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_102 = x_97;
} else {
 lean_dec_ref(x_97);
 x_102 = lean_box(0);
}
x_103 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__3;
lean_inc(x_2);
x_104 = l_Nat_reprFast(x_2);
x_105 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_MessageData_ofFormat(x_105);
if (lean_is_scalar(x_102)) {
 x_107 = lean_alloc_ctor(7, 2, 0);
} else {
 x_107 = x_102;
 lean_ctor_set_tag(x_107, 7);
}
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_106);
x_108 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__5;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
lean_inc(x_71);
x_110 = l_Lean_MessageData_ofExpr(x_71);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_96, x_113, x_3, x_4, x_5, x_6, x_101);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec_ref(x_114);
x_73 = x_3;
x_74 = x_4;
x_75 = x_5;
x_76 = x_6;
x_77 = x_115;
goto block_95;
}
block_95:
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = 1;
x_79 = l_Lean_Meta_abstractMVars___redArg(x_71, x_78, x_73, x_74, x_76, x_77);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_ctor_get(x_80, 2);
lean_inc_ref(x_82);
x_83 = lean_infer_type(x_82, x_73, x_74, x_75, x_76, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
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
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_2, x_87);
lean_dec(x_2);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_84);
lean_ctor_set(x_89, 2, x_88);
if (lean_is_scalar(x_86)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_86;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_80);
lean_dec(x_2);
x_91 = lean_ctor_get(x_83, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_83, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_93 = x_83;
} else {
 lean_dec_ref(x_83);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0), 7, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0___redArg(x_8, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_addAnswer_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_14 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_SynthInstance_wakeUp(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_16;
x_12 = x_17;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_10 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_13 = l_Lean_Meta_SynthInstance_getEntry(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = l_Lean_Meta_SynthInstance_isNewAnswer(x_19, x_11);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_15);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_21 = lean_box(0);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_56; 
lean_free_object(x_13);
x_22 = lean_st_ref_take(x_4, x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_28);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 x_29 = x_23;
} else {
 lean_dec_ref(x_23);
 x_29 = lean_box(0);
}
x_56 = !lean_is_exclusive(x_28);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; uint8_t x_74; 
x_57 = lean_ctor_get(x_28, 0);
x_58 = lean_ctor_get(x_28, 1);
lean_inc(x_11);
x_59 = lean_array_push(x_19, x_11);
lean_inc_ref(x_18);
lean_ctor_set(x_15, 1, x_59);
x_60 = lean_array_get_size(x_58);
x_61 = l_Lean_Expr_hash(x_2);
x_62 = 32;
x_63 = lean_uint64_shift_right(x_61, x_62);
x_64 = lean_uint64_xor(x_61, x_63);
x_65 = 16;
x_66 = lean_uint64_shift_right(x_64, x_65);
x_67 = lean_uint64_xor(x_64, x_66);
x_68 = lean_uint64_to_usize(x_67);
x_69 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_70 = 1;
x_71 = lean_usize_sub(x_69, x_70);
x_72 = lean_usize_land(x_68, x_71);
x_73 = lean_array_uget(x_58, x_72);
x_74 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_2, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_57, x_75);
lean_dec(x_57);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_15);
lean_ctor_set(x_77, 2, x_73);
x_78 = lean_array_uset(x_58, x_72, x_77);
x_79 = lean_unsigned_to_nat(4u);
x_80 = lean_nat_mul(x_76, x_79);
x_81 = lean_unsigned_to_nat(3u);
x_82 = lean_nat_div(x_80, x_81);
lean_dec(x_80);
x_83 = lean_array_get_size(x_78);
x_84 = lean_nat_dec_le(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_78);
lean_ctor_set(x_28, 1, x_85);
lean_ctor_set(x_28, 0, x_76);
x_30 = x_28;
goto block_55;
}
else
{
lean_ctor_set(x_28, 1, x_78);
lean_ctor_set(x_28, 0, x_76);
x_30 = x_28;
goto block_55;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_box(0);
x_87 = lean_array_uset(x_58, x_72, x_86);
x_88 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_2, x_15, x_73);
x_89 = lean_array_uset(x_87, x_72, x_88);
lean_ctor_set(x_28, 1, x_89);
x_30 = x_28;
goto block_55;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; size_t x_101; size_t x_102; size_t x_103; size_t x_104; size_t x_105; lean_object* x_106; uint8_t x_107; 
x_90 = lean_ctor_get(x_28, 0);
x_91 = lean_ctor_get(x_28, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_28);
lean_inc(x_11);
x_92 = lean_array_push(x_19, x_11);
lean_inc_ref(x_18);
lean_ctor_set(x_15, 1, x_92);
x_93 = lean_array_get_size(x_91);
x_94 = l_Lean_Expr_hash(x_2);
x_95 = 32;
x_96 = lean_uint64_shift_right(x_94, x_95);
x_97 = lean_uint64_xor(x_94, x_96);
x_98 = 16;
x_99 = lean_uint64_shift_right(x_97, x_98);
x_100 = lean_uint64_xor(x_97, x_99);
x_101 = lean_uint64_to_usize(x_100);
x_102 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_103 = 1;
x_104 = lean_usize_sub(x_102, x_103);
x_105 = lean_usize_land(x_101, x_104);
x_106 = lean_array_uget(x_91, x_105);
x_107 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_2, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_nat_add(x_90, x_108);
lean_dec(x_90);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_2);
lean_ctor_set(x_110, 1, x_15);
lean_ctor_set(x_110, 2, x_106);
x_111 = lean_array_uset(x_91, x_105, x_110);
x_112 = lean_unsigned_to_nat(4u);
x_113 = lean_nat_mul(x_109, x_112);
x_114 = lean_unsigned_to_nat(3u);
x_115 = lean_nat_div(x_113, x_114);
lean_dec(x_113);
x_116 = lean_array_get_size(x_111);
x_117 = lean_nat_dec_le(x_115, x_116);
lean_dec(x_116);
lean_dec(x_115);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_111);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_109);
lean_ctor_set(x_119, 1, x_118);
x_30 = x_119;
goto block_55;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_109);
lean_ctor_set(x_120, 1, x_111);
x_30 = x_120;
goto block_55;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_box(0);
x_122 = lean_array_uset(x_91, x_105, x_121);
x_123 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_2, x_15, x_106);
x_124 = lean_array_uset(x_122, x_105, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_90);
lean_ctor_set(x_125, 1, x_124);
x_30 = x_125;
goto block_55;
}
}
block_55:
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 4, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_st_ref_set(x_4, x_31, x_24);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_array_get_size(x_18);
x_38 = lean_box(0);
x_39 = lean_nat_dec_lt(x_36, x_37);
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_ctor_set(x_32, 0, x_38);
return x_32;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_37, x_37);
if (x_40 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_ctor_set(x_32, 0, x_38);
return x_32;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
lean_free_object(x_32);
x_41 = 0;
x_42 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_43 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_addAnswer_spec__0(x_11, x_18, x_41, x_42, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_18);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get_size(x_18);
x_47 = lean_box(0);
x_48 = lean_nat_dec_lt(x_45, x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_46);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_46, x_46);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_46);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_54 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_addAnswer_spec__0(x_11, x_18, x_52, x_53, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_18);
return x_54;
}
}
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_13, 1);
x_127 = lean_ctor_get(x_15, 0);
x_128 = lean_ctor_get(x_15, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_15);
x_129 = l_Lean_Meta_SynthInstance_isNewAnswer(x_128, x_11);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_130 = lean_box(0);
lean_ctor_set(x_13, 0, x_130);
return x_13;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint64_t x_161; uint64_t x_162; uint64_t x_163; uint64_t x_164; uint64_t x_165; uint64_t x_166; uint64_t x_167; size_t x_168; size_t x_169; size_t x_170; size_t x_171; size_t x_172; lean_object* x_173; uint8_t x_174; 
lean_free_object(x_13);
x_131 = lean_st_ref_take(x_4, x_126);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec_ref(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_132, 2);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_132, 3);
lean_inc_ref(x_137);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 lean_ctor_release(x_132, 3);
 x_138 = x_132;
} else {
 lean_dec_ref(x_132);
 x_138 = lean_box(0);
}
x_155 = lean_ctor_get(x_137, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_137, 1);
lean_inc_ref(x_156);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_157 = x_137;
} else {
 lean_dec_ref(x_137);
 x_157 = lean_box(0);
}
lean_inc(x_11);
x_158 = lean_array_push(x_128, x_11);
lean_inc_ref(x_127);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_127);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_array_get_size(x_156);
x_161 = l_Lean_Expr_hash(x_2);
x_162 = 32;
x_163 = lean_uint64_shift_right(x_161, x_162);
x_164 = lean_uint64_xor(x_161, x_163);
x_165 = 16;
x_166 = lean_uint64_shift_right(x_164, x_165);
x_167 = lean_uint64_xor(x_164, x_166);
x_168 = lean_uint64_to_usize(x_167);
x_169 = lean_usize_of_nat(x_160);
lean_dec(x_160);
x_170 = 1;
x_171 = lean_usize_sub(x_169, x_170);
x_172 = lean_usize_land(x_168, x_171);
x_173 = lean_array_uget(x_156, x_172);
x_174 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_2, x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_add(x_155, x_175);
lean_dec(x_155);
x_177 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_177, 0, x_2);
lean_ctor_set(x_177, 1, x_159);
lean_ctor_set(x_177, 2, x_173);
x_178 = lean_array_uset(x_156, x_172, x_177);
x_179 = lean_unsigned_to_nat(4u);
x_180 = lean_nat_mul(x_176, x_179);
x_181 = lean_unsigned_to_nat(3u);
x_182 = lean_nat_div(x_180, x_181);
lean_dec(x_180);
x_183 = lean_array_get_size(x_178);
x_184 = lean_nat_dec_le(x_182, x_183);
lean_dec(x_183);
lean_dec(x_182);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_178);
if (lean_is_scalar(x_157)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_157;
}
lean_ctor_set(x_186, 0, x_176);
lean_ctor_set(x_186, 1, x_185);
x_139 = x_186;
goto block_154;
}
else
{
lean_object* x_187; 
if (lean_is_scalar(x_157)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_157;
}
lean_ctor_set(x_187, 0, x_176);
lean_ctor_set(x_187, 1, x_178);
x_139 = x_187;
goto block_154;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_188 = lean_box(0);
x_189 = lean_array_uset(x_156, x_172, x_188);
x_190 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_2, x_159, x_173);
x_191 = lean_array_uset(x_189, x_172, x_190);
if (lean_is_scalar(x_157)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_157;
}
lean_ctor_set(x_192, 0, x_155);
lean_ctor_set(x_192, 1, x_191);
x_139 = x_192;
goto block_154;
}
block_154:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 4, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_134);
lean_ctor_set(x_140, 1, x_135);
lean_ctor_set(x_140, 2, x_136);
lean_ctor_set(x_140, 3, x_139);
x_141 = lean_st_ref_set(x_4, x_140, x_133);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_unsigned_to_nat(0u);
x_145 = lean_array_get_size(x_127);
x_146 = lean_box(0);
x_147 = lean_nat_dec_lt(x_144, x_145);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_145);
lean_dec_ref(x_127);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_is_scalar(x_143)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_143;
}
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_142);
return x_148;
}
else
{
uint8_t x_149; 
x_149 = lean_nat_dec_le(x_145, x_145);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_145);
lean_dec_ref(x_127);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_is_scalar(x_143)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_143;
}
lean_ctor_set(x_150, 0, x_146);
lean_ctor_set(x_150, 1, x_142);
return x_150;
}
else
{
size_t x_151; size_t x_152; lean_object* x_153; 
lean_dec(x_143);
x_151 = 0;
x_152 = lean_usize_of_nat(x_145);
lean_dec(x_145);
x_153 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_addAnswer_spec__0(x_11, x_127, x_151, x_152, x_146, x_3, x_4, x_5, x_6, x_7, x_8, x_142);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_127);
return x_153;
}
}
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_193 = lean_ctor_get(x_13, 0);
x_194 = lean_ctor_get(x_13, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_13);
x_195 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_193, 1);
lean_inc_ref(x_196);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_197 = x_193;
} else {
 lean_dec_ref(x_193);
 x_197 = lean_box(0);
}
x_198 = l_Lean_Meta_SynthInstance_isNewAnswer(x_196, x_11);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_194);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint64_t x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; uint64_t x_237; size_t x_238; size_t x_239; size_t x_240; size_t x_241; size_t x_242; lean_object* x_243; uint8_t x_244; 
x_201 = lean_st_ref_take(x_4, x_194);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec_ref(x_201);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_202, 2);
lean_inc_ref(x_206);
x_207 = lean_ctor_get(x_202, 3);
lean_inc_ref(x_207);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 lean_ctor_release(x_202, 3);
 x_208 = x_202;
} else {
 lean_dec_ref(x_202);
 x_208 = lean_box(0);
}
x_225 = lean_ctor_get(x_207, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_207, 1);
lean_inc_ref(x_226);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_227 = x_207;
} else {
 lean_dec_ref(x_207);
 x_227 = lean_box(0);
}
lean_inc(x_11);
x_228 = lean_array_push(x_196, x_11);
lean_inc_ref(x_195);
if (lean_is_scalar(x_197)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_197;
}
lean_ctor_set(x_229, 0, x_195);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_array_get_size(x_226);
x_231 = l_Lean_Expr_hash(x_2);
x_232 = 32;
x_233 = lean_uint64_shift_right(x_231, x_232);
x_234 = lean_uint64_xor(x_231, x_233);
x_235 = 16;
x_236 = lean_uint64_shift_right(x_234, x_235);
x_237 = lean_uint64_xor(x_234, x_236);
x_238 = lean_uint64_to_usize(x_237);
x_239 = lean_usize_of_nat(x_230);
lean_dec(x_230);
x_240 = 1;
x_241 = lean_usize_sub(x_239, x_240);
x_242 = lean_usize_land(x_238, x_241);
x_243 = lean_array_uget(x_226, x_242);
x_244 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_2, x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_245 = lean_unsigned_to_nat(1u);
x_246 = lean_nat_add(x_225, x_245);
lean_dec(x_225);
x_247 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_247, 0, x_2);
lean_ctor_set(x_247, 1, x_229);
lean_ctor_set(x_247, 2, x_243);
x_248 = lean_array_uset(x_226, x_242, x_247);
x_249 = lean_unsigned_to_nat(4u);
x_250 = lean_nat_mul(x_246, x_249);
x_251 = lean_unsigned_to_nat(3u);
x_252 = lean_nat_div(x_250, x_251);
lean_dec(x_250);
x_253 = lean_array_get_size(x_248);
x_254 = lean_nat_dec_le(x_252, x_253);
lean_dec(x_253);
lean_dec(x_252);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_248);
if (lean_is_scalar(x_227)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_227;
}
lean_ctor_set(x_256, 0, x_246);
lean_ctor_set(x_256, 1, x_255);
x_209 = x_256;
goto block_224;
}
else
{
lean_object* x_257; 
if (lean_is_scalar(x_227)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_227;
}
lean_ctor_set(x_257, 0, x_246);
lean_ctor_set(x_257, 1, x_248);
x_209 = x_257;
goto block_224;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_box(0);
x_259 = lean_array_uset(x_226, x_242, x_258);
x_260 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_2, x_229, x_243);
x_261 = lean_array_uset(x_259, x_242, x_260);
if (lean_is_scalar(x_227)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_227;
}
lean_ctor_set(x_262, 0, x_225);
lean_ctor_set(x_262, 1, x_261);
x_209 = x_262;
goto block_224;
}
block_224:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(0, 4, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_204);
lean_ctor_set(x_210, 1, x_205);
lean_ctor_set(x_210, 2, x_206);
lean_ctor_set(x_210, 3, x_209);
x_211 = lean_st_ref_set(x_4, x_210, x_203);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_213 = x_211;
} else {
 lean_dec_ref(x_211);
 x_213 = lean_box(0);
}
x_214 = lean_unsigned_to_nat(0u);
x_215 = lean_array_get_size(x_195);
x_216 = lean_box(0);
x_217 = lean_nat_dec_lt(x_214, x_215);
if (x_217 == 0)
{
lean_object* x_218; 
lean_dec(x_215);
lean_dec_ref(x_195);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_is_scalar(x_213)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_213;
}
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_212);
return x_218;
}
else
{
uint8_t x_219; 
x_219 = lean_nat_dec_le(x_215, x_215);
if (x_219 == 0)
{
lean_object* x_220; 
lean_dec(x_215);
lean_dec_ref(x_195);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_is_scalar(x_213)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_213;
}
lean_ctor_set(x_220, 0, x_216);
lean_ctor_set(x_220, 1, x_212);
return x_220;
}
else
{
size_t x_221; size_t x_222; lean_object* x_223; 
lean_dec(x_213);
x_221 = 0;
x_222 = lean_usize_of_nat(x_215);
lean_dec(x_215);
x_223 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_addAnswer_spec__0(x_11, x_195, x_221, x_222, x_216, x_3, x_4, x_5, x_6, x_7, x_8, x_212);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_195);
return x_223;
}
}
}
}
}
}
else
{
uint8_t x_263; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_263 = !lean_is_exclusive(x_13);
if (x_263 == 0)
{
return x_13;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_13, 0);
x_265 = lean_ctor_get(x_13, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_13);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_267 = !lean_is_exclusive(x_10);
if (x_267 == 0)
{
return x_10;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_10, 0);
x_269 = lean_ctor_get(x_10, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_10);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("✅️", 6, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__2;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_infer_type(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_11, x_6, x_12);
lean_dec(x_6);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_17 = l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__3;
x_18 = l_Lean_MessageData_ofExpr(x_15);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_24 = l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__3;
x_25 = l_Lean_MessageData_ofExpr(x_21);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("answer", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__0;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("❌️", 6, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__3;
x_2 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(size: ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ≥ ", 5, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_nat_dec_le(x_12, x_1);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_1);
x_14 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__1;
x_15 = 1;
x_16 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_17 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg(x_14, x_2, x_3, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_5, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_5, 0);
lean_dec(x_20);
x_21 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__1;
x_22 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg(x_21, x_9, x_11);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec_ref(x_22);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_32 = lean_infer_type(x_4, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_33, x_8, x_34);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_40 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__5;
x_41 = l_Lean_MessageData_ofExpr(x_37);
lean_ctor_set_tag(x_35, 7);
lean_ctor_set(x_35, 1, x_41);
lean_ctor_set(x_35, 0, x_40);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_39);
lean_ctor_set(x_5, 0, x_35);
x_42 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__6;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__8;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Nat_reprFast(x_1);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_MessageData_ofFormat(x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__10;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Nat_reprFast(x_12);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__12;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg(x_21, x_57, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_59 = lean_ctor_get(x_35, 0);
x_60 = lean_ctor_get(x_35, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_35);
x_61 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_62 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__5;
x_63 = l_Lean_MessageData_ofExpr(x_59);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_61);
lean_ctor_set(x_5, 0, x_64);
x_65 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__6;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_5);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__8;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Nat_reprFast(x_1);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_MessageData_ofFormat(x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__10;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Nat_reprFast(x_12);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_MessageData_ofFormat(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__12;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg(x_21, x_80, x_7, x_8, x_9, x_10, x_60);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_32);
if (x_82 == 0)
{
return x_32;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_32, 0);
x_84 = lean_ctor_get(x_32, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_32);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_5);
x_86 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__1;
x_87 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg(x_86, x_9, x_11);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
x_92 = lean_box(0);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec_ref(x_87);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_95 = lean_infer_type(x_4, x_7, x_8, x_9, x_10, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_96, x_8, x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
x_102 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_103 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__5;
x_104 = l_Lean_MessageData_ofExpr(x_99);
if (lean_is_scalar(x_101)) {
 x_105 = lean_alloc_ctor(7, 2, 0);
} else {
 x_105 = x_101;
 lean_ctor_set_tag(x_105, 7);
}
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_102);
x_107 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__6;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__8;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Nat_reprFast(x_1);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_MessageData_ofFormat(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__10;
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Nat_reprFast(x_12);
x_118 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = l_Lean_MessageData_ofFormat(x_118);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__12;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg(x_86, x_122, x_7, x_8, x_9, x_10, x_100);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_124 = lean_ctor_get(x_95, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_95, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_126 = x_95;
} else {
 lean_dec_ref(x_95);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_addAnswer___lam__0), 9, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_10);
lean_inc_ref(x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_addAnswer___lam__1___boxed), 9, 1);
lean_closure_set(x_14, 0, x_9);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_addAnswer___lam__2), 11, 4);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_13);
lean_closure_set(x_15, 3, x_9);
x_16 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_11, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_addAnswer_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_addAnswer_spec__0(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_addAnswer___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_hasUnusedArguments(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_expr_has_loose_bvar(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
x_1 = x_2;
goto _start;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_hasUnusedArguments___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_hasUnusedArguments(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_13 = lean_infer_type(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_1, x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_free_object(x_13);
x_2 = x_12;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_19 = lean_box(x_17);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_1, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
x_2 = x_12;
x_7 = x_21;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_24 = lean_box(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = 1;
x_13 = lean_usize_sub(x_3, x_12);
x_14 = lean_array_uget(x_2, x_13);
x_15 = l_Lean_Expr_fvarId_x21(x_14);
x_16 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_15, x_1);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_17 = l_List_anyM___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__0(x_15, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_14);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec_ref(x_17);
x_3 = x_13;
x_10 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec_ref(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_5);
x_3 = x_13;
x_5 = x_23;
x_10 = x_22;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec_ref(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_5);
x_3 = x_13;
x_5 = x_29;
goto _start;
}
}
else
{
lean_object* x_31; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = 1;
x_13 = lean_usize_sub(x_3, x_12);
x_14 = lean_array_uget(x_2, x_13);
x_15 = l_Lean_Expr_fvarId_x21(x_14);
x_16 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_15, x_1);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_17 = l_List_anyM___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__0(x_15, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_14);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1_spec__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec_ref(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_5);
x_24 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1_spec__1(x_1, x_2, x_13, x_4, x_23, x_6, x_7, x_8, x_9, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec_ref(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_5);
x_30 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1_spec__1(x_1, x_2, x_13, x_4, x_29, x_6, x_7, x_8, x_9, x_10);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unusedArgs", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__1;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nhas unused arguments, reduced type", 35, 35);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nTransformer", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_8);
x_14 = l_Lean_mkAppN(x_8, x_1);
x_15 = l_Lean_Meta_mkLambdaFVars(x_2, x_14, x_3, x_4, x_4, x_4, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__0;
x_19 = lean_array_push(x_18, x_8);
x_20 = l_Lean_Meta_mkLambdaFVars(x_19, x_16, x_3, x_4, x_4, x_4, x_5, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
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
x_29 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__2;
x_30 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_29, x_11, x_22);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec_ref(x_7);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec_ref(x_30);
x_24 = x_33;
goto block_28;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_30, 1);
x_36 = lean_ctor_get(x_30, 0);
lean_dec(x_36);
x_37 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_38 = l_Lean_MessageData_ofExpr(x_7);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_38);
lean_ctor_set(x_30, 0, x_37);
x_39 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__4;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_39);
lean_inc_ref(x_6);
x_41 = l_Lean_indentExpr(x_6);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__6;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_21);
x_45 = l_Lean_indentExpr(x_21);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_37);
x_48 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_29, x_47, x_9, x_10, x_11, x_12, x_35);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
x_24 = x_49;
goto block_28;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_dec(x_30);
x_51 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_52 = l_Lean_MessageData_ofExpr(x_7);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__4;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_inc_ref(x_6);
x_56 = l_Lean_indentExpr(x_6);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__6;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_inc(x_21);
x_60 = l_Lean_indentExpr(x_21);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_51);
x_63 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_29, x_62, x_9, x_10, x_11, x_12, x_50);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_24 = x_64;
goto block_28;
}
}
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_21);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_23)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_23;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_65; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_65 = !lean_is_exclusive(x_20);
if (x_65 == 0)
{
return x_20;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_20, 0);
x_67 = lean_ctor_get(x_20, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_20);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_69 = !lean_is_exclusive(x_15);
if (x_69 == 0)
{
return x_15;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_15, 0);
x_71 = lean_ctor_get(x_15, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_15);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("redf", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_box(0);
x_30 = lean_array_get_size(x_4);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_lt(x_31, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
x_11 = x_29;
x_12 = x_10;
goto block_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_34 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_35 = l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1(x_5, x_4, x_33, x_34, x_29, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_11 = x_36;
x_12 = x_37;
goto block_28;
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
block_28:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_array_mk(x_11);
x_14 = 1;
lean_inc_ref(x_13);
x_15 = l_Lean_Meta_mkForallFVars(x_13, x_5, x_1, x_2, x_2, x_14, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_box(x_1);
x_19 = lean_box(x_2);
x_20 = lean_box(x_14);
lean_inc(x_16);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___boxed), 13, 7);
lean_closure_set(x_21, 0, x_13);
lean_closure_set(x_21, 1, x_4);
lean_closure_set(x_21, 2, x_18);
lean_closure_set(x_21, 3, x_19);
lean_closure_set(x_21, 4, x_20);
lean_closure_set(x_21, 5, x_16);
lean_closure_set(x_21, 6, x_3);
x_22 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___closed__1;
x_23 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___redArg(x_22, x_16, x_21, x_6, x_7, x_8, x_9, x_17);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec_ref(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_8, x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_hasUnusedArguments(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_10);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_box(x_14);
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___boxed), 10, 3);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_12);
x_20 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_12, x_19, x_16, x_2, x_3, x_4, x_5, x_13);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_hasUnusedArguments(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_box(x_23);
lean_inc(x_21);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___boxed), 10, 3);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_28);
lean_closure_set(x_29, 2, x_21);
x_30 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_21, x_29, x_26, x_2, x_3, x_4, x_5, x_22);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__2), 6, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_anyM___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox(x_4);
x_16 = lean_unbox(x_5);
x_17 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0(x_1, x_2, x_14, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_2);
x_13 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_SynthInstance_consume_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 7);
lean_inc_ref(x_9);
lean_dec_ref(x_6);
x_10 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isDelayedAssigned___at___Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(x_9, x_1);
x_11 = lean_box(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_6, 7);
lean_inc_ref(x_13);
lean_dec_ref(x_6);
x_14 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isDelayedAssigned___at___Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(x_13, x_1);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_SynthInstance_consume_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_isAssigned___at___Lean_Meta_SynthInstance_consume_spec__0___redArg(x_1, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___Lean_Meta_SynthInstance_consume_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_13 = x_1;
} else {
 lean_dec_ref(x_1);
 x_13 = lean_box(0);
}
x_18 = l_Lean_Expr_mvarId_x21(x_11);
x_19 = l_Lean_MVarId_isAssigned___at___Lean_Meta_SynthInstance_consume_spec__0___redArg(x_18, x_6, x_9);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec_ref(x_19);
x_14 = x_22;
goto block_17;
}
else
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec_ref(x_19);
x_1 = x_12;
x_9 = x_23;
goto _start;
}
block_17:
{
lean_object* x_15; 
if (lean_is_scalar(x_13)) {
 x_15 = lean_alloc_ctor(1, 2, 0);
} else {
 x_15 = x_13;
}
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_2);
x_1 = x_12;
x_2 = x_15;
x_9 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_13 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_1, x_9, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__0;
x_17 = lean_array_push(x_16, x_14);
x_18 = 0;
x_19 = l_Lean_Expr_betaRev(x_2, x_17, x_18, x_18);
lean_dec_ref(x_17);
lean_inc_ref(x_19);
x_20 = lean_infer_type(x_19, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_23, 2, x_19);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_19);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec_ref(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_array_uget(x_5, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_20);
lean_dec_ref(x_16);
lean_inc_ref(x_1);
x_21 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2___lam__0___boxed), 12, 5);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_18);
lean_closure_set(x_21, 3, x_19);
lean_closure_set(x_21, 4, x_17);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_22 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_2, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_uset(x_5, x_4, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_4, x_27);
x_29 = lean_array_uset(x_26, x_4, x_23);
x_4 = x_28;
x_5 = x_29;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_consume_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_array_push(x_5, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_9;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_List_filterAuxM___at___Lean_Meta_SynthInstance_consume_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_List_reverse___redArg(x_12);
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
x_16 = l_List_reverse___redArg(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_st_ref_get(x_7, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec(x_17);
lean_ctor_set(x_11, 1, x_13);
lean_ctor_set(x_11, 0, x_18);
lean_ctor_set(x_15, 0, x_11);
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
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
lean_ctor_set(x_11, 1, x_13);
lean_ctor_set(x_11, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_st_ref_get(x_7, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_box(0);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_consume___lam__0___boxed), 9, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_15);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_12);
x_17 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_12, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_inc(x_14);
lean_inc(x_18);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_ctor_set(x_1, 3, x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; 
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_20 = l_Lean_Meta_SynthInstance_addAnswer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_21);
lean_inc_ref(x_12);
x_22 = l_Lean_Meta_SynthInstance_mkTableKeyFor(x_12, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_Lean_Meta_SynthInstance_findEntry_x3f___redArg(x_23, x_3, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
lean_inc_ref(x_1);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_29; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_21);
lean_inc_ref(x_12);
x_29 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f(x_12, x_21, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_1);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = l_Lean_Meta_SynthInstance_newSubgoal(x_12, x_23, x_21, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_23);
lean_dec(x_21);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec_ref(x_29);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
lean_inc(x_36);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1___boxed), 8, 1);
lean_closure_set(x_38, 0, x_36);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_12);
x_39 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_12, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Lean_Meta_SynthInstance_findEntry_x3f___redArg(x_40, x_3, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_37);
lean_dec_ref(x_28);
lean_dec_ref(x_1);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
lean_ctor_set(x_30, 0, x_36);
x_45 = 0;
x_46 = lean_box(0);
x_47 = lean_box(x_45);
x_48 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_consume___lam__1___boxed), 10, 3);
lean_closure_set(x_48, 0, x_30);
lean_closure_set(x_48, 1, x_47);
lean_closure_set(x_48, 2, x_46);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_49 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_12, x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_44);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 1, x_18);
lean_ctor_set(x_50, 0, x_54);
lean_inc(x_53);
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_11);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_50);
lean_ctor_set(x_55, 4, x_14);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_Meta_SynthInstance_newSubgoal(x_53, x_40, x_54, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_51);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_50, 0);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
lean_inc(x_59);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_18);
lean_inc(x_58);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_10);
lean_ctor_set(x_61, 1, x_11);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_14);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Lean_Meta_SynthInstance_newSubgoal(x_58, x_40, x_59, x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_51);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_40);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_64 = !lean_is_exclusive(x_49);
if (x_64 == 0)
{
return x_49;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_49, 0);
x_66 = lean_ctor_get(x_49, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_49);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; 
lean_dec(x_36);
lean_free_object(x_30);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_68 = lean_ctor_get(x_43, 0);
lean_inc(x_68);
lean_dec(x_43);
x_69 = lean_ctor_get(x_42, 1);
lean_inc(x_69);
lean_dec_ref(x_42);
x_70 = lean_ctor_get(x_68, 0);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc_ref(x_71);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_72 = x_68;
} else {
 lean_dec_ref(x_68);
 x_72 = lean_box(0);
}
x_73 = lean_array_size(x_71);
x_74 = 0;
lean_inc(x_3);
lean_inc_ref(x_71);
x_75 = l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2(x_37, x_12, x_73, x_74, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_69);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_96; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_st_ref_take(x_3, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_79, 2);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_79, 3);
lean_inc_ref(x_84);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 lean_ctor_release(x_79, 3);
 x_85 = x_79;
} else {
 lean_dec_ref(x_79);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_array_get_size(x_76);
x_172 = lean_nat_dec_lt(x_170, x_171);
if (x_172 == 0)
{
lean_dec(x_171);
lean_dec(x_76);
lean_dec_ref(x_1);
x_96 = x_83;
goto block_169;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_171, x_171);
if (x_173 == 0)
{
lean_dec(x_171);
lean_dec(x_76);
lean_dec_ref(x_1);
x_96 = x_83;
goto block_169;
}
else
{
size_t x_174; lean_object* x_175; 
x_174 = lean_usize_of_nat(x_171);
lean_dec(x_171);
x_175 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_consume_spec__3(x_1, x_76, x_74, x_174, x_83);
lean_dec(x_76);
x_96 = x_175;
goto block_169;
}
}
block_95:
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(0, 4, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_82);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_st_ref_set(x_3, x_89, x_80);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
lean_ctor_set(x_90, 0, x_86);
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_86);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
block_169:
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_84);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; size_t x_110; size_t x_111; size_t x_112; size_t x_113; size_t x_114; lean_object* x_115; uint8_t x_116; 
x_98 = lean_ctor_get(x_84, 0);
x_99 = lean_ctor_get(x_84, 1);
x_100 = lean_array_push(x_70, x_28);
if (lean_is_scalar(x_72)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_72;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_71);
x_102 = lean_array_get_size(x_99);
x_103 = l_Lean_Expr_hash(x_40);
x_104 = 32;
x_105 = lean_uint64_shift_right(x_103, x_104);
x_106 = lean_uint64_xor(x_103, x_105);
x_107 = 16;
x_108 = lean_uint64_shift_right(x_106, x_107);
x_109 = lean_uint64_xor(x_106, x_108);
x_110 = lean_uint64_to_usize(x_109);
x_111 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_112 = 1;
x_113 = lean_usize_sub(x_111, x_112);
x_114 = lean_usize_land(x_110, x_113);
x_115 = lean_array_uget(x_99, x_114);
x_116 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_40, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_nat_add(x_98, x_117);
lean_dec(x_98);
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_40);
lean_ctor_set(x_119, 1, x_101);
lean_ctor_set(x_119, 2, x_115);
x_120 = lean_array_uset(x_99, x_114, x_119);
x_121 = lean_unsigned_to_nat(4u);
x_122 = lean_nat_mul(x_118, x_121);
x_123 = lean_unsigned_to_nat(3u);
x_124 = lean_nat_div(x_122, x_123);
lean_dec(x_122);
x_125 = lean_array_get_size(x_120);
x_126 = lean_nat_dec_le(x_124, x_125);
lean_dec(x_125);
lean_dec(x_124);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_120);
lean_ctor_set(x_84, 1, x_127);
lean_ctor_set(x_84, 0, x_118);
x_87 = x_96;
x_88 = x_84;
goto block_95;
}
else
{
lean_ctor_set(x_84, 1, x_120);
lean_ctor_set(x_84, 0, x_118);
x_87 = x_96;
x_88 = x_84;
goto block_95;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_box(0);
x_129 = lean_array_uset(x_99, x_114, x_128);
x_130 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_40, x_101, x_115);
x_131 = lean_array_uset(x_129, x_114, x_130);
lean_ctor_set(x_84, 1, x_131);
x_87 = x_96;
x_88 = x_84;
goto block_95;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint64_t x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; uint64_t x_141; uint64_t x_142; uint64_t x_143; size_t x_144; size_t x_145; size_t x_146; size_t x_147; size_t x_148; lean_object* x_149; uint8_t x_150; 
x_132 = lean_ctor_get(x_84, 0);
x_133 = lean_ctor_get(x_84, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_84);
x_134 = lean_array_push(x_70, x_28);
if (lean_is_scalar(x_72)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_72;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_71);
x_136 = lean_array_get_size(x_133);
x_137 = l_Lean_Expr_hash(x_40);
x_138 = 32;
x_139 = lean_uint64_shift_right(x_137, x_138);
x_140 = lean_uint64_xor(x_137, x_139);
x_141 = 16;
x_142 = lean_uint64_shift_right(x_140, x_141);
x_143 = lean_uint64_xor(x_140, x_142);
x_144 = lean_uint64_to_usize(x_143);
x_145 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_146 = 1;
x_147 = lean_usize_sub(x_145, x_146);
x_148 = lean_usize_land(x_144, x_147);
x_149 = lean_array_uget(x_133, x_148);
x_150 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_40, x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_nat_add(x_132, x_151);
lean_dec(x_132);
x_153 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_153, 0, x_40);
lean_ctor_set(x_153, 1, x_135);
lean_ctor_set(x_153, 2, x_149);
x_154 = lean_array_uset(x_133, x_148, x_153);
x_155 = lean_unsigned_to_nat(4u);
x_156 = lean_nat_mul(x_152, x_155);
x_157 = lean_unsigned_to_nat(3u);
x_158 = lean_nat_div(x_156, x_157);
lean_dec(x_156);
x_159 = lean_array_get_size(x_154);
x_160 = lean_nat_dec_le(x_158, x_159);
lean_dec(x_159);
lean_dec(x_158);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_154);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_152);
lean_ctor_set(x_162, 1, x_161);
x_87 = x_96;
x_88 = x_162;
goto block_95;
}
else
{
lean_object* x_163; 
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_152);
lean_ctor_set(x_163, 1, x_154);
x_87 = x_96;
x_88 = x_163;
goto block_95;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_box(0);
x_165 = lean_array_uset(x_133, x_148, x_164);
x_166 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_40, x_135, x_149);
x_167 = lean_array_uset(x_165, x_148, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_132);
lean_ctor_set(x_168, 1, x_167);
x_87 = x_96;
x_88 = x_168;
goto block_95;
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_40);
lean_dec_ref(x_28);
lean_dec_ref(x_1);
lean_dec(x_3);
x_176 = !lean_is_exclusive(x_75);
if (x_176 == 0)
{
return x_75;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_75, 0);
x_178 = lean_ctor_get(x_75, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_75);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_37);
lean_dec(x_36);
lean_free_object(x_30);
lean_dec_ref(x_28);
lean_dec_ref(x_1);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_180 = !lean_is_exclusive(x_39);
if (x_180 == 0)
{
return x_39;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_39, 0);
x_182 = lean_ctor_get(x_39, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_39);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_184 = lean_ctor_get(x_30, 0);
lean_inc(x_184);
lean_dec(x_30);
x_185 = lean_ctor_get(x_29, 1);
lean_inc(x_185);
lean_dec_ref(x_29);
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
lean_dec(x_184);
lean_inc(x_186);
x_188 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1___boxed), 8, 1);
lean_closure_set(x_188, 0, x_186);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_12);
x_189 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_12, x_188, x_2, x_3, x_4, x_5, x_6, x_7, x_185);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec_ref(x_189);
x_192 = l_Lean_Meta_SynthInstance_findEntry_x3f___redArg(x_190, x_3, x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_187);
lean_dec_ref(x_28);
lean_dec_ref(x_1);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec_ref(x_192);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_186);
x_196 = 0;
x_197 = lean_box(0);
x_198 = lean_box(x_196);
x_199 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_consume___lam__1___boxed), 10, 3);
lean_closure_set(x_199, 0, x_195);
lean_closure_set(x_199, 1, x_198);
lean_closure_set(x_199, 2, x_197);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_200 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_12, x_199, x_2, x_3, x_4, x_5, x_6, x_7, x_194);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec_ref(x_200);
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_205 = x_201;
} else {
 lean_dec_ref(x_201);
 x_205 = lean_box(0);
}
lean_inc(x_204);
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
 lean_ctor_set_tag(x_206, 1);
}
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_18);
lean_inc(x_203);
x_207 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_207, 0, x_10);
lean_ctor_set(x_207, 1, x_11);
lean_ctor_set(x_207, 2, x_203);
lean_ctor_set(x_207, 3, x_206);
lean_ctor_set(x_207, 4, x_14);
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_209 = l_Lean_Meta_SynthInstance_newSubgoal(x_203, x_190, x_204, x_208, x_2, x_3, x_4, x_5, x_6, x_7, x_202);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_190);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_210 = lean_ctor_get(x_200, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_200, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_212 = x_200;
} else {
 lean_dec_ref(x_200);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; size_t x_219; size_t x_220; lean_object* x_221; 
lean_dec(x_186);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_214 = lean_ctor_get(x_193, 0);
lean_inc(x_214);
lean_dec(x_193);
x_215 = lean_ctor_get(x_192, 1);
lean_inc(x_215);
lean_dec_ref(x_192);
x_216 = lean_ctor_get(x_214, 0);
lean_inc_ref(x_216);
x_217 = lean_ctor_get(x_214, 1);
lean_inc_ref(x_217);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_218 = x_214;
} else {
 lean_dec_ref(x_214);
 x_218 = lean_box(0);
}
x_219 = lean_array_size(x_217);
x_220 = 0;
lean_inc(x_3);
lean_inc_ref(x_217);
x_221 = l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2(x_187, x_12, x_219, x_220, x_217, x_2, x_3, x_4, x_5, x_6, x_7, x_215);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_241; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec_ref(x_221);
x_224 = lean_st_ref_take(x_3, x_223);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec_ref(x_224);
x_227 = lean_ctor_get(x_225, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_225, 1);
lean_inc_ref(x_228);
x_229 = lean_ctor_get(x_225, 2);
lean_inc_ref(x_229);
x_230 = lean_ctor_get(x_225, 3);
lean_inc_ref(x_230);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 lean_ctor_release(x_225, 2);
 lean_ctor_release(x_225, 3);
 x_231 = x_225;
} else {
 lean_dec_ref(x_225);
 x_231 = lean_box(0);
}
x_232 = lean_box(0);
x_281 = lean_unsigned_to_nat(0u);
x_282 = lean_array_get_size(x_222);
x_283 = lean_nat_dec_lt(x_281, x_282);
if (x_283 == 0)
{
lean_dec(x_282);
lean_dec(x_222);
lean_dec_ref(x_1);
x_241 = x_229;
goto block_280;
}
else
{
uint8_t x_284; 
x_284 = lean_nat_dec_le(x_282, x_282);
if (x_284 == 0)
{
lean_dec(x_282);
lean_dec(x_222);
lean_dec_ref(x_1);
x_241 = x_229;
goto block_280;
}
else
{
size_t x_285; lean_object* x_286; 
x_285 = lean_usize_of_nat(x_282);
lean_dec(x_282);
x_286 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_consume_spec__3(x_1, x_222, x_220, x_285, x_229);
lean_dec(x_222);
x_241 = x_286;
goto block_280;
}
}
block_240:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
if (lean_is_scalar(x_231)) {
 x_235 = lean_alloc_ctor(0, 4, 0);
} else {
 x_235 = x_231;
}
lean_ctor_set(x_235, 0, x_227);
lean_ctor_set(x_235, 1, x_228);
lean_ctor_set(x_235, 2, x_233);
lean_ctor_set(x_235, 3, x_234);
x_236 = lean_st_ref_set(x_3, x_235, x_226);
lean_dec(x_3);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_232);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
block_280:
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint64_t x_248; uint64_t x_249; uint64_t x_250; uint64_t x_251; uint64_t x_252; uint64_t x_253; uint64_t x_254; size_t x_255; size_t x_256; size_t x_257; size_t x_258; size_t x_259; lean_object* x_260; uint8_t x_261; 
x_242 = lean_ctor_get(x_230, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_230, 1);
lean_inc_ref(x_243);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_244 = x_230;
} else {
 lean_dec_ref(x_230);
 x_244 = lean_box(0);
}
x_245 = lean_array_push(x_216, x_28);
if (lean_is_scalar(x_218)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_218;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_217);
x_247 = lean_array_get_size(x_243);
x_248 = l_Lean_Expr_hash(x_190);
x_249 = 32;
x_250 = lean_uint64_shift_right(x_248, x_249);
x_251 = lean_uint64_xor(x_248, x_250);
x_252 = 16;
x_253 = lean_uint64_shift_right(x_251, x_252);
x_254 = lean_uint64_xor(x_251, x_253);
x_255 = lean_uint64_to_usize(x_254);
x_256 = lean_usize_of_nat(x_247);
lean_dec(x_247);
x_257 = 1;
x_258 = lean_usize_sub(x_256, x_257);
x_259 = lean_usize_land(x_255, x_258);
x_260 = lean_array_uget(x_243, x_259);
x_261 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_190, x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_262 = lean_unsigned_to_nat(1u);
x_263 = lean_nat_add(x_242, x_262);
lean_dec(x_242);
x_264 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_264, 0, x_190);
lean_ctor_set(x_264, 1, x_246);
lean_ctor_set(x_264, 2, x_260);
x_265 = lean_array_uset(x_243, x_259, x_264);
x_266 = lean_unsigned_to_nat(4u);
x_267 = lean_nat_mul(x_263, x_266);
x_268 = lean_unsigned_to_nat(3u);
x_269 = lean_nat_div(x_267, x_268);
lean_dec(x_267);
x_270 = lean_array_get_size(x_265);
x_271 = lean_nat_dec_le(x_269, x_270);
lean_dec(x_270);
lean_dec(x_269);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; 
x_272 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_265);
if (lean_is_scalar(x_244)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_244;
}
lean_ctor_set(x_273, 0, x_263);
lean_ctor_set(x_273, 1, x_272);
x_233 = x_241;
x_234 = x_273;
goto block_240;
}
else
{
lean_object* x_274; 
if (lean_is_scalar(x_244)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_244;
}
lean_ctor_set(x_274, 0, x_263);
lean_ctor_set(x_274, 1, x_265);
x_233 = x_241;
x_234 = x_274;
goto block_240;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_275 = lean_box(0);
x_276 = lean_array_uset(x_243, x_259, x_275);
x_277 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_190, x_246, x_260);
x_278 = lean_array_uset(x_276, x_259, x_277);
if (lean_is_scalar(x_244)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_244;
}
lean_ctor_set(x_279, 0, x_242);
lean_ctor_set(x_279, 1, x_278);
x_233 = x_241;
x_234 = x_279;
goto block_240;
}
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec_ref(x_216);
lean_dec(x_190);
lean_dec_ref(x_28);
lean_dec_ref(x_1);
lean_dec(x_3);
x_287 = lean_ctor_get(x_221, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_221, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_289 = x_221;
} else {
 lean_dec_ref(x_221);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec_ref(x_28);
lean_dec_ref(x_1);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_291 = lean_ctor_get(x_189, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_189, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_293 = x_189;
} else {
 lean_dec_ref(x_189);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
}
}
else
{
uint8_t x_295; 
lean_dec_ref(x_28);
lean_dec(x_23);
lean_dec(x_21);
lean_dec_ref(x_1);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_295 = !lean_is_exclusive(x_29);
if (x_295 == 0)
{
return x_29;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_29, 0);
x_297 = lean_ctor_get(x_29, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_29);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_321; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_299 = lean_ctor_get(x_26, 0);
lean_inc(x_299);
lean_dec(x_26);
x_300 = lean_st_ref_take(x_3, x_27);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec_ref(x_300);
x_303 = lean_ctor_get(x_301, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_301, 1);
lean_inc_ref(x_304);
x_305 = lean_ctor_get(x_301, 2);
lean_inc_ref(x_305);
x_306 = lean_ctor_get(x_301, 3);
lean_inc_ref(x_306);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 lean_ctor_release(x_301, 2);
 lean_ctor_release(x_301, 3);
 x_307 = x_301;
} else {
 lean_dec_ref(x_301);
 x_307 = lean_box(0);
}
x_308 = lean_ctor_get(x_299, 0);
lean_inc_ref(x_308);
x_309 = lean_ctor_get(x_299, 1);
lean_inc_ref(x_309);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_310 = x_299;
} else {
 lean_dec_ref(x_299);
 x_310 = lean_box(0);
}
x_311 = lean_box(0);
x_395 = lean_unsigned_to_nat(0u);
x_396 = lean_array_get_size(x_309);
x_397 = lean_nat_dec_lt(x_395, x_396);
if (x_397 == 0)
{
lean_dec(x_396);
lean_dec_ref(x_1);
x_321 = x_305;
goto block_394;
}
else
{
uint8_t x_398; 
x_398 = lean_nat_dec_le(x_396, x_396);
if (x_398 == 0)
{
lean_dec(x_396);
lean_dec_ref(x_1);
x_321 = x_305;
goto block_394;
}
else
{
size_t x_399; size_t x_400; lean_object* x_401; 
x_399 = 0;
x_400 = lean_usize_of_nat(x_396);
lean_dec(x_396);
x_401 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_consume_spec__3(x_1, x_309, x_399, x_400, x_305);
x_321 = x_401;
goto block_394;
}
}
block_320:
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
if (lean_is_scalar(x_307)) {
 x_314 = lean_alloc_ctor(0, 4, 0);
} else {
 x_314 = x_307;
}
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_304);
lean_ctor_set(x_314, 2, x_312);
lean_ctor_set(x_314, 3, x_313);
x_315 = lean_st_ref_set(x_3, x_314, x_302);
lean_dec(x_3);
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
lean_object* x_317; 
x_317 = lean_ctor_get(x_315, 0);
lean_dec(x_317);
lean_ctor_set(x_315, 0, x_311);
return x_315;
}
else
{
lean_object* x_318; lean_object* x_319; 
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
lean_dec(x_315);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_311);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
block_394:
{
uint8_t x_322; 
x_322 = !lean_is_exclusive(x_306);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint64_t x_328; uint64_t x_329; uint64_t x_330; uint64_t x_331; uint64_t x_332; uint64_t x_333; uint64_t x_334; size_t x_335; size_t x_336; size_t x_337; size_t x_338; size_t x_339; lean_object* x_340; uint8_t x_341; 
x_323 = lean_ctor_get(x_306, 0);
x_324 = lean_ctor_get(x_306, 1);
x_325 = lean_array_push(x_308, x_28);
if (lean_is_scalar(x_310)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_310;
}
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_309);
x_327 = lean_array_get_size(x_324);
x_328 = l_Lean_Expr_hash(x_23);
x_329 = 32;
x_330 = lean_uint64_shift_right(x_328, x_329);
x_331 = lean_uint64_xor(x_328, x_330);
x_332 = 16;
x_333 = lean_uint64_shift_right(x_331, x_332);
x_334 = lean_uint64_xor(x_331, x_333);
x_335 = lean_uint64_to_usize(x_334);
x_336 = lean_usize_of_nat(x_327);
lean_dec(x_327);
x_337 = 1;
x_338 = lean_usize_sub(x_336, x_337);
x_339 = lean_usize_land(x_335, x_338);
x_340 = lean_array_uget(x_324, x_339);
x_341 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_23, x_340);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
x_342 = lean_unsigned_to_nat(1u);
x_343 = lean_nat_add(x_323, x_342);
lean_dec(x_323);
x_344 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_344, 0, x_23);
lean_ctor_set(x_344, 1, x_326);
lean_ctor_set(x_344, 2, x_340);
x_345 = lean_array_uset(x_324, x_339, x_344);
x_346 = lean_unsigned_to_nat(4u);
x_347 = lean_nat_mul(x_343, x_346);
x_348 = lean_unsigned_to_nat(3u);
x_349 = lean_nat_div(x_347, x_348);
lean_dec(x_347);
x_350 = lean_array_get_size(x_345);
x_351 = lean_nat_dec_le(x_349, x_350);
lean_dec(x_350);
lean_dec(x_349);
if (x_351 == 0)
{
lean_object* x_352; 
x_352 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_345);
lean_ctor_set(x_306, 1, x_352);
lean_ctor_set(x_306, 0, x_343);
x_312 = x_321;
x_313 = x_306;
goto block_320;
}
else
{
lean_ctor_set(x_306, 1, x_345);
lean_ctor_set(x_306, 0, x_343);
x_312 = x_321;
x_313 = x_306;
goto block_320;
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_353 = lean_box(0);
x_354 = lean_array_uset(x_324, x_339, x_353);
x_355 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_23, x_326, x_340);
x_356 = lean_array_uset(x_354, x_339, x_355);
lean_ctor_set(x_306, 1, x_356);
x_312 = x_321;
x_313 = x_306;
goto block_320;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint64_t x_362; uint64_t x_363; uint64_t x_364; uint64_t x_365; uint64_t x_366; uint64_t x_367; uint64_t x_368; size_t x_369; size_t x_370; size_t x_371; size_t x_372; size_t x_373; lean_object* x_374; uint8_t x_375; 
x_357 = lean_ctor_get(x_306, 0);
x_358 = lean_ctor_get(x_306, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_306);
x_359 = lean_array_push(x_308, x_28);
if (lean_is_scalar(x_310)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_310;
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_309);
x_361 = lean_array_get_size(x_358);
x_362 = l_Lean_Expr_hash(x_23);
x_363 = 32;
x_364 = lean_uint64_shift_right(x_362, x_363);
x_365 = lean_uint64_xor(x_362, x_364);
x_366 = 16;
x_367 = lean_uint64_shift_right(x_365, x_366);
x_368 = lean_uint64_xor(x_365, x_367);
x_369 = lean_uint64_to_usize(x_368);
x_370 = lean_usize_of_nat(x_361);
lean_dec(x_361);
x_371 = 1;
x_372 = lean_usize_sub(x_370, x_371);
x_373 = lean_usize_land(x_369, x_372);
x_374 = lean_array_uget(x_358, x_373);
x_375 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_23, x_374);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_376 = lean_unsigned_to_nat(1u);
x_377 = lean_nat_add(x_357, x_376);
lean_dec(x_357);
x_378 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_378, 0, x_23);
lean_ctor_set(x_378, 1, x_360);
lean_ctor_set(x_378, 2, x_374);
x_379 = lean_array_uset(x_358, x_373, x_378);
x_380 = lean_unsigned_to_nat(4u);
x_381 = lean_nat_mul(x_377, x_380);
x_382 = lean_unsigned_to_nat(3u);
x_383 = lean_nat_div(x_381, x_382);
lean_dec(x_381);
x_384 = lean_array_get_size(x_379);
x_385 = lean_nat_dec_le(x_383, x_384);
lean_dec(x_384);
lean_dec(x_383);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; 
x_386 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_379);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_377);
lean_ctor_set(x_387, 1, x_386);
x_312 = x_321;
x_313 = x_387;
goto block_320;
}
else
{
lean_object* x_388; 
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_377);
lean_ctor_set(x_388, 1, x_379);
x_312 = x_321;
x_313 = x_388;
goto block_320;
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_389 = lean_box(0);
x_390 = lean_array_uset(x_358, x_373, x_389);
x_391 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_23, x_360, x_374);
x_392 = lean_array_uset(x_390, x_373, x_391);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_357);
lean_ctor_set(x_393, 1, x_392);
x_312 = x_321;
x_313 = x_393;
goto block_320;
}
}
}
}
}
else
{
uint8_t x_402; 
lean_dec(x_21);
lean_dec_ref(x_1);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_402 = !lean_is_exclusive(x_22);
if (x_402 == 0)
{
return x_22;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_403 = lean_ctor_get(x_22, 0);
x_404 = lean_ctor_get(x_22, 1);
lean_inc(x_404);
lean_inc(x_403);
lean_dec(x_22);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
}
}
}
else
{
uint8_t x_406; 
lean_free_object(x_1);
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_406 = !lean_is_exclusive(x_17);
if (x_406 == 0)
{
return x_17;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_17, 0);
x_408 = lean_ctor_get(x_17, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_17);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
return x_409;
}
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_410 = lean_ctor_get(x_1, 0);
x_411 = lean_ctor_get(x_1, 1);
x_412 = lean_ctor_get(x_1, 2);
x_413 = lean_ctor_get(x_1, 3);
x_414 = lean_ctor_get(x_1, 4);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_1);
x_415 = lean_box(0);
x_416 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_consume___lam__0___boxed), 9, 2);
lean_closure_set(x_416, 0, x_413);
lean_closure_set(x_416, 1, x_415);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_412);
x_417 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_412, x_416, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec_ref(x_417);
lean_inc(x_414);
lean_inc(x_418);
lean_inc_ref(x_412);
lean_inc_ref(x_411);
lean_inc_ref(x_410);
x_420 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_420, 0, x_410);
lean_ctor_set(x_420, 1, x_411);
lean_ctor_set(x_420, 2, x_412);
lean_ctor_set(x_420, 3, x_418);
lean_ctor_set(x_420, 4, x_414);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_421; 
lean_dec(x_414);
lean_dec_ref(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
x_421 = l_Lean_Meta_SynthInstance_addAnswer(x_420, x_2, x_3, x_4, x_5, x_6, x_7, x_419);
return x_421;
}
else
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_ctor_get(x_418, 0);
lean_inc(x_422);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_422);
lean_inc_ref(x_412);
x_423 = l_Lean_Meta_SynthInstance_mkTableKeyFor(x_412, x_422, x_2, x_3, x_4, x_5, x_6, x_7, x_419);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec_ref(x_423);
x_426 = l_Lean_Meta_SynthInstance_findEntry_x3f___redArg(x_424, x_3, x_425);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec_ref(x_426);
lean_inc_ref(x_420);
x_429 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_429, 0, x_420);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_430; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_422);
lean_inc_ref(x_412);
x_430 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f(x_412, x_422, x_4, x_5, x_6, x_7, x_428);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; 
lean_dec_ref(x_420);
lean_dec(x_418);
lean_dec(x_414);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec_ref(x_430);
x_433 = l_Lean_Meta_SynthInstance_newSubgoal(x_412, x_424, x_422, x_429, x_2, x_3, x_4, x_5, x_6, x_7, x_432);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_424);
lean_dec(x_422);
x_434 = lean_ctor_get(x_431, 0);
lean_inc(x_434);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 x_435 = x_431;
} else {
 lean_dec_ref(x_431);
 x_435 = lean_box(0);
}
x_436 = lean_ctor_get(x_430, 1);
lean_inc(x_436);
lean_dec_ref(x_430);
x_437 = lean_ctor_get(x_434, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_434, 1);
lean_inc(x_438);
lean_dec(x_434);
lean_inc(x_437);
x_439 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__1___boxed), 8, 1);
lean_closure_set(x_439, 0, x_437);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_412);
x_440 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_412, x_439, x_2, x_3, x_4, x_5, x_6, x_7, x_436);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec_ref(x_440);
x_443 = l_Lean_Meta_SynthInstance_findEntry_x3f___redArg(x_441, x_3, x_442);
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_438);
lean_dec_ref(x_429);
lean_dec_ref(x_420);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec_ref(x_443);
if (lean_is_scalar(x_435)) {
 x_446 = lean_alloc_ctor(1, 1, 0);
} else {
 x_446 = x_435;
}
lean_ctor_set(x_446, 0, x_437);
x_447 = 0;
x_448 = lean_box(0);
x_449 = lean_box(x_447);
x_450 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_consume___lam__1___boxed), 10, 3);
lean_closure_set(x_450, 0, x_446);
lean_closure_set(x_450, 1, x_449);
lean_closure_set(x_450, 2, x_448);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_451 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_412, x_450, x_2, x_3, x_4, x_5, x_6, x_7, x_445);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec_ref(x_451);
x_454 = lean_ctor_get(x_452, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_452, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_456 = x_452;
} else {
 lean_dec_ref(x_452);
 x_456 = lean_box(0);
}
lean_inc(x_455);
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_457 = x_456;
 lean_ctor_set_tag(x_457, 1);
}
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_418);
lean_inc(x_454);
x_458 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_458, 0, x_410);
lean_ctor_set(x_458, 1, x_411);
lean_ctor_set(x_458, 2, x_454);
lean_ctor_set(x_458, 3, x_457);
lean_ctor_set(x_458, 4, x_414);
x_459 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_459, 0, x_458);
x_460 = l_Lean_Meta_SynthInstance_newSubgoal(x_454, x_441, x_455, x_459, x_2, x_3, x_4, x_5, x_6, x_7, x_453);
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_441);
lean_dec(x_418);
lean_dec(x_414);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_461 = lean_ctor_get(x_451, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_451, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_463 = x_451;
} else {
 lean_dec_ref(x_451);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 2, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_461);
lean_ctor_set(x_464, 1, x_462);
return x_464;
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; size_t x_470; size_t x_471; lean_object* x_472; 
lean_dec(x_437);
lean_dec(x_435);
lean_dec(x_418);
lean_dec(x_414);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
x_465 = lean_ctor_get(x_444, 0);
lean_inc(x_465);
lean_dec(x_444);
x_466 = lean_ctor_get(x_443, 1);
lean_inc(x_466);
lean_dec_ref(x_443);
x_467 = lean_ctor_get(x_465, 0);
lean_inc_ref(x_467);
x_468 = lean_ctor_get(x_465, 1);
lean_inc_ref(x_468);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_469 = x_465;
} else {
 lean_dec_ref(x_465);
 x_469 = lean_box(0);
}
x_470 = lean_array_size(x_468);
x_471 = 0;
lean_inc(x_3);
lean_inc_ref(x_468);
x_472 = l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2(x_438, x_412, x_470, x_471, x_468, x_2, x_3, x_4, x_5, x_6, x_7, x_466);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_492; lean_object* x_532; lean_object* x_533; uint8_t x_534; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec_ref(x_472);
x_475 = lean_st_ref_take(x_3, x_474);
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec_ref(x_475);
x_478 = lean_ctor_get(x_476, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_476, 1);
lean_inc_ref(x_479);
x_480 = lean_ctor_get(x_476, 2);
lean_inc_ref(x_480);
x_481 = lean_ctor_get(x_476, 3);
lean_inc_ref(x_481);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_482 = x_476;
} else {
 lean_dec_ref(x_476);
 x_482 = lean_box(0);
}
x_483 = lean_box(0);
x_532 = lean_unsigned_to_nat(0u);
x_533 = lean_array_get_size(x_473);
x_534 = lean_nat_dec_lt(x_532, x_533);
if (x_534 == 0)
{
lean_dec(x_533);
lean_dec(x_473);
lean_dec_ref(x_420);
x_492 = x_480;
goto block_531;
}
else
{
uint8_t x_535; 
x_535 = lean_nat_dec_le(x_533, x_533);
if (x_535 == 0)
{
lean_dec(x_533);
lean_dec(x_473);
lean_dec_ref(x_420);
x_492 = x_480;
goto block_531;
}
else
{
size_t x_536; lean_object* x_537; 
x_536 = lean_usize_of_nat(x_533);
lean_dec(x_533);
x_537 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_consume_spec__3(x_420, x_473, x_471, x_536, x_480);
lean_dec(x_473);
x_492 = x_537;
goto block_531;
}
}
block_491:
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
if (lean_is_scalar(x_482)) {
 x_486 = lean_alloc_ctor(0, 4, 0);
} else {
 x_486 = x_482;
}
lean_ctor_set(x_486, 0, x_478);
lean_ctor_set(x_486, 1, x_479);
lean_ctor_set(x_486, 2, x_484);
lean_ctor_set(x_486, 3, x_485);
x_487 = lean_st_ref_set(x_3, x_486, x_477);
lean_dec(x_3);
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_489 = x_487;
} else {
 lean_dec_ref(x_487);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_483);
lean_ctor_set(x_490, 1, x_488);
return x_490;
}
block_531:
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint64_t x_499; uint64_t x_500; uint64_t x_501; uint64_t x_502; uint64_t x_503; uint64_t x_504; uint64_t x_505; size_t x_506; size_t x_507; size_t x_508; size_t x_509; size_t x_510; lean_object* x_511; uint8_t x_512; 
x_493 = lean_ctor_get(x_481, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_481, 1);
lean_inc_ref(x_494);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_495 = x_481;
} else {
 lean_dec_ref(x_481);
 x_495 = lean_box(0);
}
x_496 = lean_array_push(x_467, x_429);
if (lean_is_scalar(x_469)) {
 x_497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_497 = x_469;
}
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_468);
x_498 = lean_array_get_size(x_494);
x_499 = l_Lean_Expr_hash(x_441);
x_500 = 32;
x_501 = lean_uint64_shift_right(x_499, x_500);
x_502 = lean_uint64_xor(x_499, x_501);
x_503 = 16;
x_504 = lean_uint64_shift_right(x_502, x_503);
x_505 = lean_uint64_xor(x_502, x_504);
x_506 = lean_uint64_to_usize(x_505);
x_507 = lean_usize_of_nat(x_498);
lean_dec(x_498);
x_508 = 1;
x_509 = lean_usize_sub(x_507, x_508);
x_510 = lean_usize_land(x_506, x_509);
x_511 = lean_array_uget(x_494, x_510);
x_512 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_441, x_511);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; 
x_513 = lean_unsigned_to_nat(1u);
x_514 = lean_nat_add(x_493, x_513);
lean_dec(x_493);
x_515 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_515, 0, x_441);
lean_ctor_set(x_515, 1, x_497);
lean_ctor_set(x_515, 2, x_511);
x_516 = lean_array_uset(x_494, x_510, x_515);
x_517 = lean_unsigned_to_nat(4u);
x_518 = lean_nat_mul(x_514, x_517);
x_519 = lean_unsigned_to_nat(3u);
x_520 = lean_nat_div(x_518, x_519);
lean_dec(x_518);
x_521 = lean_array_get_size(x_516);
x_522 = lean_nat_dec_le(x_520, x_521);
lean_dec(x_521);
lean_dec(x_520);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; 
x_523 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_516);
if (lean_is_scalar(x_495)) {
 x_524 = lean_alloc_ctor(0, 2, 0);
} else {
 x_524 = x_495;
}
lean_ctor_set(x_524, 0, x_514);
lean_ctor_set(x_524, 1, x_523);
x_484 = x_492;
x_485 = x_524;
goto block_491;
}
else
{
lean_object* x_525; 
if (lean_is_scalar(x_495)) {
 x_525 = lean_alloc_ctor(0, 2, 0);
} else {
 x_525 = x_495;
}
lean_ctor_set(x_525, 0, x_514);
lean_ctor_set(x_525, 1, x_516);
x_484 = x_492;
x_485 = x_525;
goto block_491;
}
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_526 = lean_box(0);
x_527 = lean_array_uset(x_494, x_510, x_526);
x_528 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_441, x_497, x_511);
x_529 = lean_array_uset(x_527, x_510, x_528);
if (lean_is_scalar(x_495)) {
 x_530 = lean_alloc_ctor(0, 2, 0);
} else {
 x_530 = x_495;
}
lean_ctor_set(x_530, 0, x_493);
lean_ctor_set(x_530, 1, x_529);
x_484 = x_492;
x_485 = x_530;
goto block_491;
}
}
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec_ref(x_467);
lean_dec(x_441);
lean_dec_ref(x_429);
lean_dec_ref(x_420);
lean_dec(x_3);
x_538 = lean_ctor_get(x_472, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_472, 1);
lean_inc(x_539);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_540 = x_472;
} else {
 lean_dec_ref(x_472);
 x_540 = lean_box(0);
}
if (lean_is_scalar(x_540)) {
 x_541 = lean_alloc_ctor(1, 2, 0);
} else {
 x_541 = x_540;
}
lean_ctor_set(x_541, 0, x_538);
lean_ctor_set(x_541, 1, x_539);
return x_541;
}
}
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_438);
lean_dec(x_437);
lean_dec(x_435);
lean_dec_ref(x_429);
lean_dec_ref(x_420);
lean_dec(x_418);
lean_dec(x_414);
lean_dec_ref(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_542 = lean_ctor_get(x_440, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_440, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_544 = x_440;
} else {
 lean_dec_ref(x_440);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 2, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_542);
lean_ctor_set(x_545, 1, x_543);
return x_545;
}
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec_ref(x_429);
lean_dec(x_424);
lean_dec(x_422);
lean_dec_ref(x_420);
lean_dec(x_418);
lean_dec(x_414);
lean_dec_ref(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_546 = lean_ctor_get(x_430, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_430, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_548 = x_430;
} else {
 lean_dec_ref(x_430);
 x_548 = lean_box(0);
}
if (lean_is_scalar(x_548)) {
 x_549 = lean_alloc_ctor(1, 2, 0);
} else {
 x_549 = x_548;
}
lean_ctor_set(x_549, 0, x_546);
lean_ctor_set(x_549, 1, x_547);
return x_549;
}
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_571; lean_object* x_611; lean_object* x_612; uint8_t x_613; 
lean_dec(x_422);
lean_dec(x_418);
lean_dec(x_414);
lean_dec_ref(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_550 = lean_ctor_get(x_427, 0);
lean_inc(x_550);
lean_dec(x_427);
x_551 = lean_st_ref_take(x_3, x_428);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec_ref(x_551);
x_554 = lean_ctor_get(x_552, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_552, 1);
lean_inc_ref(x_555);
x_556 = lean_ctor_get(x_552, 2);
lean_inc_ref(x_556);
x_557 = lean_ctor_get(x_552, 3);
lean_inc_ref(x_557);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 lean_ctor_release(x_552, 1);
 lean_ctor_release(x_552, 2);
 lean_ctor_release(x_552, 3);
 x_558 = x_552;
} else {
 lean_dec_ref(x_552);
 x_558 = lean_box(0);
}
x_559 = lean_ctor_get(x_550, 0);
lean_inc_ref(x_559);
x_560 = lean_ctor_get(x_550, 1);
lean_inc_ref(x_560);
if (lean_is_exclusive(x_550)) {
 lean_ctor_release(x_550, 0);
 lean_ctor_release(x_550, 1);
 x_561 = x_550;
} else {
 lean_dec_ref(x_550);
 x_561 = lean_box(0);
}
x_562 = lean_box(0);
x_611 = lean_unsigned_to_nat(0u);
x_612 = lean_array_get_size(x_560);
x_613 = lean_nat_dec_lt(x_611, x_612);
if (x_613 == 0)
{
lean_dec(x_612);
lean_dec_ref(x_420);
x_571 = x_556;
goto block_610;
}
else
{
uint8_t x_614; 
x_614 = lean_nat_dec_le(x_612, x_612);
if (x_614 == 0)
{
lean_dec(x_612);
lean_dec_ref(x_420);
x_571 = x_556;
goto block_610;
}
else
{
size_t x_615; size_t x_616; lean_object* x_617; 
x_615 = 0;
x_616 = lean_usize_of_nat(x_612);
lean_dec(x_612);
x_617 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_consume_spec__3(x_420, x_560, x_615, x_616, x_556);
x_571 = x_617;
goto block_610;
}
}
block_570:
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
if (lean_is_scalar(x_558)) {
 x_565 = lean_alloc_ctor(0, 4, 0);
} else {
 x_565 = x_558;
}
lean_ctor_set(x_565, 0, x_554);
lean_ctor_set(x_565, 1, x_555);
lean_ctor_set(x_565, 2, x_563);
lean_ctor_set(x_565, 3, x_564);
x_566 = lean_st_ref_set(x_3, x_565, x_553);
lean_dec(x_3);
x_567 = lean_ctor_get(x_566, 1);
lean_inc(x_567);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_568 = x_566;
} else {
 lean_dec_ref(x_566);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(0, 2, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_562);
lean_ctor_set(x_569, 1, x_567);
return x_569;
}
block_610:
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; uint64_t x_578; uint64_t x_579; uint64_t x_580; uint64_t x_581; uint64_t x_582; uint64_t x_583; uint64_t x_584; size_t x_585; size_t x_586; size_t x_587; size_t x_588; size_t x_589; lean_object* x_590; uint8_t x_591; 
x_572 = lean_ctor_get(x_557, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_557, 1);
lean_inc_ref(x_573);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_574 = x_557;
} else {
 lean_dec_ref(x_557);
 x_574 = lean_box(0);
}
x_575 = lean_array_push(x_559, x_429);
if (lean_is_scalar(x_561)) {
 x_576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_576 = x_561;
}
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_560);
x_577 = lean_array_get_size(x_573);
x_578 = l_Lean_Expr_hash(x_424);
x_579 = 32;
x_580 = lean_uint64_shift_right(x_578, x_579);
x_581 = lean_uint64_xor(x_578, x_580);
x_582 = 16;
x_583 = lean_uint64_shift_right(x_581, x_582);
x_584 = lean_uint64_xor(x_581, x_583);
x_585 = lean_uint64_to_usize(x_584);
x_586 = lean_usize_of_nat(x_577);
lean_dec(x_577);
x_587 = 1;
x_588 = lean_usize_sub(x_586, x_587);
x_589 = lean_usize_land(x_585, x_588);
x_590 = lean_array_uget(x_573, x_589);
x_591 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_424, x_590);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; uint8_t x_601; 
x_592 = lean_unsigned_to_nat(1u);
x_593 = lean_nat_add(x_572, x_592);
lean_dec(x_572);
x_594 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_594, 0, x_424);
lean_ctor_set(x_594, 1, x_576);
lean_ctor_set(x_594, 2, x_590);
x_595 = lean_array_uset(x_573, x_589, x_594);
x_596 = lean_unsigned_to_nat(4u);
x_597 = lean_nat_mul(x_593, x_596);
x_598 = lean_unsigned_to_nat(3u);
x_599 = lean_nat_div(x_597, x_598);
lean_dec(x_597);
x_600 = lean_array_get_size(x_595);
x_601 = lean_nat_dec_le(x_599, x_600);
lean_dec(x_600);
lean_dec(x_599);
if (x_601 == 0)
{
lean_object* x_602; lean_object* x_603; 
x_602 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_595);
if (lean_is_scalar(x_574)) {
 x_603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_603 = x_574;
}
lean_ctor_set(x_603, 0, x_593);
lean_ctor_set(x_603, 1, x_602);
x_563 = x_571;
x_564 = x_603;
goto block_570;
}
else
{
lean_object* x_604; 
if (lean_is_scalar(x_574)) {
 x_604 = lean_alloc_ctor(0, 2, 0);
} else {
 x_604 = x_574;
}
lean_ctor_set(x_604, 0, x_593);
lean_ctor_set(x_604, 1, x_595);
x_563 = x_571;
x_564 = x_604;
goto block_570;
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_605 = lean_box(0);
x_606 = lean_array_uset(x_573, x_589, x_605);
x_607 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_424, x_576, x_590);
x_608 = lean_array_uset(x_606, x_589, x_607);
if (lean_is_scalar(x_574)) {
 x_609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_609 = x_574;
}
lean_ctor_set(x_609, 0, x_572);
lean_ctor_set(x_609, 1, x_608);
x_563 = x_571;
x_564 = x_609;
goto block_570;
}
}
}
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_422);
lean_dec_ref(x_420);
lean_dec(x_418);
lean_dec(x_414);
lean_dec_ref(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_618 = lean_ctor_get(x_423, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_423, 1);
lean_inc(x_619);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_620 = x_423;
} else {
 lean_dec_ref(x_423);
 x_620 = lean_box(0);
}
if (lean_is_scalar(x_620)) {
 x_621 = lean_alloc_ctor(1, 2, 0);
} else {
 x_621 = x_620;
}
lean_ctor_set(x_621, 0, x_618);
lean_ctor_set(x_621, 1, x_619);
return x_621;
}
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_414);
lean_dec_ref(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_622 = lean_ctor_get(x_417, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_417, 1);
lean_inc(x_623);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_624 = x_417;
} else {
 lean_dec_ref(x_417);
 x_624 = lean_box(0);
}
if (lean_is_scalar(x_624)) {
 x_625 = lean_alloc_ctor(1, 2, 0);
} else {
 x_625 = x_624;
}
lean_ctor_set(x_625, 0, x_622);
lean_ctor_set(x_625, 1, x_623);
return x_625;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_SynthInstance_consume_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at___Lean_Meta_SynthInstance_consume_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_SynthInstance_consume_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_isAssigned___at___Lean_Meta_SynthInstance_consume_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___Lean_Meta_SynthInstance_consume_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_filterAuxM___at___Lean_Meta_SynthInstance_consume_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_mapMUnsafe_map___at___Lean_Meta_SynthInstance_consume_spec__2(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_consume_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SynthInstance_consume_spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_consume___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_Meta_SynthInstance_consume___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode;
x_8 = l_Array_back_x21___redArg(x_7, x_6);
lean_dec_ref(x_6);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode;
x_13 = l_Array_back_x21___redArg(x_12, x_11);
lean_dec_ref(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_getTop___redArg(x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_getTop___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_getTop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_10);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_11 = x_5;
} else {
 lean_dec_ref(x_5);
 x_11 = lean_box(0);
}
x_12 = lean_box(0);
x_21 = lean_array_get_size(x_8);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_21, x_22);
x_24 = lean_nat_dec_lt(x_23, x_21);
lean_dec(x_21);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_1);
x_13 = x_8;
goto block_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_array_fget(x_8, x_23);
x_26 = lean_array_fset(x_8, x_23, x_12);
x_27 = lean_apply_1(x_1, x_25);
x_28 = lean_array_fset(x_26, x_23, x_27);
lean_dec(x_23);
x_13 = x_28;
goto block_20;
}
block_20:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
if (lean_is_scalar(x_11)) {
 x_14 = lean_alloc_ctor(0, 4, 0);
} else {
 x_14 = x_11;
}
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
x_15 = lean_st_ref_set(x_2, x_14, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_10, 3);
lean_inc_ref(x_15);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 x_16 = x_10;
} else {
 lean_dec_ref(x_10);
 x_16 = lean_box(0);
}
x_17 = lean_box(0);
x_26 = lean_array_get_size(x_13);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_26, x_27);
x_29 = lean_nat_dec_lt(x_28, x_26);
lean_dec(x_26);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_1);
x_18 = x_13;
goto block_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_array_fget(x_13, x_28);
x_31 = lean_array_fset(x_13, x_28, x_17);
x_32 = lean_apply_1(x_1, x_30);
x_33 = lean_array_fset(x_31, x_28, x_32);
lean_dec(x_28);
x_18 = x_33;
goto block_25;
}
block_25:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
if (lean_is_scalar(x_16)) {
 x_19 = lean_alloc_ctor(0, 4, 0);
} else {
 x_19 = x_16;
}
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
x_20 = lean_st_ref_set(x_3, x_19, x_11);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_17);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_modifyTop___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_modifyTop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SynthInstance_generate_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_Meta_AbstractMVarsResult_numMVars(x_7);
lean_dec_ref(x_7);
x_9 = lean_nat_dec_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
return x_9;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" apply ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_generate___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" to ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_generate___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_7);
x_11 = lean_infer_type(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_12, x_7, x_13);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
x_20 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_21 = l_Lean_exceptOptionEmoji___redArg(x_3);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec_ref(x_21);
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_22);
lean_ctor_set(x_2, 0, x_20);
x_23 = l_Lean_Meta_SynthInstance_generate___lam__0___closed__1;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_MessageData_ofExpr(x_18);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_SynthInstance_generate___lam__0___closed__3;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_ofExpr(x_17);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_14, 0, x_31);
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_dec(x_2);
x_34 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_35 = l_Lean_exceptOptionEmoji___redArg(x_3);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec_ref(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_SynthInstance_generate___lam__0___closed__1;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_MessageData_ofExpr(x_33);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_SynthInstance_generate___lam__0___closed__3;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_MessageData_ofExpr(x_32);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_34);
lean_ctor_set(x_14, 0, x_46);
return x_14;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
x_49 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_49);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_50 = x_2;
} else {
 lean_dec_ref(x_2);
 x_50 = lean_box(0);
}
x_51 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_52 = l_Lean_exceptOptionEmoji___redArg(x_3);
x_53 = l_Lean_stringToMessageData(x_52);
lean_dec_ref(x_52);
if (lean_is_scalar(x_50)) {
 x_54 = lean_alloc_ctor(7, 2, 0);
} else {
 x_54 = x_50;
 lean_ctor_set_tag(x_54, 7);
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Meta_SynthInstance_generate___lam__0___closed__1;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_MessageData_ofExpr(x_49);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_SynthInstance_generate___lam__0___closed__3;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_MessageData_ofExpr(x_47);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_51);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_48);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_7);
lean_dec_ref(x_2);
x_65 = !lean_is_exclusive(x_11);
if (x_65 == 0)
{
return x_11;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_11, 0);
x_67 = lean_ctor_get(x_11, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_11);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_14 = lean_st_ref_take(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_15, 3);
lean_inc_ref(x_20);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 x_21 = x_15;
} else {
 lean_dec_ref(x_15);
 x_21 = lean_box(0);
}
x_22 = lean_box(0);
x_56 = lean_array_get_size(x_18);
x_57 = lean_nat_sub(x_56, x_5);
x_58 = lean_nat_dec_lt(x_57, x_56);
lean_dec(x_56);
if (x_58 == 0)
{
lean_dec(x_57);
lean_dec(x_6);
x_23 = x_18;
goto block_55;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_array_fget(x_18, x_57);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 4);
lean_dec(x_61);
x_62 = lean_array_fset(x_18, x_57, x_22);
lean_ctor_set(x_59, 4, x_6);
x_63 = lean_array_fset(x_62, x_57, x_59);
lean_dec(x_57);
x_23 = x_63;
goto block_55;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_59, 0);
x_65 = lean_ctor_get(x_59, 1);
x_66 = lean_ctor_get(x_59, 2);
x_67 = lean_ctor_get(x_59, 3);
x_68 = lean_ctor_get_uint8(x_59, sizeof(void*)*5);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_59);
x_69 = lean_array_fset(x_18, x_57, x_22);
x_70 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set(x_70, 3, x_67);
lean_ctor_set(x_70, 4, x_6);
lean_ctor_set_uint8(x_70, sizeof(void*)*5, x_68);
x_71 = lean_array_fset(x_69, x_57, x_70);
lean_dec(x_57);
x_23 = x_71;
goto block_55;
}
}
block_55:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
if (lean_is_scalar(x_21)) {
 x_24 = lean_alloc_ctor(0, 4, 0);
} else {
 x_24 = x_21;
}
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
x_25 = lean_st_ref_set(x_8, x_24, x_16);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
x_27 = l_Lean_Meta_SynthInstance_tryResolve(x_1, x_2, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec_ref(x_27);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_3);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_4);
x_40 = l_Lean_Meta_SynthInstance_consume(x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_Lean_Meta_SynthInstance_generate___lam__1___closed__0;
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Lean_Meta_SynthInstance_generate___lam__1___closed__0;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_27);
if (x_51 == 0)
{
return x_27;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_27, 0);
x_53 = lean_ctor_get(x_27, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_27);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_backward_synthInstance_canonInstances;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_8 = l_Lean_Meta_SynthInstance_getTop___redArg(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_9, 3);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_9, 4);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_9, sizeof(void*)*5);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_50; uint8_t x_51; 
x_19 = lean_ctor_get(x_5, 2);
lean_inc(x_19);
x_20 = 1;
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_15, x_21);
lean_dec(x_15);
x_23 = l_Lean_Meta_SynthInstance_instInhabitedInstance;
x_24 = lean_array_get(x_23, x_14, x_22);
lean_dec_ref(x_14);
lean_inc_ref(x_24);
lean_inc_ref(x_11);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_generate___lam__0___boxed), 10, 2);
lean_closure_set(x_25, 0, x_11);
lean_closure_set(x_25, 1, x_24);
lean_inc_ref(x_12);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_generate___lam__1___boxed), 13, 6);
lean_closure_set(x_26, 0, x_11);
lean_closure_set(x_26, 1, x_24);
lean_closure_set(x_26, 2, x_12);
lean_closure_set(x_26, 3, x_17);
lean_closure_set(x_26, 4, x_21);
lean_closure_set(x_26, 5, x_22);
x_50 = l_Lean_Meta_SynthInstance_generate___closed__0;
x_51 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_19, x_50);
lean_dec(x_19);
if (x_51 == 0)
{
lean_dec_ref(x_12);
x_27 = x_1;
x_28 = x_2;
x_29 = x_3;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_10;
goto block_49;
}
else
{
if (x_16 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; size_t x_65; size_t x_66; size_t x_67; size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_71; 
x_52 = lean_st_ref_get(x_2, x_10);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 3);
lean_inc_ref(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec_ref(x_52);
x_56 = lean_ctor_get(x_54, 1);
lean_inc_ref(x_56);
lean_dec_ref(x_54);
x_57 = lean_array_get_size(x_56);
x_58 = l_Lean_Expr_hash(x_12);
x_59 = 32;
x_60 = lean_uint64_shift_right(x_58, x_59);
x_61 = lean_uint64_xor(x_58, x_60);
x_62 = 16;
x_63 = lean_uint64_shift_right(x_61, x_62);
x_64 = lean_uint64_xor(x_61, x_63);
x_65 = lean_uint64_to_usize(x_64);
x_66 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_67 = 1;
x_68 = lean_usize_sub(x_66, x_67);
x_69 = lean_usize_land(x_65, x_68);
x_70 = lean_array_uget(x_56, x_69);
lean_dec_ref(x_56);
x_71 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(x_12, x_70);
lean_dec(x_70);
lean_dec_ref(x_12);
if (lean_obj_tag(x_71) == 0)
{
x_27 = x_1;
x_28 = x_2;
x_29 = x_3;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_55;
goto block_49;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get(x_72, 1);
lean_inc_ref(x_73);
lean_dec(x_72);
x_74 = lean_array_get_size(x_73);
x_75 = lean_nat_dec_lt(x_17, x_74);
if (x_75 == 0)
{
lean_dec(x_74);
lean_dec_ref(x_73);
x_27 = x_1;
x_28 = x_2;
x_29 = x_3;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_55;
goto block_49;
}
else
{
if (x_75 == 0)
{
lean_dec(x_74);
lean_dec_ref(x_73);
x_27 = x_1;
x_28 = x_2;
x_29 = x_3;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_55;
goto block_49;
}
else
{
size_t x_76; size_t x_77; uint8_t x_78; 
x_76 = 0;
x_77 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_78 = l_Array_anyMUnsafe_any___at___Lean_Meta_SynthInstance_generate_spec__0(x_17, x_73, x_76, x_77);
lean_dec_ref(x_73);
if (x_78 == 0)
{
x_27 = x_1;
x_28 = x_2;
x_29 = x_3;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_55;
goto block_49;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_79 = lean_st_ref_take(x_2, x_55);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_80, 1);
x_84 = lean_array_pop(x_83);
lean_ctor_set(x_80, 1, x_84);
x_85 = lean_st_ref_set(x_2, x_80, x_81);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_85, 0, x_88);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_92 = lean_ctor_get(x_80, 0);
x_93 = lean_ctor_get(x_80, 1);
x_94 = lean_ctor_get(x_80, 2);
x_95 = lean_ctor_get(x_80, 3);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_80);
x_96 = lean_array_pop(x_93);
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_94);
lean_ctor_set(x_97, 3, x_95);
x_98 = lean_st_ref_set(x_2, x_97, x_81);
lean_dec(x_2);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_box(0);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
}
}
}
}
else
{
lean_dec_ref(x_12);
x_27 = x_1;
x_28 = x_2;
x_29 = x_3;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_10;
goto block_49;
}
}
block_49:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = l_Lean_Meta_SynthInstance_newSubgoal___closed__0;
x_35 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_36 = lean_box(x_20);
x_37 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___boxed), 13, 6);
lean_closure_set(x_37, 0, lean_box(0));
lean_closure_set(x_37, 1, x_34);
lean_closure_set(x_37, 2, x_25);
lean_closure_set(x_37, 3, x_26);
lean_closure_set(x_37, 4, x_36);
lean_closure_set(x_37, 5, x_35);
x_38 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_13, x_37, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_103 = lean_st_ref_take(x_2, x_10);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = !lean_is_exclusive(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_104, 1);
x_108 = lean_array_pop(x_107);
lean_ctor_set(x_104, 1, x_108);
x_109 = lean_st_ref_set(x_2, x_104, x_105);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 0);
lean_dec(x_111);
x_112 = lean_box(0);
lean_ctor_set(x_109, 0, x_112);
return x_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
lean_dec(x_109);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_116 = lean_ctor_get(x_104, 0);
x_117 = lean_ctor_get(x_104, 1);
x_118 = lean_ctor_get(x_104, 2);
x_119 = lean_ctor_get(x_104, 3);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_104);
x_120 = lean_array_pop(x_117);
x_121 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_118);
lean_ctor_set(x_121, 3, x_119);
x_122 = lean_st_ref_set(x_2, x_121, x_105);
lean_dec(x_2);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
x_125 = lean_box(0);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SynthInstance_generate_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Meta_SynthInstance_generate_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_SynthInstance_generate___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_SynthInstance_generate___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getNextToResume___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedAnswer;
x_2 = l_Lean_Meta_SynthInstance_instInhabitedConsumerNode;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_st_ref_take(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 2);
x_11 = lean_array_pop(x_10);
lean_ctor_set(x_7, 2, x_11);
x_12 = lean_st_ref_set(x_1, x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_15);
lean_dec(x_4);
x_16 = l_Lean_Meta_SynthInstance_getNextToResume___redArg___closed__0;
x_17 = l_Array_back_x21___redArg(x_16, x_15);
lean_dec_ref(x_15);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_19);
lean_dec(x_4);
x_20 = l_Lean_Meta_SynthInstance_getNextToResume___redArg___closed__0;
x_21 = l_Array_back_x21___redArg(x_20, x_19);
lean_dec_ref(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 2);
x_26 = lean_ctor_get(x_7, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_27 = lean_array_pop(x_25);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_st_ref_set(x_1, x_28, x_8);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_32);
lean_dec(x_4);
x_33 = l_Lean_Meta_SynthInstance_getNextToResume___redArg___closed__0;
x_34 = l_Array_back_x21___redArg(x_33, x_32);
lean_dec_ref(x_32);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_getNextToResume___redArg(x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_getNextToResume___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_getNextToResume(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_SynthInstance_resume_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___Lean_Meta_SynthInstance_getEntry_spec__0___closed__0;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("propagating ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" to subgoal ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" of ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_1, x_7, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_2, x_7, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_3, x_7, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__1;
x_23 = l_Lean_MessageData_ofExpr(x_13);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_23);
lean_ctor_set(x_15, 0, x_22);
x_24 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__3;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_24);
lean_ctor_set(x_11, 0, x_15);
x_25 = l_Lean_MessageData_ofExpr(x_17);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__5;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_ofExpr(x_21);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_19, 0, x_32);
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__1;
x_36 = l_Lean_MessageData_ofExpr(x_13);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_36);
lean_ctor_set(x_15, 0, x_35);
x_37 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__3;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_37);
lean_ctor_set(x_11, 0, x_15);
x_38 = l_Lean_MessageData_ofExpr(x_17);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__5;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_MessageData_ofExpr(x_33);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_34);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_47 = lean_ctor_get(x_15, 0);
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_15);
x_49 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_3, x_7, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__1;
x_54 = l_Lean_MessageData_ofExpr(x_13);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__3;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_56);
lean_ctor_set(x_11, 0, x_55);
x_57 = l_Lean_MessageData_ofExpr(x_47);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_11);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__5;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_MessageData_ofExpr(x_50);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
if (lean_is_scalar(x_52)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_52;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_51);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_66 = lean_ctor_get(x_11, 0);
x_67 = lean_ctor_get(x_11, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_11);
x_68 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_2, x_7, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = l_Lean_instantiateMVars___at___Lean_Meta_SynthInstance_mkTableKeyFor_spec__0___redArg(x_3, x_7, x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__1;
x_77 = l_Lean_MessageData_ofExpr(x_66);
if (lean_is_scalar(x_71)) {
 x_78 = lean_alloc_ctor(7, 2, 0);
} else {
 x_78 = x_71;
 lean_ctor_set_tag(x_78, 7);
}
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__3;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_MessageData_ofExpr(x_69);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Meta_SynthInstance_resume___lam__0___closed__5;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_MessageData_ofExpr(x_73);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
if (lean_is_scalar(x_75)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_75;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_74);
return x_89;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lam__0___boxed), 10, 3);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
x_15 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_inc(x_1);
x_27 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__1___redArg(x_1, x_12, x_14);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec_ref(x_27);
x_15 = x_8;
x_16 = x_9;
x_17 = x_10;
x_18 = x_11;
x_19 = x_12;
x_20 = x_13;
x_21 = x_30;
goto block_26;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_27, 1);
x_33 = lean_ctor_get(x_27, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_2, 2);
x_35 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__3;
x_36 = lean_nat_add(x_3, x_34);
x_37 = l_Nat_reprFast(x_36);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_MessageData_ofFormat(x_38);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_39);
lean_ctor_set(x_27, 0, x_35);
x_40 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg(x_1, x_41, x_10, x_11, x_12, x_13, x_32);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_15 = x_8;
x_16 = x_9;
x_17 = x_10;
x_18 = x_11;
x_19 = x_12;
x_20 = x_13;
x_21 = x_43;
goto block_26;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_dec(x_27);
x_45 = lean_ctor_get(x_2, 2);
x_46 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__3;
x_47 = lean_nat_add(x_3, x_45);
x_48 = l_Nat_reprFast(x_47);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg(x_1, x_53, x_10, x_11, x_12, x_13, x_44);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_15 = x_8;
x_16 = x_9;
x_17 = x_10;
x_18 = x_11;
x_19 = x_12;
x_20 = x_13;
x_21 = x_55;
goto block_26;
}
}
block_26:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_nat_add(x_3, x_22);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_6);
lean_ctor_set(x_24, 3, x_7);
lean_ctor_set(x_24, 4, x_23);
x_25 = l_Lean_Meta_SynthInstance_consume(x_24, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resume", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lam__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_SynthInstance_resume___lam__3___closed__0;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_1);
x_16 = lean_infer_type(x_1, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_19 = lean_infer_type(x_2, x_11, x_12, x_13, x_14, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
lean_inc_ref(x_3);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lam__1___boxed), 12, 4);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_17);
lean_closure_set(x_22, 3, x_4);
x_23 = l_Lean_Meta_SynthInstance_resume___lam__3___closed__1;
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lam__2___boxed), 14, 7);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_3);
lean_closure_set(x_24, 2, x_5);
lean_closure_set(x_24, 3, x_1);
lean_closure_set(x_24, 4, x_6);
lean_closure_set(x_24, 5, x_7);
lean_closure_set(x_24, 6, x_8);
x_25 = 1;
x_26 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_27 = l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg(x_23, x_22, x_24, x_25, x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
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
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.SynthInstance.resume", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resume found no remaining subgoals", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_SynthInstance_resume___closed__1;
x_2 = lean_unsigned_to_nat(18u);
x_3 = lean_unsigned_to_nat(591u);
x_4 = l_Lean_Meta_SynthInstance_resume___closed__0;
x_5 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Meta_SynthInstance_getNextToResume___redArg(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec_ref(x_8);
x_13 = l_Lean_Meta_SynthInstance_resume___closed__2;
x_14 = l_panic___at___Lean_Meta_SynthInstance_resume_spec__0(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec_ref(x_8);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_10, 4);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc(x_16);
lean_inc(x_21);
lean_inc_ref(x_19);
x_23 = l_Lean_Meta_SynthInstance_tryAnswer(x_19, x_21, x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec_ref(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lam__3), 15, 8);
lean_closure_set(x_33, 0, x_17);
lean_closure_set(x_33, 1, x_21);
lean_closure_set(x_33, 2, x_16);
lean_closure_set(x_33, 3, x_19);
lean_closure_set(x_33, 4, x_20);
lean_closure_set(x_33, 5, x_18);
lean_closure_set(x_33, 6, x_32);
lean_closure_set(x_33, 7, x_22);
x_34 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_newSubgoal_spec__7___redArg(x_32, x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_31);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_SynthInstance_resume___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_SynthInstance_resume___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_SynthInstance_resume___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_checkSystem___redArg(x_1, x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_15);
lean_dec(x_12);
x_16 = l_Array_isEmpty___redArg(x_15);
lean_dec_ref(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec_ref(x_14);
lean_free_object(x_10);
x_17 = l_Lean_Meta_SynthInstance_resume(x_1, x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = l_Array_isEmpty___redArg(x_14);
lean_dec_ref(x_14);
if (x_30 == 0)
{
lean_object* x_31; 
lean_free_object(x_10);
x_31 = l_Lean_Meta_SynthInstance_generate(x_1, x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(x_16);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(x_16);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; lean_object* x_43; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_42 = 0;
x_43 = lean_box(x_42);
lean_ctor_set(x_10, 0, x_43);
return x_10;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_10, 0);
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_10);
x_46 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_44, 2);
lean_inc_ref(x_47);
lean_dec(x_44);
x_48 = l_Array_isEmpty___redArg(x_47);
lean_dec_ref(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec_ref(x_46);
x_49 = l_Lean_Meta_SynthInstance_resume(x_1, x_2, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = 1;
x_53 = lean_box(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_57 = x_49;
} else {
 lean_dec_ref(x_49);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = l_Array_isEmpty___redArg(x_46);
lean_dec_ref(x_46);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_Lean_Meta_SynthInstance_generate(x_1, x_2, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(x_48);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_45);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_8);
if (x_72 == 0)
{
return x_8;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_8, 0);
x_74 = lean_ctor_get(x_8, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_8);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_getResult___redArg(x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_getResult___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_getResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_synth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_8 = l_Lean_Meta_SynthInstance_step(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec_ref(x_8);
x_18 = l_Lean_Meta_SynthInstance_getResult___redArg(x_2, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_7 = x_20;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_main_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__4;
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
x_11 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_1, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_2, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_14);
x_20 = lean_st_ref_set(x_2, x_16, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_13);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_16, 1);
x_26 = lean_ctor_get(x_16, 2);
x_27 = lean_ctor_get(x_16, 3);
x_28 = lean_ctor_get(x_16, 4);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_st_ref_set(x_2, x_29, x_17);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_main_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_main_spec__0___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Meta_SynthInstance_main_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Meta_SynthInstance_main_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Core_withCurrHeartbeats___at___Lean_Meta_SynthInstance_main_spec__1___redArg___lam__0), 6, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
x_8 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_7, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Meta_SynthInstance_main_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_withCurrHeartbeats___at___Lean_Meta_SynthInstance_main_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to synthesize", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_main___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_main___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_main___lam__0___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_SynthInstance_main___lam__0___closed__6;
x_2 = l_Lean_Meta_SynthInstance_main___lam__0___closed__4;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_inc_ref(x_6);
x_30 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
lean_inc_ref(x_4);
x_33 = l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_main_spec__0___redArg(x_4, x_7, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l_Lean_Meta_SynthInstance_main___lam__0___closed__7;
x_37 = lean_st_mk_ref(x_36, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = lean_st_ref_get(x_7, x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_ctor_get(x_8, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_45);
lean_dec(x_42);
x_46 = l_Lean_Meta_SynthInstance_getMaxHeartbeats(x_44);
lean_dec(x_44);
lean_ctor_set(x_40, 1, x_46);
lean_ctor_set(x_40, 0, x_5);
x_47 = lean_box(1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_38);
lean_inc_ref(x_40);
x_48 = l_Lean_Meta_SynthInstance_newSubgoal(x_45, x_34, x_31, x_47, x_40, x_38, x_6, x_7, x_8, x_9, x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_38);
x_50 = l_Lean_Meta_SynthInstance_synth(x_40, x_38, x_6, x_7, x_8, x_9, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_st_ref_get(x_38, x_52);
lean_dec(x_38);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_38);
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_dec_ref(x_50);
x_11 = x_58;
x_12 = x_59;
goto block_29;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_40);
lean_dec(x_38);
x_60 = lean_ctor_get(x_48, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_dec_ref(x_48);
x_11 = x_60;
x_12 = x_61;
goto block_29;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_40, 0);
x_63 = lean_ctor_get(x_40, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_40);
x_64 = lean_ctor_get(x_8, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_65);
lean_dec(x_62);
x_66 = l_Lean_Meta_SynthInstance_getMaxHeartbeats(x_64);
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_5);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_box(1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_38);
lean_inc_ref(x_67);
x_69 = l_Lean_Meta_SynthInstance_newSubgoal(x_65, x_34, x_31, x_68, x_67, x_38, x_6, x_7, x_8, x_9, x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_38);
x_71 = l_Lean_Meta_SynthInstance_synth(x_67, x_38, x_6, x_7, x_8, x_9, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = lean_st_ref_get(x_38, x_73);
lean_dec(x_38);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_38);
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_71, 1);
lean_inc(x_79);
lean_dec_ref(x_71);
x_11 = x_78;
x_12 = x_79;
goto block_29;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_67);
lean_dec(x_38);
x_80 = lean_ctor_get(x_69, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_dec_ref(x_69);
x_11 = x_80;
x_12 = x_81;
goto block_29;
}
}
block_29:
{
lean_object* x_13; uint8_t x_14; 
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Exception_isInterrupt(x_11);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Exception_isRuntime(x_11);
if (x_15 == 0)
{
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_SynthInstance_main___lam__0___closed__1;
x_17 = l_Lean_indentExpr(x_4);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_SynthInstance_main___lam__0___closed__3;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Exception_toMessageData(x_11);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_useDiagnosticMsg;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
x_28 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_27, x_6, x_7, x_8, x_9, x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_28;
}
}
else
{
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = 0;
x_10 = lean_box(0);
x_11 = lean_box(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_main___lam__0___boxed), 10, 5);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_1);
lean_closure_set(x_12, 4, x_2);
x_13 = l_Lean_Core_withCurrHeartbeats___at___Lean_Meta_SynthInstance_main_spec__1___redArg(x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_main_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_main_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_main_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_mkTableKey___at___Lean_Meta_SynthInstance_main_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_Meta_SynthInstance_main___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = lean_whnf(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = 0;
x_12 = 1;
x_13 = 1;
x_14 = l_Lean_Meta_mkForallFVars(x_1, x_9, x_11, x_12, x_12, x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_14;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___lam__0), 7, 0);
x_8 = 0;
x_9 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_1, x_7, x_8, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type class resolution failed, insufficient number of arguments", 62, 62);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = lean_whnf(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_30; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_17);
lean_dec(x_14);
x_30 = l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(x_4, x_2);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec_ref(x_16);
x_31 = lean_array_fget(x_3, x_2);
x_18 = x_31;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_15;
goto block_29;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_16);
x_33 = 0;
x_34 = lean_box(0);
lean_inc_ref(x_5);
x_35 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_32, x_33, x_34, x_5, x_6, x_7, x_8, x_15);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_18 = x_36;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_37;
goto block_29;
}
block_29:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc_ref(x_18);
x_24 = lean_array_fset(x_3, x_2, x_18);
x_25 = lean_expr_instantiate1(x_17, x_18);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_2, x_26);
lean_dec(x_2);
x_1 = x_25;
x_2 = x_27;
x_3 = x_24;
x_5 = x_19;
x_6 = x_20;
x_7 = x_21;
x_8 = x_22;
x_9 = x_23;
goto _start;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_14);
lean_dec_ref(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_dec_ref(x_13);
x_39 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1;
x_40 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_39, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_13);
if (x_41 == 0)
{
return x_13;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_getAppFn(x_3);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_st_ref_get(x_7, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = l_Lean_getOutParamPositions_x3f(x_15, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Array_isEmpty___redArg(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_11);
lean_dec_ref(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_9);
x_19 = lean_infer_type(x_9, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lam__0___closed__0;
x_23 = l_Lean_Expr_getAppNumArgs(x_3);
lean_inc(x_23);
x_24 = lean_mk_array(x_23, x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_23, x_25);
lean_dec(x_23);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_24, x_26);
x_28 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_29 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs(x_20, x_28, x_27, x_17, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_17);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = 1;
x_33 = l_Lean_mkAppN(x_9, x_30);
lean_dec(x_30);
x_34 = 1;
x_35 = l_Lean_Meta_mkForallFVars(x_2, x_33, x_18, x_32, x_32, x_34, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_19;
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_42);
lean_dec(x_40);
x_43 = l_Lean_getOutParamPositions_x3f(x_42, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Array_isEmpty___redArg(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec_ref(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_9);
x_47 = lean_infer_type(x_9, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lam__0___closed__0;
x_51 = l_Lean_Expr_getAppNumArgs(x_3);
lean_inc(x_51);
x_52 = lean_mk_array(x_51, x_50);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_sub(x_51, x_53);
lean_dec(x_51);
x_55 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_52, x_54);
x_56 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_57 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs(x_48, x_56, x_55, x_45, x_4, x_5, x_6, x_7, x_49);
lean_dec(x_45);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = 1;
x_61 = l_Lean_mkAppN(x_9, x_58);
lean_dec(x_58);
x_62 = 1;
x_63 = l_Lean_Meta_mkForallFVars(x_2, x_61, x_46, x_60, x_60, x_62, x_4, x_5, x_6, x_7, x_59);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_66 = x_57;
} else {
 lean_dec_ref(x_57);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_dec(x_45);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_47;
}
}
else
{
lean_object* x_68; 
lean_dec(x_45);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_41);
return x_68;
}
}
}
}
else
{
lean_object* x_69; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_8);
return x_69;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lam__0), 8, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = 0;
x_9 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" result type", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__1;
x_2 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nis not definitionally equal to", 31, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_3, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 6);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_22 = 1;
x_23 = 1;
lean_ctor_set_uint8(x_9, 7, x_23);
lean_ctor_set_uint8(x_9, 9, x_22);
x_24 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_9);
x_25 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_25, 2, x_14);
lean_ctor_set(x_25, 3, x_15);
lean_ctor_set(x_25, 4, x_16);
lean_ctor_set(x_25, 5, x_17);
lean_ctor_set(x_25, 6, x_18);
lean_ctor_set_uint64(x_25, sizeof(void*)*7, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 8, x_12);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 9, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 10, x_21);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_10);
lean_inc_ref(x_1);
x_26 = l_Lean_Meta_isExprDefEq(x_1, x_10, x_25, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_ctor_get(x_26, 0);
lean_dec(x_31);
x_32 = l_Lean_Meta_SynthInstance_newSubgoal___closed__0;
x_33 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_32, x_5, x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_free_object(x_26);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
lean_ctor_set(x_33, 0, x_27);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec_ref(x_33);
x_41 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_42 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__2;
x_43 = l_Lean_indentExpr(x_10);
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_43);
lean_ctor_set(x_26, 0, x_42);
x_44 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__4;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_26);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_indentExpr(x_1);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
x_49 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_32, x_48, x_3, x_4, x_5, x_6, x_40);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_27);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_27);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_26, 1);
lean_inc(x_54);
lean_dec(x_26);
x_55 = l_Lean_Meta_SynthInstance_newSubgoal___closed__0;
x_56 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_55, x_5, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_60 = x_56;
} else {
 lean_dec_ref(x_56);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_27);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_dec_ref(x_56);
x_63 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_64 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__2;
x_65 = l_Lean_indentExpr(x_10);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__4;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_indentExpr(x_1);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_63);
x_72 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_55, x_71, x_3, x_4, x_5, x_6, x_62);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_ctor_set(x_75, 0, x_27);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_26;
}
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_26;
}
}
else
{
uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; uint64_t x_98; lean_object* x_99; lean_object* x_100; 
x_76 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_77 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_78 = lean_ctor_get_uint8(x_9, 0);
x_79 = lean_ctor_get_uint8(x_9, 1);
x_80 = lean_ctor_get_uint8(x_9, 2);
x_81 = lean_ctor_get_uint8(x_9, 3);
x_82 = lean_ctor_get_uint8(x_9, 4);
x_83 = lean_ctor_get_uint8(x_9, 5);
x_84 = lean_ctor_get_uint8(x_9, 6);
x_85 = lean_ctor_get_uint8(x_9, 8);
x_86 = lean_ctor_get_uint8(x_9, 10);
x_87 = lean_ctor_get_uint8(x_9, 11);
x_88 = lean_ctor_get_uint8(x_9, 12);
x_89 = lean_ctor_get_uint8(x_9, 13);
x_90 = lean_ctor_get_uint8(x_9, 14);
x_91 = lean_ctor_get_uint8(x_9, 15);
x_92 = lean_ctor_get_uint8(x_9, 16);
x_93 = lean_ctor_get_uint8(x_9, 17);
x_94 = lean_ctor_get_uint8(x_9, 18);
lean_dec(x_9);
x_95 = 1;
x_96 = 1;
x_97 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_97, 0, x_78);
lean_ctor_set_uint8(x_97, 1, x_79);
lean_ctor_set_uint8(x_97, 2, x_80);
lean_ctor_set_uint8(x_97, 3, x_81);
lean_ctor_set_uint8(x_97, 4, x_82);
lean_ctor_set_uint8(x_97, 5, x_83);
lean_ctor_set_uint8(x_97, 6, x_84);
lean_ctor_set_uint8(x_97, 7, x_96);
lean_ctor_set_uint8(x_97, 8, x_85);
lean_ctor_set_uint8(x_97, 9, x_95);
lean_ctor_set_uint8(x_97, 10, x_86);
lean_ctor_set_uint8(x_97, 11, x_87);
lean_ctor_set_uint8(x_97, 12, x_88);
lean_ctor_set_uint8(x_97, 13, x_89);
lean_ctor_set_uint8(x_97, 14, x_90);
lean_ctor_set_uint8(x_97, 15, x_91);
lean_ctor_set_uint8(x_97, 16, x_92);
lean_ctor_set_uint8(x_97, 17, x_93);
lean_ctor_set_uint8(x_97, 18, x_94);
x_98 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_97);
x_99 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_13);
lean_ctor_set(x_99, 2, x_14);
lean_ctor_set(x_99, 3, x_15);
lean_ctor_set(x_99, 4, x_16);
lean_ctor_set(x_99, 5, x_17);
lean_ctor_set(x_99, 6, x_18);
lean_ctor_set_uint64(x_99, sizeof(void*)*7, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*7 + 8, x_12);
lean_ctor_set_uint8(x_99, sizeof(void*)*7 + 9, x_76);
lean_ctor_set_uint8(x_99, sizeof(void*)*7 + 10, x_77);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_10);
lean_inc_ref(x_1);
x_100 = l_Lean_Meta_isExprDefEq(x_1, x_10, x_99, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_104 = x_100;
} else {
 lean_dec_ref(x_100);
 x_104 = lean_box(0);
}
x_105 = l_Lean_Meta_SynthInstance_newSubgoal___closed__0;
x_106 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_105, x_5, x_103);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_104);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_110 = x_106;
} else {
 lean_dec_ref(x_106);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_101);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
lean_dec_ref(x_106);
x_113 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_114 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__2;
x_115 = l_Lean_indentExpr(x_10);
if (lean_is_scalar(x_104)) {
 x_116 = lean_alloc_ctor(7, 2, 0);
} else {
 x_116 = x_104;
 lean_ctor_set_tag(x_116, 7);
}
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__4;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_indentExpr(x_1);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_113);
x_122 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_105, x_121, x_3, x_4, x_5, x_6, x_112);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_101);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_dec(x_101);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_100;
}
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_100;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_126 = !lean_is_exclusive(x_8);
if (x_126 == 0)
{
return x_8;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_8, 0);
x_128 = lean_ctor_get(x_8, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_8);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_applyAbstractResult_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_12 = l_Lean_Meta_openAbstractMVarsResult(x_11, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_16);
x_17 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams(x_1, x_16, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec_ref(x_17);
x_27 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_16, x_4, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
lean_inc(x_28);
x_30 = l_Lean_Meta_check(x_28, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_2, 0, x_28);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_2, 0, x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_28);
lean_free_object(x_2);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
lean_dec(x_2);
lean_inc_ref(x_3);
x_44 = l_Lean_Meta_openAbstractMVarsResult(x_43, x_3, x_4, x_5, x_6, x_7);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec_ref(x_44);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_48);
x_49 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams(x_1, x_48, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_48);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec_ref(x_49);
x_57 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_48, x_4, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
lean_inc(x_58);
x_60 = l_Lean_Meta_check(x_58, x_3, x_4, x_5, x_6, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_58);
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_48);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_69 = lean_ctor_get(x_49, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_49, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_71 = x_49;
} else {
 lean_dec_ref(x_49);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_applyCachedAbstractResult_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_50 = l_Lean_Meta_AbstractMVarsResult_numMVars(x_10);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_50, x_51);
lean_dec(x_50);
if (x_52 == 0)
{
x_11 = x_52;
goto block_49;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_53);
x_54 = l_Array_isEmpty___redArg(x_53);
lean_dec_ref(x_53);
x_11 = x_54;
goto block_49;
}
block_49:
{
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_applyAbstractResult_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_15);
lean_dec(x_10);
lean_inc_ref(x_15);
x_16 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams(x_1, x_15, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec_ref(x_15);
lean_free_object(x_2);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
lean_ctor_set(x_2, 0, x_15);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec_ref(x_15);
lean_free_object(x_2);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_33 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_33);
lean_dec(x_10);
lean_inc_ref(x_33);
x_34 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams(x_1, x_33, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_33);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_38 = x_34;
} else {
 lean_dec_ref(x_34);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_33);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_33);
x_45 = lean_ctor_get(x_34, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_47 = x_34;
} else {
 lean_dec_ref(x_34);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_beqSynthInstanceCacheKey____x40_Lean_Meta_Basic___hyg_1633____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_hashSynthInstanceCacheKey____x40_Lean_Meta_Basic___hyg_1583____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_4 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__0;
x_5 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__1;
x_6 = l_Lean_Meta_hashSynthInstanceCacheKey____x40_Lean_Meta_Basic___hyg_1583_(x_2);
x_7 = lean_uint64_to_usize(x_6);
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_4, x_5, x_1, x_7, x_8, x_2, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_2);
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_7, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_8, 2);
x_14 = lean_box(0);
x_15 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg(x_13, x_1, x_14);
lean_ctor_set(x_8, 2, x_15);
x_16 = lean_st_ref_set(x_4, x_7, x_9);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
x_25 = lean_ctor_get(x_8, 2);
x_26 = lean_ctor_get(x_8, 3);
x_27 = lean_ctor_get(x_8, 4);
x_28 = lean_ctor_get(x_8, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_29 = lean_box(0);
x_30 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg(x_25, x_1, x_29);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_27);
lean_ctor_set(x_31, 5, x_28);
lean_ctor_set(x_7, 1, x_31);
x_32 = lean_st_ref_set(x_4, x_7, x_9);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 2);
x_39 = lean_ctor_get(x_7, 3);
x_40 = lean_ctor_get(x_7, 4);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
x_41 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_8, 4);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_8, 5);
lean_inc_ref(x_46);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 lean_ctor_release(x_8, 4);
 lean_ctor_release(x_8, 5);
 x_47 = x_8;
} else {
 lean_dec_ref(x_8);
 x_47 = lean_box(0);
}
x_48 = lean_box(0);
x_49 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg(x_43, x_1, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 6, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set(x_50, 4, x_45);
lean_ctor_set(x_50, 5, x_46);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_37);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_38);
lean_ctor_set(x_51, 3, x_39);
lean_ctor_set(x_51, 4, x_40);
x_52 = lean_st_ref_set(x_4, x_51, x_9);
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
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_3, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_58 = x_3;
} else {
 lean_dec_ref(x_3);
 x_58 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_1);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_5);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_168 = lean_ctor_get(x_2, 0);
lean_inc(x_168);
x_169 = l_Lean_Meta_AbstractMVarsResult_numMVars(x_168);
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_nat_dec_eq(x_169, x_170);
lean_dec(x_169);
if (x_171 == 0)
{
lean_dec(x_168);
x_59 = x_171;
goto block_165;
}
else
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_ctor_get(x_168, 0);
lean_inc_ref(x_172);
lean_dec(x_168);
x_173 = l_Array_isEmpty___redArg(x_172);
lean_dec_ref(x_172);
x_59 = x_173;
goto block_165;
}
}
block_165:
{
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_58);
lean_dec(x_57);
x_60 = lean_st_ref_take(x_4, x_5);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec_ref(x_60);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_61, 1);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_62, 2);
x_68 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg(x_67, x_1, x_2);
lean_ctor_set(x_62, 2, x_68);
x_69 = lean_st_ref_set(x_4, x_61, x_63);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = lean_box(0);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_76 = lean_ctor_get(x_62, 0);
x_77 = lean_ctor_get(x_62, 1);
x_78 = lean_ctor_get(x_62, 2);
x_79 = lean_ctor_get(x_62, 3);
x_80 = lean_ctor_get(x_62, 4);
x_81 = lean_ctor_get(x_62, 5);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_62);
x_82 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg(x_78, x_1, x_2);
x_83 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_82);
lean_ctor_set(x_83, 3, x_79);
lean_ctor_set(x_83, 4, x_80);
lean_ctor_set(x_83, 5, x_81);
lean_ctor_set(x_61, 1, x_83);
x_84 = lean_st_ref_set(x_4, x_61, x_63);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_89 = lean_ctor_get(x_61, 0);
x_90 = lean_ctor_get(x_61, 2);
x_91 = lean_ctor_get(x_61, 3);
x_92 = lean_ctor_get(x_61, 4);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_61);
x_93 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_62, 2);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_62, 3);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_62, 4);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_62, 5);
lean_inc_ref(x_98);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 lean_ctor_release(x_62, 4);
 lean_ctor_release(x_62, 5);
 x_99 = x_62;
} else {
 lean_dec_ref(x_62);
 x_99 = lean_box(0);
}
x_100 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg(x_95, x_1, x_2);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 6, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_93);
lean_ctor_set(x_101, 1, x_94);
lean_ctor_set(x_101, 2, x_100);
lean_ctor_set(x_101, 3, x_96);
lean_ctor_set(x_101, 4, x_97);
lean_ctor_set(x_101, 5, x_98);
x_102 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_102, 0, x_89);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_90);
lean_ctor_set(x_102, 3, x_91);
lean_ctor_set(x_102, 4, x_92);
x_103 = lean_st_ref_set(x_4, x_102, x_63);
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
x_106 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_2);
x_108 = lean_st_ref_take(x_4, x_5);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 1);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec_ref(x_108);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_109, 1);
lean_dec(x_113);
x_114 = !lean_is_exclusive(x_110);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_115 = lean_ctor_get(x_110, 2);
x_116 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg___closed__0;
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_57);
if (lean_is_scalar(x_58)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_58;
}
lean_ctor_set(x_118, 0, x_117);
x_119 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg(x_115, x_1, x_118);
lean_ctor_set(x_110, 2, x_119);
x_120 = lean_st_ref_set(x_4, x_109, x_111);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_120, 0);
lean_dec(x_122);
x_123 = lean_box(0);
lean_ctor_set(x_120, 0, x_123);
return x_120;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_dec(x_120);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_127 = lean_ctor_get(x_110, 0);
x_128 = lean_ctor_get(x_110, 1);
x_129 = lean_ctor_get(x_110, 2);
x_130 = lean_ctor_get(x_110, 3);
x_131 = lean_ctor_get(x_110, 4);
x_132 = lean_ctor_get(x_110, 5);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_110);
x_133 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg___closed__0;
x_134 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_57);
if (lean_is_scalar(x_58)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_58;
}
lean_ctor_set(x_135, 0, x_134);
x_136 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg(x_129, x_1, x_135);
x_137 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_128);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_137, 3, x_130);
lean_ctor_set(x_137, 4, x_131);
lean_ctor_set(x_137, 5, x_132);
lean_ctor_set(x_109, 1, x_137);
x_138 = lean_st_ref_set(x_4, x_109, x_111);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
x_141 = lean_box(0);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_139);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_143 = lean_ctor_get(x_109, 0);
x_144 = lean_ctor_get(x_109, 2);
x_145 = lean_ctor_get(x_109, 3);
x_146 = lean_ctor_get(x_109, 4);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_109);
x_147 = lean_ctor_get(x_110, 0);
lean_inc_ref(x_147);
x_148 = lean_ctor_get(x_110, 1);
lean_inc_ref(x_148);
x_149 = lean_ctor_get(x_110, 2);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_110, 3);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_110, 4);
lean_inc_ref(x_151);
x_152 = lean_ctor_get(x_110, 5);
lean_inc_ref(x_152);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 lean_ctor_release(x_110, 5);
 x_153 = x_110;
} else {
 lean_dec_ref(x_110);
 x_153 = lean_box(0);
}
x_154 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg___closed__0;
x_155 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_155, 2, x_57);
if (lean_is_scalar(x_58)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_58;
}
lean_ctor_set(x_156, 0, x_155);
x_157 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg(x_149, x_1, x_156);
if (lean_is_scalar(x_153)) {
 x_158 = lean_alloc_ctor(0, 6, 0);
} else {
 x_158 = x_153;
}
lean_ctor_set(x_158, 0, x_147);
lean_ctor_set(x_158, 1, x_148);
lean_ctor_set(x_158, 2, x_157);
lean_ctor_set(x_158, 3, x_150);
lean_ctor_set(x_158, 4, x_151);
lean_ctor_set(x_158, 5, x_152);
x_159 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_159, 0, x_143);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_159, 2, x_144);
lean_ctor_set(x_159, 3, x_145);
lean_ctor_set(x_159, 4, x_146);
x_160 = lean_st_ref_set(x_4, x_159, x_111);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_box(0);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg(x_1, x_2, x_3, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_synthInstanceCore_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__0;
x_4 = l_Lean_Meta_hashSynthInstanceCacheKey____x40_Lean_Meta_Basic___hyg_1583_(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f_spec__0___redArg(x_3, x_1, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_synthInstanceCore_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_synthInstanceCore_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_1, x_4, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_12 = l_Lean_exceptOptionEmoji___redArg(x_2);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec_ref(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__1;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofExpr(x_10);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_23 = l_Lean_exceptOptionEmoji___redArg(x_2);
x_24 = l_Lean_stringToMessageData(x_23);
lean_dec_ref(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__1;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_ofExpr(x_20);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_Meta_SynthInstance_main(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<not-available>", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (cached)", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_4, 5);
x_13 = 1;
x_14 = 0;
x_15 = 3;
lean_ctor_set_uint8(x_10, 0, x_13);
lean_ctor_set_uint8(x_10, 1, x_13);
lean_ctor_set_uint8(x_10, 3, x_14);
lean_ctor_set_uint8(x_10, 4, x_13);
lean_ctor_set_uint8(x_10, 9, x_15);
lean_ctor_set_uint8(x_10, 11, x_14);
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_10);
lean_inc(x_12);
lean_ctor_set_uint64(x_4, sizeof(void*)*7, x_16);
lean_ctor_set_uint8(x_4, sizeof(void*)*7 + 10, x_13);
x_17 = l_Lean_Meta_getLocalInstances___redArg(x_4, x_8);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_1, x_5, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_23 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess(x_21, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_st_ref_get(x_5, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_28, 2);
lean_inc_ref(x_31);
lean_dec_ref(x_28);
lean_inc(x_24);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_12);
lean_inc_ref(x_32);
x_33 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_synthInstanceCore_x3f_spec__0___redArg(x_31, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
lean_inc(x_24);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstanceCore_x3f___lam__1), 7, 2);
lean_closure_set(x_34, 0, x_24);
lean_closure_set(x_34, 1, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_35 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_34, x_13, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_36);
x_38 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_applyAbstractResult_x3f(x_24, x_36, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
lean_inc(x_3);
x_50 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_3, x_6, x_40);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_41);
lean_dec_ref(x_4);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec_ref(x_50);
x_42 = x_5;
x_43 = x_53;
goto block_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_55 = x_50;
} else {
 lean_dec_ref(x_50);
 x_55 = lean_box(0);
}
x_56 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__1;
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_64; 
x_64 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__4;
x_57 = x_64;
goto block_63;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_39, 0);
lean_inc(x_65);
x_66 = l_Lean_MessageData_ofExpr(x_65);
x_57 = x_66;
goto block_63;
}
block_63:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(7, 2, 0);
} else {
 x_58 = x_55;
 lean_ctor_set_tag(x_58, 7);
}
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
if (lean_is_scalar(x_41)) {
 x_60 = lean_alloc_ctor(7, 2, 0);
} else {
 x_60 = x_41;
 lean_ctor_set_tag(x_60, 7);
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_3, x_60, x_4, x_5, x_6, x_7, x_54);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec_ref(x_61);
x_42 = x_5;
x_43 = x_62;
goto block_49;
}
}
block_49:
{
lean_object* x_44; uint8_t x_45; 
lean_inc(x_39);
x_44 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg(x_32, x_36, x_39, x_42, x_43);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_39);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_dec(x_36);
lean_dec_ref(x_32);
lean_dec_ref(x_4);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_38;
}
}
else
{
uint8_t x_67; 
lean_dec_ref(x_32);
lean_dec(x_24);
lean_dec_ref(x_4);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_35);
if (x_67 == 0)
{
return x_35;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_35, 0);
x_69 = lean_ctor_get(x_35, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_35);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_32);
lean_dec(x_2);
x_71 = lean_ctor_get(x_33, 0);
lean_inc(x_71);
lean_dec(x_33);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_72 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_applyCachedAbstractResult_x3f(x_24, x_71, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
lean_inc(x_3);
x_76 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_3, x_6, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
uint8_t x_79; 
lean_dec(x_75);
lean_dec(x_30);
lean_dec_ref(x_4);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_76);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_76, 0);
lean_dec(x_80);
lean_ctor_set(x_76, 0, x_73);
return x_76;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_dec(x_76);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec_ref(x_76);
x_84 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__1;
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_95; 
x_95 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__4;
x_85 = x_95;
goto block_94;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_73, 0);
lean_inc(x_96);
x_97 = l_Lean_MessageData_ofExpr(x_96);
x_85 = x_97;
goto block_94;
}
block_94:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
if (lean_is_scalar(x_75)) {
 x_86 = lean_alloc_ctor(7, 2, 0);
} else {
 x_86 = x_75;
 lean_ctor_set_tag(x_86, 7);
}
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__6;
if (lean_is_scalar(x_30)) {
 x_88 = lean_alloc_ctor(7, 2, 0);
} else {
 x_88 = x_30;
 lean_ctor_set_tag(x_88, 7);
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_3, x_88, x_4, x_5, x_6, x_7, x_83);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
lean_ctor_set(x_89, 0, x_73);
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_73);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
lean_dec(x_30);
lean_dec_ref(x_4);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_72;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_18);
lean_dec_ref(x_4);
lean_dec(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_23);
if (x_98 == 0)
{
return x_23;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_23, 0);
x_100 = lean_ctor_get(x_23, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_23);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; lean_object* x_119; uint64_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_102 = lean_ctor_get(x_4, 5);
x_103 = lean_ctor_get_uint8(x_10, 2);
x_104 = lean_ctor_get_uint8(x_10, 5);
x_105 = lean_ctor_get_uint8(x_10, 6);
x_106 = lean_ctor_get_uint8(x_10, 7);
x_107 = lean_ctor_get_uint8(x_10, 8);
x_108 = lean_ctor_get_uint8(x_10, 10);
x_109 = lean_ctor_get_uint8(x_10, 12);
x_110 = lean_ctor_get_uint8(x_10, 13);
x_111 = lean_ctor_get_uint8(x_10, 14);
x_112 = lean_ctor_get_uint8(x_10, 15);
x_113 = lean_ctor_get_uint8(x_10, 16);
x_114 = lean_ctor_get_uint8(x_10, 17);
x_115 = lean_ctor_get_uint8(x_10, 18);
lean_dec(x_10);
x_116 = 1;
x_117 = 0;
x_118 = 3;
x_119 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_119, 0, x_116);
lean_ctor_set_uint8(x_119, 1, x_116);
lean_ctor_set_uint8(x_119, 2, x_103);
lean_ctor_set_uint8(x_119, 3, x_117);
lean_ctor_set_uint8(x_119, 4, x_116);
lean_ctor_set_uint8(x_119, 5, x_104);
lean_ctor_set_uint8(x_119, 6, x_105);
lean_ctor_set_uint8(x_119, 7, x_106);
lean_ctor_set_uint8(x_119, 8, x_107);
lean_ctor_set_uint8(x_119, 9, x_118);
lean_ctor_set_uint8(x_119, 10, x_108);
lean_ctor_set_uint8(x_119, 11, x_117);
lean_ctor_set_uint8(x_119, 12, x_109);
lean_ctor_set_uint8(x_119, 13, x_110);
lean_ctor_set_uint8(x_119, 14, x_111);
lean_ctor_set_uint8(x_119, 15, x_112);
lean_ctor_set_uint8(x_119, 16, x_113);
lean_ctor_set_uint8(x_119, 17, x_114);
lean_ctor_set_uint8(x_119, 18, x_115);
x_120 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_119);
lean_inc(x_102);
lean_ctor_set(x_4, 0, x_119);
lean_ctor_set_uint64(x_4, sizeof(void*)*7, x_120);
lean_ctor_set_uint8(x_4, sizeof(void*)*7 + 10, x_116);
x_121 = l_Lean_Meta_getLocalInstances___redArg(x_4, x_8);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
x_124 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_1, x_5, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_127 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess(x_125, x_4, x_5, x_6, x_7, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec_ref(x_127);
x_130 = lean_st_ref_get(x_5, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 1);
lean_inc_ref(x_132);
lean_dec(x_131);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_134 = x_130;
} else {
 lean_dec_ref(x_130);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_132, 2);
lean_inc_ref(x_135);
lean_dec_ref(x_132);
lean_inc(x_128);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_122);
lean_ctor_set(x_136, 1, x_128);
lean_ctor_set(x_136, 2, x_102);
lean_inc_ref(x_136);
x_137 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_synthInstanceCore_x3f_spec__0___redArg(x_135, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_134);
lean_inc(x_128);
x_138 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstanceCore_x3f___lam__1), 7, 2);
lean_closure_set(x_138, 0, x_128);
lean_closure_set(x_138, 1, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_139 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_138, x_116, x_4, x_5, x_6, x_7, x_133);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec_ref(x_139);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_140);
x_142 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_applyAbstractResult_x3f(x_128, x_140, x_4, x_5, x_6, x_7, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
lean_inc(x_3);
x_153 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_3, x_6, x_144);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; 
lean_dec(x_145);
lean_dec_ref(x_4);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec_ref(x_153);
x_146 = x_5;
x_147 = x_156;
goto block_152;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_158 = x_153;
} else {
 lean_dec_ref(x_153);
 x_158 = lean_box(0);
}
x_159 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__1;
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_167; 
x_167 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__4;
x_160 = x_167;
goto block_166;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_143, 0);
lean_inc(x_168);
x_169 = l_Lean_MessageData_ofExpr(x_168);
x_160 = x_169;
goto block_166;
}
block_166:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(7, 2, 0);
} else {
 x_161 = x_158;
 lean_ctor_set_tag(x_161, 7);
}
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
if (lean_is_scalar(x_145)) {
 x_163 = lean_alloc_ctor(7, 2, 0);
} else {
 x_163 = x_145;
 lean_ctor_set_tag(x_163, 7);
}
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_3, x_163, x_4, x_5, x_6, x_7, x_157);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec_ref(x_164);
x_146 = x_5;
x_147 = x_165;
goto block_152;
}
}
block_152:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_inc(x_143);
x_148 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg(x_136, x_140, x_143, x_146, x_147);
lean_dec(x_146);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_143);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
else
{
lean_dec(x_140);
lean_dec_ref(x_136);
lean_dec_ref(x_4);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_142;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec_ref(x_136);
lean_dec(x_128);
lean_dec_ref(x_4);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_170 = lean_ctor_get(x_139, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_139, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_172 = x_139;
} else {
 lean_dec_ref(x_139);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec_ref(x_136);
lean_dec(x_2);
x_174 = lean_ctor_get(x_137, 0);
lean_inc(x_174);
lean_dec(x_137);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_175 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_applyCachedAbstractResult_x3f(x_128, x_174, x_4, x_5, x_6, x_7, x_133);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
lean_inc(x_3);
x_179 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_3, x_6, x_177);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_unbox(x_180);
lean_dec(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_178);
lean_dec(x_134);
lean_dec_ref(x_4);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_183 = x_179;
} else {
 lean_dec_ref(x_179);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_176);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_179, 1);
lean_inc(x_185);
lean_dec_ref(x_179);
x_186 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__1;
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_196; 
x_196 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__4;
x_187 = x_196;
goto block_195;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_176, 0);
lean_inc(x_197);
x_198 = l_Lean_MessageData_ofExpr(x_197);
x_187 = x_198;
goto block_195;
}
block_195:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
if (lean_is_scalar(x_178)) {
 x_188 = lean_alloc_ctor(7, 2, 0);
} else {
 x_188 = x_178;
 lean_ctor_set_tag(x_188, 7);
}
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__6;
if (lean_is_scalar(x_134)) {
 x_190 = lean_alloc_ctor(7, 2, 0);
} else {
 x_190 = x_134;
 lean_ctor_set_tag(x_190, 7);
}
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_3, x_190, x_4, x_5, x_6, x_7, x_185);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_193 = x_191;
} else {
 lean_dec_ref(x_191);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_176);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
else
{
lean_dec(x_134);
lean_dec_ref(x_4);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_175;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_122);
lean_dec_ref(x_4);
lean_dec(x_102);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_199 = lean_ctor_get(x_127, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_127, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_201 = x_127;
} else {
 lean_dec_ref(x_127);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
}
else
{
lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; uint8_t x_224; lean_object* x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; lean_object* x_229; uint64_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_203 = lean_ctor_get(x_4, 0);
x_204 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_205 = lean_ctor_get(x_4, 1);
x_206 = lean_ctor_get(x_4, 2);
x_207 = lean_ctor_get(x_4, 3);
x_208 = lean_ctor_get(x_4, 4);
x_209 = lean_ctor_get(x_4, 5);
x_210 = lean_ctor_get(x_4, 6);
x_211 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_203);
lean_dec(x_4);
x_212 = lean_ctor_get_uint8(x_203, 2);
x_213 = lean_ctor_get_uint8(x_203, 5);
x_214 = lean_ctor_get_uint8(x_203, 6);
x_215 = lean_ctor_get_uint8(x_203, 7);
x_216 = lean_ctor_get_uint8(x_203, 8);
x_217 = lean_ctor_get_uint8(x_203, 10);
x_218 = lean_ctor_get_uint8(x_203, 12);
x_219 = lean_ctor_get_uint8(x_203, 13);
x_220 = lean_ctor_get_uint8(x_203, 14);
x_221 = lean_ctor_get_uint8(x_203, 15);
x_222 = lean_ctor_get_uint8(x_203, 16);
x_223 = lean_ctor_get_uint8(x_203, 17);
x_224 = lean_ctor_get_uint8(x_203, 18);
if (lean_is_exclusive(x_203)) {
 x_225 = x_203;
} else {
 lean_dec_ref(x_203);
 x_225 = lean_box(0);
}
x_226 = 1;
x_227 = 0;
x_228 = 3;
if (lean_is_scalar(x_225)) {
 x_229 = lean_alloc_ctor(0, 0, 19);
} else {
 x_229 = x_225;
}
lean_ctor_set_uint8(x_229, 0, x_226);
lean_ctor_set_uint8(x_229, 1, x_226);
lean_ctor_set_uint8(x_229, 2, x_212);
lean_ctor_set_uint8(x_229, 3, x_227);
lean_ctor_set_uint8(x_229, 4, x_226);
lean_ctor_set_uint8(x_229, 5, x_213);
lean_ctor_set_uint8(x_229, 6, x_214);
lean_ctor_set_uint8(x_229, 7, x_215);
lean_ctor_set_uint8(x_229, 8, x_216);
lean_ctor_set_uint8(x_229, 9, x_228);
lean_ctor_set_uint8(x_229, 10, x_217);
lean_ctor_set_uint8(x_229, 11, x_227);
lean_ctor_set_uint8(x_229, 12, x_218);
lean_ctor_set_uint8(x_229, 13, x_219);
lean_ctor_set_uint8(x_229, 14, x_220);
lean_ctor_set_uint8(x_229, 15, x_221);
lean_ctor_set_uint8(x_229, 16, x_222);
lean_ctor_set_uint8(x_229, 17, x_223);
lean_ctor_set_uint8(x_229, 18, x_224);
x_230 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_229);
lean_inc(x_209);
x_231 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_205);
lean_ctor_set(x_231, 2, x_206);
lean_ctor_set(x_231, 3, x_207);
lean_ctor_set(x_231, 4, x_208);
lean_ctor_set(x_231, 5, x_209);
lean_ctor_set(x_231, 6, x_210);
lean_ctor_set_uint64(x_231, sizeof(void*)*7, x_230);
lean_ctor_set_uint8(x_231, sizeof(void*)*7 + 8, x_204);
lean_ctor_set_uint8(x_231, sizeof(void*)*7 + 9, x_211);
lean_ctor_set_uint8(x_231, sizeof(void*)*7 + 10, x_226);
x_232 = l_Lean_Meta_getLocalInstances___redArg(x_231, x_8);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec_ref(x_232);
x_235 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_1, x_5, x_234);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec_ref(x_235);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_231);
x_238 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess(x_236, x_231, x_5, x_6, x_7, x_237);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec_ref(x_238);
x_241 = lean_st_ref_get(x_5, x_240);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_242, 1);
lean_inc_ref(x_243);
lean_dec(x_242);
x_244 = lean_ctor_get(x_241, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_245 = x_241;
} else {
 lean_dec_ref(x_241);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_243, 2);
lean_inc_ref(x_246);
lean_dec_ref(x_243);
lean_inc(x_239);
x_247 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_247, 0, x_233);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_209);
lean_inc_ref(x_247);
x_248 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_synthInstanceCore_x3f_spec__0___redArg(x_246, x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_245);
lean_inc(x_239);
x_249 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstanceCore_x3f___lam__1), 7, 2);
lean_closure_set(x_249, 0, x_239);
lean_closure_set(x_249, 1, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_231);
x_250 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_249, x_226, x_231, x_5, x_6, x_7, x_244);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec_ref(x_250);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_231);
lean_inc(x_251);
x_253 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_applyAbstractResult_x3f(x_239, x_251, x_231, x_5, x_6, x_7, x_252);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_256 = x_253;
} else {
 lean_dec_ref(x_253);
 x_256 = lean_box(0);
}
lean_inc(x_3);
x_264 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_3, x_6, x_255);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_unbox(x_265);
lean_dec(x_265);
if (x_266 == 0)
{
lean_object* x_267; 
lean_dec(x_256);
lean_dec_ref(x_231);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
x_267 = lean_ctor_get(x_264, 1);
lean_inc(x_267);
lean_dec_ref(x_264);
x_257 = x_5;
x_258 = x_267;
goto block_263;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_264, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_269 = x_264;
} else {
 lean_dec_ref(x_264);
 x_269 = lean_box(0);
}
x_270 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__1;
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_278; 
x_278 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__4;
x_271 = x_278;
goto block_277;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_254, 0);
lean_inc(x_279);
x_280 = l_Lean_MessageData_ofExpr(x_279);
x_271 = x_280;
goto block_277;
}
block_277:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
if (lean_is_scalar(x_269)) {
 x_272 = lean_alloc_ctor(7, 2, 0);
} else {
 x_272 = x_269;
 lean_ctor_set_tag(x_272, 7);
}
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
x_273 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
if (lean_is_scalar(x_256)) {
 x_274 = lean_alloc_ctor(7, 2, 0);
} else {
 x_274 = x_256;
 lean_ctor_set_tag(x_274, 7);
}
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
x_275 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_3, x_274, x_231, x_5, x_6, x_7, x_268);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_231);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec_ref(x_275);
x_257 = x_5;
x_258 = x_276;
goto block_263;
}
}
block_263:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_inc(x_254);
x_259 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg(x_247, x_251, x_254, x_257, x_258);
lean_dec(x_257);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_254);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_dec(x_251);
lean_dec_ref(x_247);
lean_dec_ref(x_231);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_253;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec_ref(x_247);
lean_dec(x_239);
lean_dec_ref(x_231);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_281 = lean_ctor_get(x_250, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_250, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_283 = x_250;
} else {
 lean_dec_ref(x_250);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; 
lean_dec_ref(x_247);
lean_dec(x_2);
x_285 = lean_ctor_get(x_248, 0);
lean_inc(x_285);
lean_dec(x_248);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_231);
x_286 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_applyCachedAbstractResult_x3f(x_239, x_285, x_231, x_5, x_6, x_7, x_244);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_289 = x_286;
} else {
 lean_dec_ref(x_286);
 x_289 = lean_box(0);
}
lean_inc(x_3);
x_290 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_3, x_6, x_288);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_unbox(x_291);
lean_dec(x_291);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_289);
lean_dec(x_245);
lean_dec_ref(x_231);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_293 = lean_ctor_get(x_290, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_294 = x_290;
} else {
 lean_dec_ref(x_290);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_287);
lean_ctor_set(x_295, 1, x_293);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_290, 1);
lean_inc(x_296);
lean_dec_ref(x_290);
x_297 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__1;
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_307; 
x_307 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__4;
x_298 = x_307;
goto block_306;
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_287, 0);
lean_inc(x_308);
x_309 = l_Lean_MessageData_ofExpr(x_308);
x_298 = x_309;
goto block_306;
}
block_306:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
if (lean_is_scalar(x_289)) {
 x_299 = lean_alloc_ctor(7, 2, 0);
} else {
 x_299 = x_289;
 lean_ctor_set_tag(x_299, 7);
}
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__6;
if (lean_is_scalar(x_245)) {
 x_301 = lean_alloc_ctor(7, 2, 0);
} else {
 x_301 = x_245;
 lean_ctor_set_tag(x_301, 7);
}
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_3, x_301, x_231, x_5, x_6, x_7, x_296);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_231);
x_303 = lean_ctor_get(x_302, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_304 = x_302;
} else {
 lean_dec_ref(x_302);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_287);
lean_ctor_set(x_305, 1, x_303);
return x_305;
}
}
}
else
{
lean_dec(x_245);
lean_dec_ref(x_231);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_286;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_233);
lean_dec_ref(x_231);
lean_dec(x_209);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_310 = lean_ctor_get(x_238, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_238, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_312 = x_238;
} else {
 lean_dec_ref(x_238);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
}
}
static lean_object* _init_l_Lean_Meta_synthInstanceCore_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_synthInstance_maxSize;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstanceCore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstanceCore_x3f___lam__0___boxed), 7, 1);
lean_closure_set(x_8, 0, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 2);
lean_inc(x_16);
x_17 = l_Lean_Meta_synthInstanceCore_x3f___closed__0;
x_18 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_16, x_17);
lean_dec(x_16);
x_9 = x_18;
goto block_15;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_9 = x_19;
goto block_15;
}
block_15:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Meta_SynthInstance_newSubgoal___closed__0;
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstanceCore_x3f___lam__2), 8, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
x_12 = 1;
x_13 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_;
x_14 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0___redArg(x_10, x_8, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstanceCore_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_synthInstanceCore_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_4(x_3, x_5, x_6, x_7, x_8);
x_11 = l_Lean_profileitIOUnsafe___redArg(x_1, x_2, x_10, x_4, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeclass inference", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = l_Lean_Meta_synthInstance_x3f___closed__0;
lean_inc_ref(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstanceCore_x3f), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_Expr_getAppFn(x_1);
lean_dec_ref(x_1);
x_12 = l_Lean_Expr_constName_x3f(x_11);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0___redArg(x_9, x_8, x_10, x_13, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0___redArg(x_9, x_8, x_10, x_15, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_trySynthInstance___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_isDefEqStuckExceptionId;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySynthInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_synthInstance_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Option_toLOption___redArg(x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = l_Option_toLOption___redArg(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_31; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
x_19 = l_Lean_Meta_trySynthInstance___closed__0;
lean_inc(x_18);
lean_inc(x_17);
x_31 = l_Lean_Exception_isInterrupt(x_17);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_Exception_isRuntime(x_17);
x_20 = x_32;
goto block_30;
}
else
{
x_20 = x_31;
goto block_30;
}
block_30:
{
if (x_20 == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_18);
lean_dec(x_17);
return x_8;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_dec(x_23);
x_24 = lean_nat_dec_eq(x_19, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_free_object(x_17);
lean_dec(x_18);
return x_8;
}
else
{
lean_object* x_25; 
lean_dec_ref(x_8);
x_25 = lean_box(2);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 1, x_18);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_nat_dec_eq(x_19, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_dec(x_18);
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_8);
x_28 = lean_box(2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
return x_29;
}
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_17);
return x_8;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_44; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = l_Lean_Meta_trySynthInstance___closed__0;
lean_inc(x_34);
lean_inc(x_33);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
x_44 = l_Lean_Exception_isInterrupt(x_33);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Exception_isRuntime(x_33);
x_37 = x_45;
goto block_43;
}
else
{
x_37 = x_44;
goto block_43;
}
block_43:
{
if (x_37 == 0)
{
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_34);
lean_dec(x_33);
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_39 = x_33;
} else {
 lean_dec_ref(x_33);
 x_39 = lean_box(0);
}
x_40 = lean_nat_dec_eq(x_35, x_38);
lean_dec(x_38);
if (x_40 == 0)
{
lean_dec(x_39);
lean_dec(x_34);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_36);
x_41 = lean_box(2);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
 lean_ctor_set_tag(x_42, 0);
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
return x_42;
}
}
}
else
{
lean_dec(x_34);
lean_dec(x_33);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFailedToSynthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Lean_Meta_SynthInstance_main___lam__0___closed__1;
x_8 = l_Lean_indentExpr(x_1);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_useDiagnosticMsg;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_14, x_2, x_3, x_4, x_5, x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFailedToSynthesize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwFailedToSynthesize(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_23; 
x_8 = l_Lean_Meta_trySynthInstance___closed__0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_23 = l_Lean_Meta_synthInstance_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc_ref(x_1);
x_26 = l_Lean_Meta_throwFailedToSynthesize(x_1, x_3, x_4, x_5, x_6, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_17 = x_26;
x_18 = x_27;
x_19 = x_28;
goto block_22;
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
lean_dec(x_24);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
x_17 = x_23;
x_18 = x_36;
x_19 = x_37;
goto block_22;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
lean_inc(x_39);
lean_inc(x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_17 = x_40;
x_18 = x_38;
x_19 = x_39;
goto block_22;
}
}
block_16:
{
if (x_12 == 0)
{
if (lean_obj_tag(x_10) == 0)
{
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_11;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_nat_dec_eq(x_8, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_11;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_11);
x_15 = l_Lean_Meta_throwFailedToSynthesize(x_1, x_3, x_4, x_5, x_6, x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
}
else
{
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_11;
}
}
block_22:
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_18);
x_9 = x_19;
x_10 = x_18;
x_11 = x_17;
x_12 = x_21;
goto block_16;
}
else
{
x_9 = x_19;
x_10 = x_18;
x_11 = x_17;
x_12 = x_20;
goto block_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 7);
lean_inc_ref(x_9);
lean_dec_ref(x_6);
x_10 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isDelayedAssigned___at___Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(x_9, x_1);
x_11 = lean_box(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_6, 7);
lean_inc_ref(x_13);
lean_dec_ref(x_6);
x_14 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isDelayedAssigned___at___Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(x_13, x_1);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_maxSynthPendingDepth;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthPending", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__1;
x_2 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthPending ", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("too many nested synthPending invocations", 40, 40);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_getDecl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_27; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_12);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
lean_dec(x_10);
x_27 = lean_box(x_13);
if (lean_obj_tag(x_27) == 2)
{
lean_object* x_28; 
lean_dec_ref(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_28 = lean_box(x_2);
lean_ctor_set(x_8, 0, x_28);
return x_8;
}
else
{
lean_object* x_29; 
lean_dec(x_27);
lean_free_object(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_12);
x_29 = l_Lean_Meta_isClass_x3f(x_12, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec_ref(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_box(x_2);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_box(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_30);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_38 = x_29;
} else {
 lean_dec_ref(x_29);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_5, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_40);
x_41 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_42 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_3, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 6);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_50 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_51 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__0;
x_52 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_39, x_51);
lean_dec(x_39);
x_53 = lean_nat_dec_lt(x_52, x_47);
lean_dec(x_52);
if (x_53 == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_3);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_120 = lean_ctor_get(x_3, 6);
lean_dec(x_120);
x_121 = lean_ctor_get(x_3, 5);
lean_dec(x_121);
x_122 = lean_ctor_get(x_3, 4);
lean_dec(x_122);
x_123 = lean_ctor_get(x_3, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_3, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_3, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_3, 0);
lean_dec(x_126);
x_127 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__2;
x_128 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_127, x_5, x_37);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_128, 1);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_nat_add(x_47, x_132);
lean_dec(x_47);
lean_ctor_set(x_3, 5, x_133);
x_134 = lean_unbox(x_130);
lean_dec(x_130);
if (x_134 == 0)
{
lean_free_object(x_128);
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
x_110 = x_131;
goto block_118;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__4;
lean_inc(x_1);
x_136 = l_Lean_Expr_mvar___override(x_1);
x_137 = l_Lean_MessageData_ofExpr(x_136);
lean_ctor_set_tag(x_128, 7);
lean_ctor_set(x_128, 1, x_137);
lean_ctor_set(x_128, 0, x_135);
x_138 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_127, x_139, x_3, x_4, x_5, x_6, x_131);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec_ref(x_140);
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
x_110 = x_141;
goto block_118;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_142 = lean_ctor_get(x_128, 0);
x_143 = lean_ctor_get(x_128, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_128);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_add(x_47, x_144);
lean_dec(x_47);
lean_ctor_set(x_3, 5, x_145);
x_146 = lean_unbox(x_142);
lean_dec(x_142);
if (x_146 == 0)
{
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
x_110 = x_143;
goto block_118;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_147 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__4;
lean_inc(x_1);
x_148 = l_Lean_Expr_mvar___override(x_1);
x_149 = l_Lean_MessageData_ofExpr(x_148);
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_127, x_152, x_3, x_4, x_5, x_6, x_143);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec_ref(x_153);
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
x_110 = x_154;
goto block_118;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_3);
x_155 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__2;
x_156 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_155, x_5, x_37);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = lean_unsigned_to_nat(1u);
x_161 = lean_nat_add(x_47, x_160);
lean_dec(x_47);
x_162 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_162, 0, x_40);
lean_ctor_set(x_162, 1, x_43);
lean_ctor_set(x_162, 2, x_44);
lean_ctor_set(x_162, 3, x_45);
lean_ctor_set(x_162, 4, x_46);
lean_ctor_set(x_162, 5, x_161);
lean_ctor_set(x_162, 6, x_48);
lean_ctor_set_uint64(x_162, sizeof(void*)*7, x_41);
lean_ctor_set_uint8(x_162, sizeof(void*)*7 + 8, x_42);
lean_ctor_set_uint8(x_162, sizeof(void*)*7 + 9, x_49);
lean_ctor_set_uint8(x_162, sizeof(void*)*7 + 10, x_50);
x_163 = lean_unbox(x_157);
lean_dec(x_157);
if (x_163 == 0)
{
lean_dec(x_159);
x_106 = x_162;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
x_110 = x_158;
goto block_118;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_164 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__4;
lean_inc(x_1);
x_165 = l_Lean_Expr_mvar___override(x_1);
x_166 = l_Lean_MessageData_ofExpr(x_165);
if (lean_is_scalar(x_159)) {
 x_167 = lean_alloc_ctor(7, 2, 0);
} else {
 x_167 = x_159;
 lean_ctor_set_tag(x_167, 7);
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_155, x_169, x_162, x_4, x_5, x_6, x_158);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec_ref(x_170);
x_106 = x_162;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
x_110 = x_171;
goto block_118;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_40);
lean_dec(x_38);
lean_dec(x_1);
x_172 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__2;
x_173 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_172, x_5, x_37);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec_ref(x_173);
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_176;
goto block_26;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_173, 1);
lean_inc(x_177);
lean_dec_ref(x_173);
x_178 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__6;
x_179 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_172, x_178, x_3, x_4, x_5, x_6, x_177);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec_ref(x_179);
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_180;
goto block_26;
}
}
block_91:
{
lean_dec(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
lean_dec(x_56);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 0);
lean_dec(x_61);
x_62 = lean_box(x_2);
lean_ctor_set(x_58, 0, x_62);
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_dec(x_58);
x_64 = lean_box(x_2);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_dec_ref(x_58);
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
lean_dec(x_59);
x_68 = l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___redArg(x_1, x_56, x_66);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec_ref(x_68);
x_72 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_67, x_56, x_71);
lean_dec(x_56);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
x_75 = 1;
x_76 = lean_box(x_75);
lean_ctor_set(x_72, 0, x_76);
return x_72;
}
else
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = 1;
x_79 = lean_box(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_67);
lean_dec(x_56);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_68);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_68, 0);
lean_dec(x_82);
x_83 = lean_box(x_53);
lean_ctor_set(x_68, 0, x_83);
return x_68;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_68, 1);
lean_inc(x_84);
lean_dec(x_68);
x_85 = lean_box(x_53);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_56);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_58);
if (x_87 == 0)
{
return x_58;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_58, 0);
x_89 = lean_ctor_get(x_58, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_58);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
block_105:
{
if (x_100 == 0)
{
if (lean_obj_tag(x_97) == 0)
{
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_38);
x_54 = x_92;
x_55 = x_94;
x_56 = x_95;
x_57 = x_99;
x_58 = x_96;
goto block_91;
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_97, 0);
lean_inc(x_101);
lean_dec_ref(x_97);
x_102 = lean_nat_dec_eq(x_98, x_101);
lean_dec(x_101);
lean_dec(x_98);
if (x_102 == 0)
{
lean_dec(x_38);
x_54 = x_92;
x_55 = x_94;
x_56 = x_95;
x_57 = x_99;
x_58 = x_96;
goto block_91;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_99);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_92);
lean_dec(x_1);
x_103 = lean_box(x_2);
if (lean_is_scalar(x_38)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_38;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_93);
return x_104;
}
}
}
else
{
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_38);
x_54 = x_92;
x_55 = x_94;
x_56 = x_95;
x_57 = x_99;
x_58 = x_96;
goto block_91;
}
}
block_118:
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_box(0);
lean_inc(x_109);
lean_inc_ref(x_108);
lean_inc(x_107);
lean_inc_ref(x_106);
x_112 = l_Lean_Meta_synthInstance_x3f(x_12, x_111, x_106, x_107, x_108, x_109, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_dec(x_38);
x_54 = x_108;
x_55 = x_106;
x_56 = x_107;
x_57 = x_109;
x_58 = x_112;
goto block_91;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
x_115 = l_Lean_Meta_trySynthInstance___closed__0;
x_116 = l_Lean_Exception_isInterrupt(x_113);
if (x_116 == 0)
{
uint8_t x_117; 
x_117 = l_Lean_Exception_isRuntime(x_113);
x_92 = x_108;
x_93 = x_114;
x_94 = x_106;
x_95 = x_107;
x_96 = x_112;
x_97 = x_113;
x_98 = x_115;
x_99 = x_109;
x_100 = x_117;
goto block_105;
}
else
{
x_92 = x_108;
x_93 = x_114;
x_94 = x_106;
x_95 = x_107;
x_96 = x_112;
x_97 = x_113;
x_98 = x_115;
x_99 = x_109;
x_100 = x_116;
goto block_105;
}
}
}
}
}
else
{
uint8_t x_181; 
lean_dec_ref(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_29);
if (x_181 == 0)
{
return x_29;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_29, 0);
x_183 = lean_ctor_get(x_29, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_29);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
block_26:
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Meta_recordSynthPendingFailure(x_12, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(x_2);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_200; 
x_185 = lean_ctor_get(x_8, 0);
x_186 = lean_ctor_get(x_8, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_8);
x_187 = lean_ctor_get(x_185, 2);
lean_inc_ref(x_187);
x_188 = lean_ctor_get_uint8(x_185, sizeof(void*)*7);
lean_dec(x_185);
x_200 = lean_box(x_188);
if (lean_obj_tag(x_200) == 2)
{
lean_object* x_201; lean_object* x_202; 
lean_dec_ref(x_187);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_201 = lean_box(x_2);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_186);
return x_202;
}
else
{
lean_object* x_203; 
lean_dec(x_200);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_187);
x_203 = l_Lean_Meta_isClass_x3f(x_187, x_3, x_4, x_5, x_6, x_186);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec_ref(x_187);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_206 = x_203;
} else {
 lean_dec_ref(x_203);
 x_206 = lean_box(0);
}
x_207 = lean_box(x_2);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint64_t x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_204);
x_209 = lean_ctor_get(x_203, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_210 = x_203;
} else {
 lean_dec_ref(x_203);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_5, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_212);
x_213 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_214 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_215 = lean_ctor_get(x_3, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_216);
x_217 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_217);
x_218 = lean_ctor_get(x_3, 4);
lean_inc(x_218);
x_219 = lean_ctor_get(x_3, 5);
lean_inc(x_219);
x_220 = lean_ctor_get(x_3, 6);
lean_inc(x_220);
x_221 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_222 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_223 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__0;
x_224 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_211, x_223);
lean_dec(x_211);
x_225 = lean_nat_dec_lt(x_224, x_219);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 x_284 = x_3;
} else {
 lean_dec_ref(x_3);
 x_284 = lean_box(0);
}
x_285 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__2;
x_286 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_285, x_5, x_209);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_289 = x_286;
} else {
 lean_dec_ref(x_286);
 x_289 = lean_box(0);
}
x_290 = lean_unsigned_to_nat(1u);
x_291 = lean_nat_add(x_219, x_290);
lean_dec(x_219);
if (lean_is_scalar(x_284)) {
 x_292 = lean_alloc_ctor(0, 7, 11);
} else {
 x_292 = x_284;
}
lean_ctor_set(x_292, 0, x_212);
lean_ctor_set(x_292, 1, x_215);
lean_ctor_set(x_292, 2, x_216);
lean_ctor_set(x_292, 3, x_217);
lean_ctor_set(x_292, 4, x_218);
lean_ctor_set(x_292, 5, x_291);
lean_ctor_set(x_292, 6, x_220);
lean_ctor_set_uint64(x_292, sizeof(void*)*7, x_213);
lean_ctor_set_uint8(x_292, sizeof(void*)*7 + 8, x_214);
lean_ctor_set_uint8(x_292, sizeof(void*)*7 + 9, x_221);
lean_ctor_set_uint8(x_292, sizeof(void*)*7 + 10, x_222);
x_293 = lean_unbox(x_287);
lean_dec(x_287);
if (x_293 == 0)
{
lean_dec(x_289);
x_271 = x_292;
x_272 = x_4;
x_273 = x_5;
x_274 = x_6;
x_275 = x_288;
goto block_283;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_294 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__4;
lean_inc(x_1);
x_295 = l_Lean_Expr_mvar___override(x_1);
x_296 = l_Lean_MessageData_ofExpr(x_295);
if (lean_is_scalar(x_289)) {
 x_297 = lean_alloc_ctor(7, 2, 0);
} else {
 x_297 = x_289;
 lean_ctor_set_tag(x_297, 7);
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_296);
x_298 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2;
x_299 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_285, x_299, x_292, x_4, x_5, x_6, x_288);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
lean_dec_ref(x_300);
x_271 = x_292;
x_272 = x_4;
x_273 = x_5;
x_274 = x_6;
x_275 = x_301;
goto block_283;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec_ref(x_216);
lean_dec(x_215);
lean_dec_ref(x_212);
lean_dec(x_210);
lean_dec(x_1);
x_302 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__2;
x_303 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_302, x_5, x_209);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_unbox(x_304);
lean_dec(x_304);
if (x_305 == 0)
{
lean_object* x_306; 
x_306 = lean_ctor_get(x_303, 1);
lean_inc(x_306);
lean_dec_ref(x_303);
x_189 = x_3;
x_190 = x_4;
x_191 = x_5;
x_192 = x_6;
x_193 = x_306;
goto block_199;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_307 = lean_ctor_get(x_303, 1);
lean_inc(x_307);
lean_dec_ref(x_303);
x_308 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__6;
x_309 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_302, x_308, x_3, x_4, x_5, x_6, x_307);
x_310 = lean_ctor_get(x_309, 1);
lean_inc(x_310);
lean_dec_ref(x_309);
x_189 = x_3;
x_190 = x_4;
x_191 = x_5;
x_192 = x_6;
x_193 = x_310;
goto block_199;
}
}
block_256:
{
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_228);
lean_dec(x_1);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = lean_box(x_2);
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_233;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_232);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_236 = lean_ctor_get(x_230, 1);
lean_inc(x_236);
lean_dec_ref(x_230);
x_237 = lean_ctor_get(x_231, 0);
lean_inc(x_237);
lean_dec(x_231);
x_238 = l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___redArg(x_1, x_228, x_236);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_unbox(x_239);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; 
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_dec_ref(x_238);
x_242 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_237, x_228, x_241);
lean_dec(x_228);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_244 = x_242;
} else {
 lean_dec_ref(x_242);
 x_244 = lean_box(0);
}
x_245 = 1;
x_246 = lean_box(x_245);
if (lean_is_scalar(x_244)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_244;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_243);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_237);
lean_dec(x_228);
lean_dec(x_1);
x_248 = lean_ctor_get(x_238, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_249 = x_238;
} else {
 lean_dec_ref(x_238);
 x_249 = lean_box(0);
}
x_250 = lean_box(x_225);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
return x_251;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_228);
lean_dec(x_1);
x_252 = lean_ctor_get(x_230, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_230, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_254 = x_230;
} else {
 lean_dec_ref(x_230);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
block_270:
{
if (x_265 == 0)
{
if (lean_obj_tag(x_262) == 0)
{
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_210);
x_226 = x_257;
x_227 = x_259;
x_228 = x_260;
x_229 = x_264;
x_230 = x_261;
goto block_256;
}
else
{
lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_262, 0);
lean_inc(x_266);
lean_dec_ref(x_262);
x_267 = lean_nat_dec_eq(x_263, x_266);
lean_dec(x_266);
lean_dec(x_263);
if (x_267 == 0)
{
lean_dec(x_210);
x_226 = x_257;
x_227 = x_259;
x_228 = x_260;
x_229 = x_264;
x_230 = x_261;
goto block_256;
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_264);
lean_dec_ref(x_261);
lean_dec(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_257);
lean_dec(x_1);
x_268 = lean_box(x_2);
if (lean_is_scalar(x_210)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_210;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_258);
return x_269;
}
}
}
else
{
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_210);
x_226 = x_257;
x_227 = x_259;
x_228 = x_260;
x_229 = x_264;
x_230 = x_261;
goto block_256;
}
}
block_283:
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_box(0);
lean_inc(x_274);
lean_inc_ref(x_273);
lean_inc(x_272);
lean_inc_ref(x_271);
x_277 = l_Lean_Meta_synthInstance_x3f(x_187, x_276, x_271, x_272, x_273, x_274, x_275);
if (lean_obj_tag(x_277) == 0)
{
lean_dec(x_210);
x_226 = x_273;
x_227 = x_271;
x_228 = x_272;
x_229 = x_274;
x_230 = x_277;
goto block_256;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
x_280 = l_Lean_Meta_trySynthInstance___closed__0;
x_281 = l_Lean_Exception_isInterrupt(x_278);
if (x_281 == 0)
{
uint8_t x_282; 
x_282 = l_Lean_Exception_isRuntime(x_278);
x_257 = x_273;
x_258 = x_279;
x_259 = x_271;
x_260 = x_272;
x_261 = x_277;
x_262 = x_278;
x_263 = x_280;
x_264 = x_274;
x_265 = x_282;
goto block_270;
}
else
{
x_257 = x_273;
x_258 = x_279;
x_259 = x_271;
x_260 = x_272;
x_261 = x_277;
x_262 = x_278;
x_263 = x_280;
x_264 = x_274;
x_265 = x_281;
goto block_270;
}
}
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec_ref(x_187);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_311 = lean_ctor_get(x_203, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_203, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_313 = x_203;
} else {
 lean_dec_ref(x_203);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
block_199:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = l_Lean_Meta_recordSynthPendingFailure(x_187, x_189, x_190, x_191, x_192, x_193);
lean_dec(x_192);
lean_dec_ref(x_191);
lean_dec(x_190);
lean_dec_ref(x_189);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_196 = x_194;
} else {
 lean_dec_ref(x_194);
 x_196 = lean_box(0);
}
x_197 = lean_box(x_2);
if (lean_is_scalar(x_196)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_196;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_195);
return x_198;
}
}
}
else
{
uint8_t x_315; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_315 = !lean_is_exclusive(x_8);
if (x_315 == 0)
{
return x_8;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_8, 0);
x_317 = lean_ctor_get(x_8, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_8);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
}
LEAN_EXPORT lean_object* lean_synth_pending(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_ctor_get(x_4, 3);
x_12 = lean_ctor_get(x_4, 4);
x_13 = lean_ctor_get(x_4, 5);
x_14 = lean_ctor_get(x_4, 6);
x_15 = lean_ctor_get(x_4, 7);
x_16 = lean_ctor_get(x_4, 8);
x_17 = lean_ctor_get(x_4, 9);
x_18 = lean_ctor_get(x_4, 10);
x_19 = lean_ctor_get(x_4, 11);
x_20 = lean_ctor_get(x_4, 12);
x_21 = lean_nat_dec_eq(x_11, x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_box(x_21);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___boxed), 7, 2);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
lean_ctor_set(x_4, 3, x_25);
x_26 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_23, x_2, x_3, x_4, x_5, x_6);
return x_26;
}
else
{
lean_object* x_27; 
lean_free_object(x_4);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_27 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_withIncRecDepth___at___Lean_Meta_transformWithCache_visit___at___Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0_spec__0_spec__9_spec__9___redArg(x_13, x_6);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
x_30 = lean_ctor_get(x_4, 2);
x_31 = lean_ctor_get(x_4, 3);
x_32 = lean_ctor_get(x_4, 4);
x_33 = lean_ctor_get(x_4, 5);
x_34 = lean_ctor_get(x_4, 6);
x_35 = lean_ctor_get(x_4, 7);
x_36 = lean_ctor_get(x_4, 8);
x_37 = lean_ctor_get(x_4, 9);
x_38 = lean_ctor_get(x_4, 10);
x_39 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_40 = lean_ctor_get(x_4, 11);
x_41 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_42 = lean_ctor_get(x_4, 12);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_43 = lean_nat_dec_eq(x_31, x_32);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_box(x_43);
lean_inc(x_1);
x_45 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___boxed), 7, 2);
lean_closure_set(x_45, 0, x_1);
lean_closure_set(x_45, 1, x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_31, x_46);
lean_dec(x_31);
x_48 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_48, 0, x_28);
lean_ctor_set(x_48, 1, x_29);
lean_ctor_set(x_48, 2, x_30);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 4, x_32);
lean_ctor_set(x_48, 5, x_33);
lean_ctor_set(x_48, 6, x_34);
lean_ctor_set(x_48, 7, x_35);
lean_ctor_set(x_48, 8, x_36);
lean_ctor_set(x_48, 9, x_37);
lean_ctor_set(x_48, 10, x_38);
lean_ctor_set(x_48, 11, x_40);
lean_ctor_set(x_48, 12, x_42);
lean_ctor_set_uint8(x_48, sizeof(void*)*13, x_39);
lean_ctor_set_uint8(x_48, sizeof(void*)*13 + 1, x_41);
x_49 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_45, x_2, x_3, x_48, x_5, x_6);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec_ref(x_42);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_50 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_withIncRecDepth___at___Lean_Meta_transformWithCache_visit___at___Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0_spec__0_spec__9_spec__9___redArg(x_33, x_6);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_5_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_2 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_5_;
x_2 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_;
x_2 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SynthInstance", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_2 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_2 = l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_SynthInstance___hyg_9910_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(9910u);
x_2 = l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_9910_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__2;
x_3 = 0;
x_4 = l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_SynthInstance___hyg_9910_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_Meta_SynthInstance_newSubgoal___closed__0;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__4;
x_11 = 1;
x_12 = l_Lean_registerTraceClass(x_10, x_11, x_4, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__1;
x_15 = l_Lean_registerTraceClass(x_14, x_11, x_4, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__1;
x_18 = l_Lean_registerTraceClass(x_17, x_11, x_4, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Meta_SynthInstance_resume___lam__3___closed__1;
x_21 = l_Lean_registerTraceClass(x_20, x_11, x_4, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__2;
x_24 = l_Lean_registerTraceClass(x_23, x_3, x_4, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__1;
x_27 = l_Lean_registerTraceClass(x_26, x_3, x_4, x_25);
return x_27;
}
else
{
return x_24;
}
}
else
{
return x_21;
}
}
else
{
return x_18;
}
}
else
{
return x_15;
}
}
else
{
return x_12;
}
}
else
{
return x_8;
}
}
else
{
return x_5;
}
}
}
lean_object* initialize_Init_Data_Array_InsertionSort(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Instances(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AbstractMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Profile(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_InsertionSort(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Instances(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AbstractMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Profile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_5_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_5_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_5_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_5_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_5_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_5_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_5_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_5_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_5_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_5_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_5_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_5_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_5_);
l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_SynthInstance___hyg_5_ = _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_SynthInstance___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_SynthInstance___hyg_5_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_synthInstance_maxHeartbeats = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_synthInstance_maxHeartbeats);
lean_dec_ref(res);
}l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_44_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_44_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_44_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_44_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_44_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_44_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_44_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_44_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_44_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_44_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_44_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_44_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_44_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_44_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_44_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_44_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_synthInstance_maxSize = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_synthInstance_maxSize);
lean_dec_ref(res);
}l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_83_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_83_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_83_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_83_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_83_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_83_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_83_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_83_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_83_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_83_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_83_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_83_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_83_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_83_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_83_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_83_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_83_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_83_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_83_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_83_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_83_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_83_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_synthInstance_canonInstances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_synthInstance_canonInstances);
lean_dec_ref(res);
}l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__0 = _init_l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__0);
l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__0 = _init_l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__0);
l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__1 = _init_l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__1);
l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__2 = _init_l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__2);
l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__3 = _init_l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__3);
l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__4 = _init_l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedInstance___closed__4);
l_Lean_Meta_SynthInstance_instInhabitedInstance = _init_l_Lean_Meta_SynthInstance_instInhabitedInstance();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedInstance);
l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__0 = _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__0);
l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1 = _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1);
l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2 = _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2);
l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3 = _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3);
l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4 = _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4);
l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__5 = _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__5);
l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__6 = _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__6);
l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__7 = _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__7);
l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8 = _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8);
l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__9 = _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__9();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__9);
l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode = _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode);
l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__0 = _init_l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__0);
l_Lean_Meta_SynthInstance_instInhabitedConsumerNode = _init_l_Lean_Meta_SynthInstance_instInhabitedConsumerNode();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedConsumerNode);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__0 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__0);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__1 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__1);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__2 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__2);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__3 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__3);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__4 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__4);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__5 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__5);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__6 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__6);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__7 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__7);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__8 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__8();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__8);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__9 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__9();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__9);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__10 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__10();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__10);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM);
l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__0 = _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__0);
l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1 = _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1);
l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__0 = _init_l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__0);
l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__1 = _init_l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__1);
l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__2 = _init_l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__2);
l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__3 = _init_l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__3);
l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__4 = _init_l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKey___redArg___lam__2___closed__4);
l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__0 = _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__0);
l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1 = _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1);
l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__2 = _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__2);
l_Lean_Meta_SynthInstance_instInhabitedAnswer = _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedAnswer);
l_Lean_Meta_SynthInstance_checkSystem___redArg___closed__0 = _init_l_Lean_Meta_SynthInstance_checkSystem___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_checkSystem___redArg___closed__0);
l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___closed__0 = _init_l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___closed__0);
l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___closed__1 = _init_l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedSynthM___lam__0___closed__1);
l_panic___at___Lean_Meta_SynthInstance_getInstances_spec__2___closed__0 = _init_l_panic___at___Lean_Meta_SynthInstance_getInstances_spec__2___closed__0();
lean_mark_persistent(l_panic___at___Lean_Meta_SynthInstance_getInstances_spec__2___closed__0);
l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__0);
l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__1);
l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__2 = _init_l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__2);
l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__3 = _init_l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5_spec__5___closed__3);
l_Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5___closed__0 = _init_l_Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5___closed__0();
lean_mark_persistent(l_Array_filterMapM___at___Lean_Meta_SynthInstance_getInstances_spec__5___closed__0);
l_Lean_Meta_SynthInstance_getInstances___lam__0___closed__0 = _init_l_Lean_Meta_SynthInstance_getInstances___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lam__0___closed__0);
l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__0 = _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__0);
l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__1 = _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__1);
l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2 = _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__2);
l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__3 = _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__3);
l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__4 = _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__4);
l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__5 = _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__5);
l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__6 = _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__6);
l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__7 = _init_l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lam__1___closed__7);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__0 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__0);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1_spec__2___redArg___closed__2);
l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__0 = _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__0();
l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__1 = _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__1);
l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__2 = _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__2);
l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__3 = _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__3();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__3);
l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__4 = _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__4();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__4);
l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__5 = _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__5();
l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__6 = _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__6();
l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__7 = _init_l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__7();
lean_mark_persistent(l_Lean_withTraceNode___at___Lean_withTraceNode_x27___at___Lean_Meta_SynthInstance_newSubgoal_spec__1_spec__1___redArg___closed__7);
l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__0 = _init_l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__0);
l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__1 = _init_l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__1);
l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__2 = _init_l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__2);
l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__3 = _init_l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__3);
l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__4 = _init_l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__4);
l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__5 = _init_l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___lam__0___closed__5);
l_Lean_Meta_SynthInstance_newSubgoal___closed__0 = _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___closed__0);
l_panic___at___Lean_Meta_SynthInstance_getEntry_spec__0___closed__0 = _init_l_panic___at___Lean_Meta_SynthInstance_getEntry_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_Meta_SynthInstance_getEntry_spec__0___closed__0);
l_Lean_Meta_SynthInstance_getEntry___closed__0 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__0);
l_Lean_Meta_SynthInstance_getEntry___closed__1 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__1);
l_Lean_Meta_SynthInstance_getEntry___closed__2 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__2);
l_Lean_Meta_SynthInstance_getSubgoals___closed__0 = _init_l_Lean_Meta_SynthInstance_getSubgoals___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getSubgoals___closed__0);
l_Lean_Meta_SynthInstance_getSubgoals___closed__1 = _init_l_Lean_Meta_SynthInstance_getSubgoals___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getSubgoals___closed__1);
l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__0 = _init_l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__0);
l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__1 = _init_l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__1);
l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__2 = _init_l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__2);
l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__3 = _init_l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lam__1___closed__3);
l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__0 = _init_l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__0);
l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__1 = _init_l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lam__3___closed__1);
l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg___closed__0 = _init_l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_SynthInstance_wakeUp_spec__0___redArg___closed__0);
l_Lean_Meta_SynthInstance_wakeUp___closed__0 = _init_l_Lean_Meta_SynthInstance_wakeUp___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___closed__0);
l_Lean_Meta_SynthInstance_wakeUp___closed__1 = _init_l_Lean_Meta_SynthInstance_wakeUp___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__0 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__0);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__2 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__2);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__3 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__3);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__4 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__4);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__5 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lam__0___closed__5);
l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__0 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__0);
l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__1 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__1);
l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__2 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__2);
l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__3 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__1___closed__3);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__0 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__0);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__1 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__1);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__2 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__2);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__3 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__3);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__4 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__4);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__5 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__5);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__6 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__6);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__7 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__7);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__8 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__8();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__8);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__9 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__9();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__9);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__10 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__10();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__10);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__11 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__11();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__11);
l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__12 = _init_l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__12();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lam__2___closed__12);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__0 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__0);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__2 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__2);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__3 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__3);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__4 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__4);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__5 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__5);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__6 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__6();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__0___closed__6);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___closed__0 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___closed__0();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___closed__0);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lam__1___closed__1);
l_Lean_Meta_SynthInstance_generate___lam__0___closed__0 = _init_l_Lean_Meta_SynthInstance_generate___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lam__0___closed__0);
l_Lean_Meta_SynthInstance_generate___lam__0___closed__1 = _init_l_Lean_Meta_SynthInstance_generate___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lam__0___closed__1);
l_Lean_Meta_SynthInstance_generate___lam__0___closed__2 = _init_l_Lean_Meta_SynthInstance_generate___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lam__0___closed__2);
l_Lean_Meta_SynthInstance_generate___lam__0___closed__3 = _init_l_Lean_Meta_SynthInstance_generate___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lam__0___closed__3);
l_Lean_Meta_SynthInstance_generate___lam__1___closed__0 = _init_l_Lean_Meta_SynthInstance_generate___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lam__1___closed__0);
l_Lean_Meta_SynthInstance_generate___closed__0 = _init_l_Lean_Meta_SynthInstance_generate___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__0);
l_Lean_Meta_SynthInstance_getNextToResume___redArg___closed__0 = _init_l_Lean_Meta_SynthInstance_getNextToResume___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getNextToResume___redArg___closed__0);
l_Lean_Meta_SynthInstance_resume___lam__0___closed__0 = _init_l_Lean_Meta_SynthInstance_resume___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lam__0___closed__0);
l_Lean_Meta_SynthInstance_resume___lam__0___closed__1 = _init_l_Lean_Meta_SynthInstance_resume___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lam__0___closed__1);
l_Lean_Meta_SynthInstance_resume___lam__0___closed__2 = _init_l_Lean_Meta_SynthInstance_resume___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lam__0___closed__2);
l_Lean_Meta_SynthInstance_resume___lam__0___closed__3 = _init_l_Lean_Meta_SynthInstance_resume___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lam__0___closed__3);
l_Lean_Meta_SynthInstance_resume___lam__0___closed__4 = _init_l_Lean_Meta_SynthInstance_resume___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lam__0___closed__4);
l_Lean_Meta_SynthInstance_resume___lam__0___closed__5 = _init_l_Lean_Meta_SynthInstance_resume___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lam__0___closed__5);
l_Lean_Meta_SynthInstance_resume___lam__3___closed__0 = _init_l_Lean_Meta_SynthInstance_resume___lam__3___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lam__3___closed__0);
l_Lean_Meta_SynthInstance_resume___lam__3___closed__1 = _init_l_Lean_Meta_SynthInstance_resume___lam__3___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lam__3___closed__1);
l_Lean_Meta_SynthInstance_resume___closed__0 = _init_l_Lean_Meta_SynthInstance_resume___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__0);
l_Lean_Meta_SynthInstance_resume___closed__1 = _init_l_Lean_Meta_SynthInstance_resume___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__1);
l_Lean_Meta_SynthInstance_resume___closed__2 = _init_l_Lean_Meta_SynthInstance_resume___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__2);
l_Lean_Meta_SynthInstance_main___lam__0___closed__0 = _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lam__0___closed__0);
l_Lean_Meta_SynthInstance_main___lam__0___closed__1 = _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lam__0___closed__1);
l_Lean_Meta_SynthInstance_main___lam__0___closed__2 = _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lam__0___closed__2);
l_Lean_Meta_SynthInstance_main___lam__0___closed__3 = _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lam__0___closed__3);
l_Lean_Meta_SynthInstance_main___lam__0___closed__4 = _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lam__0___closed__4);
l_Lean_Meta_SynthInstance_main___lam__0___closed__5 = _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lam__0___closed__5);
l_Lean_Meta_SynthInstance_main___lam__0___closed__6 = _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lam__0___closed__6);
l_Lean_Meta_SynthInstance_main___lam__0___closed__7 = _init_l_Lean_Meta_SynthInstance_main___lam__0___closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lam__0___closed__7);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__0 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__0();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__0);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lam__0___closed__0 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lam__0___closed__0);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__0 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__0();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__0);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__2 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__2);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__3 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__3);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__4 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__4();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_assignOutParams___closed__4);
l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__0);
l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult_spec__0___redArg___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg___closed__0 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_cacheResult___redArg___closed__0);
l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__0 = _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__0();
lean_mark_persistent(l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__0);
l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__1 = _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__1();
lean_mark_persistent(l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__1);
l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__2 = _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__2();
lean_mark_persistent(l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__2);
l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__3 = _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__3();
lean_mark_persistent(l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__3);
l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__4 = _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__4();
lean_mark_persistent(l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__4);
l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__5 = _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__5();
lean_mark_persistent(l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__5);
l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__6 = _init_l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__6();
lean_mark_persistent(l_Lean_Meta_synthInstanceCore_x3f___lam__2___closed__6);
l_Lean_Meta_synthInstanceCore_x3f___closed__0 = _init_l_Lean_Meta_synthInstanceCore_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_synthInstanceCore_x3f___closed__0);
l_Lean_Meta_synthInstance_x3f___closed__0 = _init_l_Lean_Meta_synthInstance_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__0);
l_Lean_Meta_trySynthInstance___closed__0 = _init_l_Lean_Meta_trySynthInstance___closed__0();
lean_mark_persistent(l_Lean_Meta_trySynthInstance___closed__0);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__0 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__0);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__2 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__2);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__3 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__3);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__4 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__4);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__5 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__5);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__6 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__6();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lam__0___closed__6);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_SynthInstance___hyg_9910_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_SynthInstance___hyg_9910_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_SynthInstance___hyg_9910_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_SynthInstance___hyg_9910_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_SynthInstance___hyg_9910_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_SynthInstance___hyg_9910_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_SynthInstance___hyg_9910_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_SynthInstance___hyg_9910_);
l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_SynthInstance___hyg_9910_);
l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_SynthInstance___hyg_9910_);
l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_SynthInstance___hyg_9910_);
l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_SynthInstance___hyg_9910_);
l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_SynthInstance___hyg_9910_ = _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_SynthInstance___hyg_9910_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_SynthInstance___hyg_9910_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_9910_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

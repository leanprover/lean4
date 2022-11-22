// Lean compiler output
// Module: Lean.Meta.SynthInstance
// Imports: Init Lean.Meta.Basic Lean.Meta.Instances Lean.Meta.AbstractMVars Lean.Meta.WHNF Lean.Meta.Check Lean.Util.Profile
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
lean_object* l_Lean_exceptOptionEmoji___rarg(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_SynthInstance_tryResolve___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_Lean_Meta_SynthInstance_main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getMaxHeartbeats___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l___private_Lean_Data_HashMap_0__Lean_HashMapImp_mkIdx(lean_object*, uint64_t, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__3;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2___closed__1;
uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__2;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkGeneratorNode_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMap_insert___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_newSubgoal___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_State_resumeStack___default;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_toLOption___rarg(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__12;
static lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_generate___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2___closed__2;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_addAnswer___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_State_emap___default;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__3;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___closed__1;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_synthInstance_x3f___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__4;
lean_object* l_Lean_Level_succ___override(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___closed__1;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_getGlobalInstancesIndex___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__6;
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult(lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__4;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_synthInstance_x3f___spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__2;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_SynthInstance_State_tableEntries___default___spec__1___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkMaxHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_SynthInstance_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__2;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_synthInstance_x3f___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__3;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_ptrEqList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_tryResolve___spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_get___at_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__11;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__9;
lean_object* l_Lean_HashMapImp_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__1(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_tryResolve___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_getSubgoalsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_SynthInstance_resume___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__5;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_maxSize;
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_SynthInstance_getInstances___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_hasUnusedArguments(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__7;
static lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__3;
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_hasUnusedArguments___boxed(lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_tryResolve___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_crossEmoji;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_generate___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at_Lean_Meta_SynthInstance_tryResolve___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_wakeUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97_(lean_object*);
LEAN_EXPORT lean_object* l_StateT_bind___at_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__10(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__2;
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_processPostponed___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SynthInstance_Waiter_isRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_wakeUp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__3;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___boxed(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_consume___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_tryResolve___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_synthInstance_x3f___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__5;
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Meta_SynthInstance_getInstances___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__12;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__4;
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__1;
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mapMetaM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__9;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode;
extern lean_object* l_Lean_Meta_isDefEqStuckExceptionId;
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_is_out_param(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__6;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__4;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lambda__2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_TableEntry_answers___default;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2;
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__10;
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2;
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___closed__6;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedConsumerNode;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_newSubgoal___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__6;
static lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_trySynthInstance___closed__1;
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_SynthInstance_getInstances___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_addAnswer___spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__3;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__5;
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__3;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__11;
lean_object* l_Lean_Meta_getErasedInstances___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
static lean_object* l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___closed__1;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__2;
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_Lean_Meta_SynthInstance_tryResolve___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isAssigned___spec__1(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__7(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__3;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_SynthInstance_State_tableEntries___default___spec__1(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___lambda__5___closed__2;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221_(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___boxed(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_generate___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_State_generatorStack___default;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_addAnswer___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_generate___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_synth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__2;
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Meta_SynthInstance_addAnswer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__6;
uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_State_result_x3f___default;
lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__2;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Meta_SynthInstance_getInstances___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___boxed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__2;
lean_object* l_Lean_Core_checkMaxHeartbeatsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_SynthInstance_getInstances___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___closed__3;
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_State_tableEntries___default;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__2;
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_wakeUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__7;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_SynthInstance_isNewAnswer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__4;
extern lean_object* l_Id_instMonadId;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__1;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lambda__1___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__10;
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__4;
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__3;
extern lean_object* l_Lean_checkEmoji;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__2;
static lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM;
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__3;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_Waiter_isRoot___boxed(lean_object*);
static lean_object* l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_collectForwardDeps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_wakeUp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___boxed(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__3;
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_SynthInstance_getInstances___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_isNewAnswer___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_SynthInstance_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getMaxHeartbeats(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_synth_pending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__5;
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonadStateT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__3;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__2;
lean_object* l_Lean_profileitIOUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___closed__1;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_synthInstance_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_synthInstance_x3f___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_State_nextIdx___default;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2;
static lean_object* l_Lean_Meta_SynthInstance_generate___lambda__4___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_tryResolve___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__7;
static lean_object* l_Lean_Meta_SynthInstance_generate___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___lambda__5___closed__3;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_addAnswer___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_bind___at_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__4___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_processPostponed___spec__2___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___closed__2;
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
lean_object* l_Lean_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_SynthInstance_tryResolve___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_synthInstance_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__9;
static lean_object* l_Lean_Meta_SynthInstance_resume___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Meta_SynthInstance_addAnswer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedAnswer;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__1;
uint8_t lean_has_out_params(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_Lean_Meta_SynthInstance_tryResolve___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__2;
static lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__3;
lean_object* l_panic___at___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_maxHeartbeats;
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__2;
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkMaxHeartbeats___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_checkMaxHeartbeats___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_inferTCGoalsRLAttr;
static lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__5;
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("synthInstance", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maxHeartbeats", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maximum amount of heartbeats per typeclass resolution problem. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit", 147);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(20000u);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__6;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__9;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_6____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maxSize", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maximum number of instances used to construct a solution in the type class instance synthesis procedure", 103);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(128u);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__4;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__5;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_6____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__1() {
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
x_2 = l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__1;
x_3 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("infer_tc_goals_rl", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("SynthInstance", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inferTCGoalsRLAttr", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_3 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__3;
x_4 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instruct type class resolution procedure to solve goals from right to left for this instance", 92);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__2;
x_3 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__6;
x_4 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__7;
x_5 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__5;
x_6 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_inferTCGoalsRLAttr;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4;
x_3 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__5;
x_4 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__6;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1;
x_2 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__7;
x_3 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
return x_5;
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
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1;
x_3 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__7;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedConsumerNode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__1;
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
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_State_nextIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_State_emap___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_StateT_get___at_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_StateT_bind___at_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_StateT_bind___at_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_StateT_bind___at_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___spec__2___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 3, x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
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
x_12 = lean_apply_1(x_1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateT_get___at_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___spec__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lambda__2), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__1;
x_2 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__2;
x_3 = lean_alloc_closure((void*)(l_StateT_bind___at_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___spec__2___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__3;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_instMonadId;
x_2 = l_StateT_instMonadStateT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2___closed__1;
x_2 = l_instInhabitedBool;
x_3 = lean_box(x_2);
x_4 = l_instInhabited___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2___closed__2;
x_4 = lean_panic_fn(x_3, x_1);
x_5 = lean_apply_1(x_4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.MetavarContext", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.isLevelMVarAssignable", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown universe metavariable", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__1;
x_2 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(388u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__4;
x_7 = l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2(x_6, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_tc", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
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
lean_dec(x_23);
lean_inc(x_22);
x_26 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_22, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; size_t x_29; size_t x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ptr_addr(x_21);
lean_dec(x_21);
x_30 = lean_ptr_addr(x_24);
x_31 = lean_usize_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_22);
lean_dec(x_1);
x_32 = l_Lean_mkLevelMax_x27(x_24, x_28);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
size_t x_33; size_t x_34; uint8_t x_35; 
x_33 = lean_ptr_addr(x_22);
lean_dec(x_22);
x_34 = lean_ptr_addr(x_28);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_1);
x_36 = l_Lean_mkLevelMax_x27(x_24, x_28);
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_simpLevelMax_x27(x_24, x_28, x_1);
lean_dec(x_1);
lean_dec(x_28);
lean_dec(x_24);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_40 = lean_ptr_addr(x_21);
lean_dec(x_21);
x_41 = lean_ptr_addr(x_24);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_22);
lean_dec(x_1);
x_43 = l_Lean_mkLevelMax_x27(x_24, x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
else
{
size_t x_45; size_t x_46; uint8_t x_47; 
x_45 = lean_ptr_addr(x_22);
lean_dec(x_22);
x_46 = lean_ptr_addr(x_38);
x_47 = lean_usize_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_48 = l_Lean_mkLevelMax_x27(x_24, x_38);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_simpLevelMax_x27(x_24, x_38, x_1);
lean_dec(x_1);
lean_dec(x_38);
lean_dec(x_24);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_39);
return x_51;
}
}
}
}
case 3:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_inc(x_52);
x_54 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_52, x_2);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_53);
x_57 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_53, x_56);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; size_t x_60; size_t x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_61 = lean_ptr_addr(x_55);
x_62 = lean_usize_dec_eq(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_53);
lean_dec(x_1);
x_63 = l_Lean_mkLevelIMax_x27(x_55, x_59);
lean_ctor_set(x_57, 0, x_63);
return x_57;
}
else
{
size_t x_64; size_t x_65; uint8_t x_66; 
x_64 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_65 = lean_ptr_addr(x_59);
x_66 = lean_usize_dec_eq(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_1);
x_67 = l_Lean_mkLevelIMax_x27(x_55, x_59);
lean_ctor_set(x_57, 0, x_67);
return x_57;
}
else
{
lean_object* x_68; 
x_68 = l_Lean_simpLevelIMax_x27(x_55, x_59, x_1);
lean_dec(x_1);
lean_ctor_set(x_57, 0, x_68);
return x_57;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_57, 0);
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_57);
x_71 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_72 = lean_ptr_addr(x_55);
x_73 = lean_usize_dec_eq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_53);
lean_dec(x_1);
x_74 = l_Lean_mkLevelIMax_x27(x_55, x_69);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
return x_75;
}
else
{
size_t x_76; size_t x_77; uint8_t x_78; 
x_76 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_77 = lean_ptr_addr(x_69);
x_78 = lean_usize_dec_eq(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_1);
x_79 = l_Lean_mkLevelIMax_x27(x_55, x_69);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_70);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = l_Lean_simpLevelIMax_x27(x_55, x_69, x_1);
lean_dec(x_1);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_70);
return x_82;
}
}
}
}
case 5:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_1, 0);
lean_inc(x_83);
lean_inc(x_83);
x_84 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1(x_83, x_2);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
uint8_t x_87; 
lean_dec(x_83);
x_87 = !lean_is_exclusive(x_84);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_84, 0);
lean_dec(x_88);
lean_ctor_set(x_84, 0, x_1);
return x_84;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_dec(x_84);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_84);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_84, 1);
x_93 = lean_ctor_get(x_84, 0);
lean_dec(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_inc(x_83);
lean_inc(x_94);
x_95 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__1(x_94, x_83);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
x_97 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2;
lean_inc(x_96);
x_98 = l_Lean_Name_num___override(x_97, x_96);
x_99 = l_Lean_Level_param___override(x_98);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_96, x_100);
lean_dec(x_96);
lean_inc(x_99);
x_102 = l_Lean_HashMap_insert___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__3(x_94, x_83, x_99);
x_103 = lean_ctor_get(x_92, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_92, 3);
lean_inc(x_104);
lean_dec(x_92);
x_105 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_102);
lean_ctor_set(x_105, 2, x_103);
lean_ctor_set(x_105, 3, x_104);
lean_ctor_set(x_84, 1, x_105);
lean_ctor_set(x_84, 0, x_99);
return x_84;
}
else
{
lean_object* x_106; 
lean_dec(x_94);
lean_dec(x_83);
x_106 = lean_ctor_get(x_95, 0);
lean_inc(x_106);
lean_dec(x_95);
lean_ctor_set(x_84, 0, x_106);
return x_84;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_84, 1);
lean_inc(x_107);
lean_dec(x_84);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_inc(x_83);
lean_inc(x_108);
x_109 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__1(x_108, x_83);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
x_111 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2;
lean_inc(x_110);
x_112 = l_Lean_Name_num___override(x_111, x_110);
x_113 = l_Lean_Level_param___override(x_112);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_nat_add(x_110, x_114);
lean_dec(x_110);
lean_inc(x_113);
x_116 = l_Lean_HashMap_insert___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__3(x_108, x_83, x_113);
x_117 = lean_ctor_get(x_107, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_107, 3);
lean_inc(x_118);
lean_dec(x_107);
x_119 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set(x_119, 2, x_117);
lean_ctor_set(x_119, 3, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_108);
lean_dec(x_83);
x_121 = lean_ctor_get(x_109, 0);
lean_inc(x_121);
lean_dec(x_109);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_107);
return x_122;
}
}
}
}
default: 
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_1);
lean_ctor_set(x_123, 1, x_2);
return x_123;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
lean_inc(x_3);
x_4 = l_Lean_MetavarContext_getDecl(x_3, x_1);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_reverse___rarg(x_2);
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
lean_dec(x_9);
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
lean_dec(x_15);
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
x_6 = l_Lean_MVarId_isAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___spec__1(x_5, x_2);
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
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_inc(x_5);
lean_inc(x_16);
x_17 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(x_16, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2;
lean_inc(x_18);
x_20 = l_Lean_Name_num___override(x_19, x_18);
x_21 = l_Lean_Expr_fvar___override(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_18, x_22);
lean_dec(x_18);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_21);
x_25 = l_Lean_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(x_16, x_5, x_21);
x_26 = lean_ctor_get(x_14, 3);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_6, 0, x_21);
return x_6;
}
else
{
lean_object* x_28; 
lean_dec(x_16);
lean_dec(x_5);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
lean_ctor_set(x_6, 0, x_28);
return x_6;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_inc(x_5);
lean_inc(x_30);
x_31 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(x_30, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2;
lean_inc(x_32);
x_34 = l_Lean_Name_num___override(x_33, x_32);
x_35 = l_Lean_Expr_fvar___override(x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_32, x_36);
lean_dec(x_32);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_35);
x_39 = l_Lean_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(x_30, x_5, x_35);
x_40 = lean_ctor_get(x_29, 3);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_39);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
lean_dec(x_5);
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_29);
return x_44;
}
}
}
}
case 3:
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
lean_inc(x_45);
x_46 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_45, x_2);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; size_t x_49; size_t x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ptr_addr(x_45);
lean_dec(x_45);
x_50 = lean_ptr_addr(x_48);
x_51 = lean_usize_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_1);
x_52 = l_Lean_Expr_sort___override(x_48);
lean_ctor_set(x_46, 0, x_52);
return x_46;
}
else
{
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_1);
return x_46;
}
}
else
{
lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_46, 0);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_46);
x_55 = lean_ptr_addr(x_45);
lean_dec(x_45);
x_56 = lean_ptr_addr(x_53);
x_57 = lean_usize_dec_eq(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_58 = l_Lean_Expr_sort___override(x_53);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
else
{
lean_object* x_60; 
lean_dec(x_53);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
}
}
case 4:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
x_63 = lean_box(0);
lean_inc(x_62);
x_64 = l_List_mapM_loop___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___spec__2(x_62, x_63, x_2);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = l_ptrEqList___rarg(x_62, x_66);
lean_dec(x_62);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_1);
x_68 = l_Lean_Expr_const___override(x_61, x_66);
lean_ctor_set(x_64, 0, x_68);
return x_64;
}
else
{
lean_dec(x_66);
lean_dec(x_61);
lean_ctor_set(x_64, 0, x_1);
return x_64;
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_64);
x_71 = l_ptrEqList___rarg(x_62, x_69);
lean_dec(x_62);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_72 = l_Lean_Expr_const___override(x_61, x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_69);
lean_dec(x_61);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
}
}
case 5:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_75 = lean_ctor_get(x_1, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 1);
lean_inc(x_76);
lean_inc(x_75);
x_77 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_75, x_2);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_76);
x_80 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_76, x_79);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; size_t x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ptr_addr(x_75);
lean_dec(x_75);
x_84 = lean_ptr_addr(x_78);
x_85 = lean_usize_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_76);
lean_dec(x_1);
x_86 = l_Lean_Expr_app___override(x_78, x_82);
lean_ctor_set(x_80, 0, x_86);
return x_80;
}
else
{
size_t x_87; size_t x_88; uint8_t x_89; 
x_87 = lean_ptr_addr(x_76);
lean_dec(x_76);
x_88 = lean_ptr_addr(x_82);
x_89 = lean_usize_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_1);
x_90 = l_Lean_Expr_app___override(x_78, x_82);
lean_ctor_set(x_80, 0, x_90);
return x_80;
}
else
{
lean_dec(x_82);
lean_dec(x_78);
lean_ctor_set(x_80, 0, x_1);
return x_80;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; size_t x_93; size_t x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_80, 0);
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_80);
x_93 = lean_ptr_addr(x_75);
lean_dec(x_75);
x_94 = lean_ptr_addr(x_78);
x_95 = lean_usize_dec_eq(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_76);
lean_dec(x_1);
x_96 = l_Lean_Expr_app___override(x_78, x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_92);
return x_97;
}
else
{
size_t x_98; size_t x_99; uint8_t x_100; 
x_98 = lean_ptr_addr(x_76);
lean_dec(x_76);
x_99 = lean_ptr_addr(x_91);
x_100 = lean_usize_dec_eq(x_98, x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_1);
x_101 = l_Lean_Expr_app___override(x_78, x_91);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_92);
return x_102;
}
else
{
lean_object* x_103; 
lean_dec(x_91);
lean_dec(x_78);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_92);
return x_103;
}
}
}
}
case 6:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_104 = lean_ctor_get(x_1, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_1, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_1, 2);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_105);
x_108 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_105, x_2);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_106);
x_111 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_106, x_110);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; size_t x_115; size_t x_116; uint8_t x_117; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
x_114 = l_Lean_Expr_lam___override(x_104, x_105, x_106, x_107);
x_115 = lean_ptr_addr(x_105);
lean_dec(x_105);
x_116 = lean_ptr_addr(x_109);
x_117 = lean_usize_dec_eq(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_114);
lean_dec(x_106);
x_118 = l_Lean_Expr_lam___override(x_104, x_109, x_113, x_107);
lean_ctor_set(x_111, 0, x_118);
return x_111;
}
else
{
size_t x_119; size_t x_120; uint8_t x_121; 
x_119 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_120 = lean_ptr_addr(x_113);
x_121 = lean_usize_dec_eq(x_119, x_120);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_114);
x_122 = l_Lean_Expr_lam___override(x_104, x_109, x_113, x_107);
lean_ctor_set(x_111, 0, x_122);
return x_111;
}
else
{
uint8_t x_123; 
x_123 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_107, x_107);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_114);
x_124 = l_Lean_Expr_lam___override(x_104, x_109, x_113, x_107);
lean_ctor_set(x_111, 0, x_124);
return x_111;
}
else
{
lean_dec(x_113);
lean_dec(x_109);
lean_dec(x_104);
lean_ctor_set(x_111, 0, x_114);
return x_111;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; size_t x_128; size_t x_129; uint8_t x_130; 
x_125 = lean_ctor_get(x_111, 0);
x_126 = lean_ctor_get(x_111, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_111);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
x_127 = l_Lean_Expr_lam___override(x_104, x_105, x_106, x_107);
x_128 = lean_ptr_addr(x_105);
lean_dec(x_105);
x_129 = lean_ptr_addr(x_109);
x_130 = lean_usize_dec_eq(x_128, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_127);
lean_dec(x_106);
x_131 = l_Lean_Expr_lam___override(x_104, x_109, x_125, x_107);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_126);
return x_132;
}
else
{
size_t x_133; size_t x_134; uint8_t x_135; 
x_133 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_134 = lean_ptr_addr(x_125);
x_135 = lean_usize_dec_eq(x_133, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_127);
x_136 = l_Lean_Expr_lam___override(x_104, x_109, x_125, x_107);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_126);
return x_137;
}
else
{
uint8_t x_138; 
x_138 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_107, x_107);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_127);
x_139 = l_Lean_Expr_lam___override(x_104, x_109, x_125, x_107);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_126);
return x_140;
}
else
{
lean_object* x_141; 
lean_dec(x_125);
lean_dec(x_109);
lean_dec(x_104);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_127);
lean_ctor_set(x_141, 1, x_126);
return x_141;
}
}
}
}
}
case 7:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_142 = lean_ctor_get(x_1, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_1, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_1, 2);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_143);
x_146 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_143, x_2);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
lean_inc(x_144);
x_149 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_144, x_148);
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; size_t x_153; size_t x_154; uint8_t x_155; 
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
x_152 = l_Lean_Expr_forallE___override(x_142, x_143, x_144, x_145);
x_153 = lean_ptr_addr(x_143);
lean_dec(x_143);
x_154 = lean_ptr_addr(x_147);
x_155 = lean_usize_dec_eq(x_153, x_154);
if (x_155 == 0)
{
lean_object* x_156; 
lean_dec(x_152);
lean_dec(x_144);
x_156 = l_Lean_Expr_forallE___override(x_142, x_147, x_151, x_145);
lean_ctor_set(x_149, 0, x_156);
return x_149;
}
else
{
size_t x_157; size_t x_158; uint8_t x_159; 
x_157 = lean_ptr_addr(x_144);
lean_dec(x_144);
x_158 = lean_ptr_addr(x_151);
x_159 = lean_usize_dec_eq(x_157, x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_152);
x_160 = l_Lean_Expr_forallE___override(x_142, x_147, x_151, x_145);
lean_ctor_set(x_149, 0, x_160);
return x_149;
}
else
{
uint8_t x_161; 
x_161 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_145, x_145);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_152);
x_162 = l_Lean_Expr_forallE___override(x_142, x_147, x_151, x_145);
lean_ctor_set(x_149, 0, x_162);
return x_149;
}
else
{
lean_dec(x_151);
lean_dec(x_147);
lean_dec(x_142);
lean_ctor_set(x_149, 0, x_152);
return x_149;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; size_t x_166; size_t x_167; uint8_t x_168; 
x_163 = lean_ctor_get(x_149, 0);
x_164 = lean_ctor_get(x_149, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_149);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
x_165 = l_Lean_Expr_forallE___override(x_142, x_143, x_144, x_145);
x_166 = lean_ptr_addr(x_143);
lean_dec(x_143);
x_167 = lean_ptr_addr(x_147);
x_168 = lean_usize_dec_eq(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_165);
lean_dec(x_144);
x_169 = l_Lean_Expr_forallE___override(x_142, x_147, x_163, x_145);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_164);
return x_170;
}
else
{
size_t x_171; size_t x_172; uint8_t x_173; 
x_171 = lean_ptr_addr(x_144);
lean_dec(x_144);
x_172 = lean_ptr_addr(x_163);
x_173 = lean_usize_dec_eq(x_171, x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_165);
x_174 = l_Lean_Expr_forallE___override(x_142, x_147, x_163, x_145);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_164);
return x_175;
}
else
{
uint8_t x_176; 
x_176 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_145, x_145);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_165);
x_177 = l_Lean_Expr_forallE___override(x_142, x_147, x_163, x_145);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_164);
return x_178;
}
else
{
lean_object* x_179; 
lean_dec(x_163);
lean_dec(x_147);
lean_dec(x_142);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_165);
lean_ctor_set(x_179, 1, x_164);
return x_179;
}
}
}
}
}
case 8:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_180 = lean_ctor_get(x_1, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_1, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_1, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_1, 3);
lean_inc(x_183);
x_184 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_inc(x_181);
x_185 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_181, x_2);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
lean_inc(x_182);
x_188 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_182, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
lean_inc(x_183);
x_191 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_183, x_190);
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; size_t x_194; size_t x_195; uint8_t x_196; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = lean_ptr_addr(x_181);
lean_dec(x_181);
x_195 = lean_ptr_addr(x_186);
x_196 = lean_usize_dec_eq(x_194, x_195);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_1);
x_197 = l_Lean_Expr_letE___override(x_180, x_186, x_189, x_193, x_184);
lean_ctor_set(x_191, 0, x_197);
return x_191;
}
else
{
size_t x_198; size_t x_199; uint8_t x_200; 
x_198 = lean_ptr_addr(x_182);
lean_dec(x_182);
x_199 = lean_ptr_addr(x_189);
x_200 = lean_usize_dec_eq(x_198, x_199);
if (x_200 == 0)
{
lean_object* x_201; 
lean_dec(x_183);
lean_dec(x_1);
x_201 = l_Lean_Expr_letE___override(x_180, x_186, x_189, x_193, x_184);
lean_ctor_set(x_191, 0, x_201);
return x_191;
}
else
{
size_t x_202; size_t x_203; uint8_t x_204; 
x_202 = lean_ptr_addr(x_183);
lean_dec(x_183);
x_203 = lean_ptr_addr(x_193);
x_204 = lean_usize_dec_eq(x_202, x_203);
if (x_204 == 0)
{
lean_object* x_205; 
lean_dec(x_1);
x_205 = l_Lean_Expr_letE___override(x_180, x_186, x_189, x_193, x_184);
lean_ctor_set(x_191, 0, x_205);
return x_191;
}
else
{
lean_dec(x_193);
lean_dec(x_189);
lean_dec(x_186);
lean_dec(x_180);
lean_ctor_set(x_191, 0, x_1);
return x_191;
}
}
}
}
else
{
lean_object* x_206; lean_object* x_207; size_t x_208; size_t x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_191, 0);
x_207 = lean_ctor_get(x_191, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_191);
x_208 = lean_ptr_addr(x_181);
lean_dec(x_181);
x_209 = lean_ptr_addr(x_186);
x_210 = lean_usize_dec_eq(x_208, x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_1);
x_211 = l_Lean_Expr_letE___override(x_180, x_186, x_189, x_206, x_184);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_207);
return x_212;
}
else
{
size_t x_213; size_t x_214; uint8_t x_215; 
x_213 = lean_ptr_addr(x_182);
lean_dec(x_182);
x_214 = lean_ptr_addr(x_189);
x_215 = lean_usize_dec_eq(x_213, x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_183);
lean_dec(x_1);
x_216 = l_Lean_Expr_letE___override(x_180, x_186, x_189, x_206, x_184);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_207);
return x_217;
}
else
{
size_t x_218; size_t x_219; uint8_t x_220; 
x_218 = lean_ptr_addr(x_183);
lean_dec(x_183);
x_219 = lean_ptr_addr(x_206);
x_220 = lean_usize_dec_eq(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_1);
x_221 = l_Lean_Expr_letE___override(x_180, x_186, x_189, x_206, x_184);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_207);
return x_222;
}
else
{
lean_object* x_223; 
lean_dec(x_206);
lean_dec(x_189);
lean_dec(x_186);
lean_dec(x_180);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_1);
lean_ctor_set(x_223, 1, x_207);
return x_223;
}
}
}
}
}
case 10:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_224 = lean_ctor_get(x_1, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_1, 1);
lean_inc(x_225);
lean_inc(x_225);
x_226 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_225, x_2);
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; size_t x_229; size_t x_230; uint8_t x_231; 
x_228 = lean_ctor_get(x_226, 0);
x_229 = lean_ptr_addr(x_225);
lean_dec(x_225);
x_230 = lean_ptr_addr(x_228);
x_231 = lean_usize_dec_eq(x_229, x_230);
if (x_231 == 0)
{
lean_object* x_232; 
lean_dec(x_1);
x_232 = l_Lean_Expr_mdata___override(x_224, x_228);
lean_ctor_set(x_226, 0, x_232);
return x_226;
}
else
{
lean_dec(x_228);
lean_dec(x_224);
lean_ctor_set(x_226, 0, x_1);
return x_226;
}
}
else
{
lean_object* x_233; lean_object* x_234; size_t x_235; size_t x_236; uint8_t x_237; 
x_233 = lean_ctor_get(x_226, 0);
x_234 = lean_ctor_get(x_226, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_226);
x_235 = lean_ptr_addr(x_225);
lean_dec(x_225);
x_236 = lean_ptr_addr(x_233);
x_237 = lean_usize_dec_eq(x_235, x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_1);
x_238 = l_Lean_Expr_mdata___override(x_224, x_233);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_234);
return x_239;
}
else
{
lean_object* x_240; 
lean_dec(x_233);
lean_dec(x_224);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_1);
lean_ctor_set(x_240, 1, x_234);
return x_240;
}
}
}
case 11:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_241 = lean_ctor_get(x_1, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_1, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_1, 2);
lean_inc(x_243);
lean_inc(x_243);
x_244 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_243, x_2);
x_245 = !lean_is_exclusive(x_244);
if (x_245 == 0)
{
lean_object* x_246; size_t x_247; size_t x_248; uint8_t x_249; 
x_246 = lean_ctor_get(x_244, 0);
x_247 = lean_ptr_addr(x_243);
lean_dec(x_243);
x_248 = lean_ptr_addr(x_246);
x_249 = lean_usize_dec_eq(x_247, x_248);
if (x_249 == 0)
{
lean_object* x_250; 
lean_dec(x_1);
x_250 = l_Lean_Expr_proj___override(x_241, x_242, x_246);
lean_ctor_set(x_244, 0, x_250);
return x_244;
}
else
{
lean_dec(x_246);
lean_dec(x_242);
lean_dec(x_241);
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
lean_dec(x_243);
x_254 = lean_ptr_addr(x_251);
x_255 = lean_usize_dec_eq(x_253, x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_1);
x_256 = l_Lean_Expr_proj___override(x_241, x_242, x_251);
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
lean_dec(x_241);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_1);
lean_ctor_set(x_258, 1, x_252);
return x_258;
}
}
}
default: 
{
lean_object* x_259; 
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_1);
lean_ctor_set(x_259, 1, x_2);
return x_259;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1;
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_5);
x_9 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_apply_1(x_13, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__2___boxed), 3, 2);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_10);
x_17 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__3), 5, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_1);
lean_closure_set(x_6, 3, x_4);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKey___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_mkTableKey___rarg___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1;
x_2 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
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
static lean_object* _init_l_Lean_Meta_SynthInstance_TableEntry_answers___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_State_result_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_State_generatorStack___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_State_resumeStack___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_SynthInstance_State_tableEntries___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_State_tableEntries___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_SynthInstance_State_tableEntries___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Meta_SynthInstance_State_tableEntries___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_checkMaxHeartbeats___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeclass", 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkMaxHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_Meta_SynthInstance_checkMaxHeartbeats___closed__1;
x_10 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__3;
x_11 = l_Lean_Core_checkMaxHeartbeatsCore(x_9, x_10, x_8, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkMaxHeartbeats___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_checkMaxHeartbeats(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mapMetaM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_2(x_3, x_4, x_5);
x_12 = lean_apply_7(x_1, lean_box(0), x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg), 1, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_instInhabitedSynthM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_SynthInstance_getInstances___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_array_fget(x_1, x_2);
x_9 = lean_array_fget(x_1, x_7);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_13; 
x_13 = lean_array_fswap(x_1, x_2, x_7);
lean_dec(x_2);
x_1 = x_13;
x_2 = x_7;
x_3 = lean_box(0);
goto _start;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_SynthInstance_getInstances___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_10 = l_Array_insertionSort_swapLoop___at_Lean_Meta_SynthInstance_getInstances___spec__2(x_1, x_2, lean_box(0));
x_11 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_11;
x_3 = x_7;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_SynthInstance_getInstances___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___rarg(x_2);
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
lean_dec(x_13);
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
lean_dec(x_18);
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
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.SynthInstance", 23);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.SynthInstance.getInstances", 36);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("global instance is not a constant", 33);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__1;
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__2;
x_3 = lean_unsigned_to_nat(209u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_30; 
x_12 = lean_array_uget(x_2, x_3);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_dec(x_12);
if (lean_obj_tag(x_30) == 4)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_1);
x_33 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(x_1, x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_box(0);
lean_inc(x_32);
x_35 = l_List_mapM_loop___at_Lean_Meta_SynthInstance_getInstances___spec__3(x_32, x_34, x_6, x_7, x_8, x_9, x_10);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = l_ptrEqList___rarg(x_32, x_37);
lean_dec(x_32);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_30);
x_39 = l_Lean_Expr_const___override(x_31, x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_35, 0, x_40);
x_13 = x_35;
goto block_29;
}
else
{
lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_35, 0, x_41);
x_13 = x_35;
goto block_29;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
x_44 = l_ptrEqList___rarg(x_32, x_42);
lean_dec(x_32);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_30);
x_45 = l_Lean_Expr_const___override(x_31, x_42);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
x_13 = x_47;
goto block_29;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_31);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_30);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
x_13 = x_49;
goto block_29;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_10);
x_13 = x_51;
goto block_29;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_30);
x_52 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_53 = l_panic___at___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___spec__1(x_52, x_6, x_7, x_8, x_9, x_10);
x_13 = x_53;
goto block_29;
}
block_29:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_10 = x_15;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_array_push(x_5, x_20);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_5 = x_21;
x_10 = x_19;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_5);
lean_ctor_set(x_54, 1, x_10);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Meta_SynthInstance_getInstances___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
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
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_18 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_19 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5(x_1, x_2, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
if (x_9 == 0)
{
lean_dec(x_7);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_array_push(x_5, x_13);
x_3 = x_11;
x_5 = x_14;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type class instance expected", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instances", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_3 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#[", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_isClass_x3f(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_indentExpr(x_3);
x_13 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__2;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Meta_collectForwardDeps___spec__1(x_16, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_Meta_getGlobalInstancesIndex___rarg(x_7, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Meta_DiscrTree_getUnify___rarg(x_23, x_21, x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_get_size(x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Array_insertionSort_traverse___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_25, x_28, x_27);
x_30 = l_Lean_Meta_getErasedInstances___rarg(x_7, x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_get_size(x_29);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_34 = l_Array_filterMapM___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_31, x_29, x_28, x_33, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_array_get_size(x_1);
x_39 = lean_nat_dec_lt(x_28, x_38);
x_40 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_41 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_40, x_4, x_5, x_6, x_7, x_36);
if (x_39 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_38);
lean_dec(x_19);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
lean_dec(x_41);
x_56 = lean_unbox(x_54);
lean_dec(x_54);
x_42 = x_35;
x_43 = x_56;
x_44 = x_55;
goto block_53;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_38, x_38);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_38);
lean_dec(x_19);
x_58 = lean_ctor_get(x_41, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
lean_dec(x_41);
x_60 = lean_unbox(x_58);
lean_dec(x_58);
x_42 = x_35;
x_43 = x_60;
x_44 = x_59;
goto block_53;
}
else
{
lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_41, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_41, 1);
lean_inc(x_62);
lean_dec(x_41);
x_63 = 0;
x_64 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_65 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6(x_19, x_1, x_63, x_64, x_35);
lean_dec(x_19);
x_66 = lean_unbox(x_61);
lean_dec(x_61);
x_42 = x_65;
x_43 = x_66;
x_44 = x_62;
goto block_53;
}
}
block_53:
{
if (x_43 == 0)
{
lean_object* x_45; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_37)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_37;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_37);
x_46 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__8;
x_47 = l_Lean_MessageData_arrayExpr_toMessageData(x_42, x_28, x_46);
x_48 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_40, x_47, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_42);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_34);
if (x_67 == 0)
{
return x_34;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_34, 0);
x_69 = lean_ctor_get(x_34, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_34);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_24);
if (x_71 == 0)
{
return x_24;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_24, 0);
x_73 = lean_ctor_get(x_24, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_24);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Meta_getLocalInstances(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getInstances___lambda__2___boxed), 8, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_SynthInstance_getInstances___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at_Lean_Meta_SynthInstance_getInstances___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Meta_SynthInstance_getInstances___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_filterMapM___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_getInstances___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_getInstances___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkGeneratorNode_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_9, x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_4);
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
x_18 = l_Array_isEmpty___rarg(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_14);
x_19 = lean_st_ref_get(x_6, x_17);
lean_dec(x_6);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_4, x_20);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_array_get_size(x_16);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_16);
lean_ctor_set(x_26, 4, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_array_get_size(x_16);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_1);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_16);
lean_ctor_set(x_32, 4, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
x_38 = l_Array_isEmpty___rarg(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_st_ref_get(x_6, x_37);
lean_dec(x_6);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_ref_get(x_4, x_40);
lean_dec(x_4);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_array_get_size(x_36);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_1);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_36);
lean_ctor_set(x_47, 4, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_37);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_14);
if (x_52 == 0)
{
return x_14;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_14, 0);
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_14);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_8);
if (x_56 == 0)
{
return x_8;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_8, 0);
x_58 = lean_ctor_get(x_8, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_8);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = (size_t)(x_7) & (lean_unbox(x_6) - 1);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Expr_hash(x_12);
x_17 = (size_t)(x_16) & (lean_unbox(x_15) - 1);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Lean_AssocList_foldlM___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_expr_eqv(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_AssocList_replace___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_expr_eqv(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_AssocList_replace___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
lean_inc(x_7);
x_9 = (size_t)(x_8) & (lean_unbox(x_7) - 1);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_13, x_15);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Expr_hash(x_2);
lean_inc(x_23);
x_25 = (size_t)(x_24) & (lean_unbox(x_23) - 1);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_8(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___closed__1;
x_12 = lean_st_ref_get(x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_6, 2);
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
x_20 = lean_ctor_get(x_6, 2);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__2;
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg(lean_object* x_1, lean_object* x_2) {
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
x_12 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__3;
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
x_24 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___boxed), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_10, 5);
x_15 = l_Lean_replaceRef(x_3, x_14);
lean_dec(x_14);
lean_ctor_set(x_10, 5, x_15);
x_16 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_4, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_take(x_11, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_20, 3);
x_24 = l_Lean_PersistentArray_toArray___rarg(x_23);
x_25 = lean_array_get_size(x_24);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(x_26, x_27, x_24);
x_29 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_17);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_PersistentArray_push___rarg(x_1, x_30);
lean_ctor_set(x_20, 3, x_31);
x_32 = lean_st_ref_set(x_11, x_20, x_21);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
x_41 = lean_ctor_get(x_20, 2);
x_42 = lean_ctor_get(x_20, 3);
x_43 = lean_ctor_get(x_20, 4);
x_44 = lean_ctor_get(x_20, 5);
x_45 = lean_ctor_get(x_20, 6);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
x_46 = l_Lean_PersistentArray_toArray___rarg(x_42);
x_47 = lean_array_get_size(x_46);
x_48 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_49 = 0;
x_50 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(x_48, x_49, x_46);
x_51 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_17);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_5);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_3);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_PersistentArray_push___rarg(x_1, x_52);
x_54 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_54, 0, x_39);
lean_ctor_set(x_54, 1, x_40);
lean_ctor_set(x_54, 2, x_41);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_43);
lean_ctor_set(x_54, 5, x_44);
lean_ctor_set(x_54, 6, x_45);
x_55 = lean_st_ref_set(x_11, x_54, x_21);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_60 = lean_ctor_get(x_10, 0);
x_61 = lean_ctor_get(x_10, 1);
x_62 = lean_ctor_get(x_10, 2);
x_63 = lean_ctor_get(x_10, 3);
x_64 = lean_ctor_get(x_10, 4);
x_65 = lean_ctor_get(x_10, 5);
x_66 = lean_ctor_get(x_10, 6);
x_67 = lean_ctor_get(x_10, 7);
x_68 = lean_ctor_get(x_10, 8);
x_69 = lean_ctor_get(x_10, 9);
x_70 = lean_ctor_get(x_10, 10);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_10);
x_71 = l_Lean_replaceRef(x_3, x_65);
lean_dec(x_65);
x_72 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_61);
lean_ctor_set(x_72, 2, x_62);
lean_ctor_set(x_72, 3, x_63);
lean_ctor_set(x_72, 4, x_64);
lean_ctor_set(x_72, 5, x_71);
lean_ctor_set(x_72, 6, x_66);
lean_ctor_set(x_72, 7, x_67);
lean_ctor_set(x_72, 8, x_68);
lean_ctor_set(x_72, 9, x_69);
lean_ctor_set(x_72, 10, x_70);
x_73 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_4, x_8, x_9, x_72, x_11, x_12);
lean_dec(x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_st_ref_take(x_11, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 6);
lean_inc(x_85);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 lean_ctor_release(x_77, 6);
 x_86 = x_77;
} else {
 lean_dec_ref(x_77);
 x_86 = lean_box(0);
}
x_87 = l_Lean_PersistentArray_toArray___rarg(x_82);
x_88 = lean_array_get_size(x_87);
x_89 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_90 = 0;
x_91 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNode___spec__1(x_89, x_90, x_87);
x_92 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_92, 0, x_2);
lean_ctor_set(x_92, 1, x_74);
lean_ctor_set(x_92, 2, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*3, x_5);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_3);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_PersistentArray_push___rarg(x_1, x_93);
if (lean_is_scalar(x_86)) {
 x_95 = lean_alloc_ctor(0, 7, 0);
} else {
 x_95 = x_86;
}
lean_ctor_set(x_95, 0, x_79);
lean_ctor_set(x_95, 1, x_80);
lean_ctor_set(x_95, 2, x_81);
lean_ctor_set(x_95, 3, x_94);
lean_ctor_set(x_95, 4, x_83);
lean_ctor_set(x_95, 5, x_84);
lean_ctor_set(x_95, 6, x_85);
x_96 = lean_st_ref_set(x_11, x_95, x_78);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = lean_box(0);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_newSubgoal___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_9, 5);
lean_inc(x_18);
x_19 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg(x_10, x_17);
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
x_22 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_25);
x_26 = lean_apply_8(x_2, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_9);
x_29 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__12(x_20, x_1, x_18, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_newSubgoal___spec__13(x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_25);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_22, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_dec(x_22);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_36);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_38);
x_39 = lean_apply_8(x_2, x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_9);
x_42 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__12(x_20, x_1, x_18, x_40, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_newSubgoal___spec__13(x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_38);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_38);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Exception_toMessageData(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
}
static lean_object* _init_l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___closed__1;
x_12 = l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
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
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_2, x_3, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_mkGeneratorNode_x3f(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("no instances for ", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("new goal ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__3;
x_21 = lean_array_push(x_20, x_2);
x_22 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_st_ref_get(x_9, x_10);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_5, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_ctor_get(x_27, 3);
x_32 = lean_array_push(x_30, x_19);
lean_inc(x_1);
x_33 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_31, x_1, x_23);
lean_ctor_set(x_27, 3, x_33);
lean_ctor_set(x_27, 1, x_32);
x_34 = lean_st_ref_set(x_5, x_27, x_28);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_1);
x_38 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__5;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_34, 0, x_43);
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_1);
x_46 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__5;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_53 = lean_ctor_get(x_27, 0);
x_54 = lean_ctor_get(x_27, 1);
x_55 = lean_ctor_get(x_27, 2);
x_56 = lean_ctor_get(x_27, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_27);
x_57 = lean_array_push(x_54, x_19);
lean_inc(x_1);
x_58 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_56, x_1, x_23);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_58);
x_60 = lean_st_ref_set(x_5, x_59, x_28);
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
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_1);
x_64 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__5;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
if (lean_is_scalar(x_62)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_62;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_61);
return x_70;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_newSubgoal___lambda__1___boxed), 9, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___boxed), 10, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_4);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___boxed), 10, 3);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_14);
lean_closure_set(x_18, 2, x_17);
x_19 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(x_1, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__12(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_newSubgoal___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_newSubgoal___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = (size_t)(x_5) & (lean_unbox(x_4) - 1);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(x_14, x_1);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(x_18, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_instInhabitedSynthM___boxed), 7, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.SynthInstance.getEntry", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid key at synthInstance", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__1;
x_2 = l_Lean_Meta_SynthInstance_getEntry___closed__1;
x_3 = lean_unsigned_to_nat(248u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Meta_SynthInstance_getEntry___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_SynthInstance_getEntry___closed__3;
x_13 = l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_hasMVar(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_11 = lean_st_ref_get(x_7, x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_5, x_12);
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
x_20 = lean_st_ref_get(x_7, x_15);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_5, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_19);
x_27 = lean_st_ref_set(x_5, x_23, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_18);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_23, 1);
x_33 = lean_ctor_get(x_23, 2);
x_34 = lean_ctor_get(x_23, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_st_ref_set(x_5, x_35, x_24);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1;
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_14);
x_18 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_1, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_7, x_13);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_take(x_5, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
lean_ctor_set(x_25, 0, x_21);
x_29 = lean_st_ref_set(x_5, x_25, x_26);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_19);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_25, 1);
x_35 = lean_ctor_get(x_25, 2);
x_36 = lean_ctor_get(x_25, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_st_ref_set(x_5, x_37, x_26);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_19);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKeyFor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__2___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1___boxed), 8, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l_Lean_Meta_SynthInstance_mkTableKeyFor___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_getSubgoalsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_8) == 7)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_17 = lean_array_get_size(x_4);
x_18 = lean_expr_instantiate_rev_range(x_14, x_5, x_17, x_4);
lean_dec(x_17);
lean_dec(x_14);
x_19 = 0;
x_20 = 1;
x_21 = 1;
lean_inc(x_3);
x_22 = l_Lean_Meta_mkForallFVars(x_3, x_18, x_19, x_20, x_21, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 0;
x_26 = lean_box(0);
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l_Lean_Meta_mkFreshExprMVarAt(x_1, x_2, x_23, x_25, x_26, x_27, x_9, x_10, x_11, x_12, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_3);
lean_inc(x_29);
x_31 = l_Lean_mkAppN(x_29, x_3);
lean_inc(x_31);
x_32 = l_Lean_Expr_app___override(x_7, x_31);
x_33 = l_Lean_BinderInfo_isInstImplicit(x_16);
x_34 = lean_array_push(x_4, x_31);
if (x_33 == 0)
{
lean_dec(x_29);
x_4 = x_34;
x_7 = x_32;
x_8 = x_15;
x_13 = x_30;
goto _start;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_6);
x_4 = x_34;
x_6 = x_36;
x_7 = x_32;
x_8 = x_15;
x_13 = x_30;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_array_get_size(x_4);
x_43 = lean_expr_instantiate_rev_range(x_8, x_5, x_42, x_4);
lean_dec(x_5);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_44 = lean_whnf(x_43, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_48 = l_Lean_Expr_isForall(x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_6);
lean_ctor_set(x_49, 1, x_7);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_44, 0, x_49);
return x_44;
}
else
{
lean_free_object(x_44);
x_5 = x_42;
x_8 = x_46;
x_13 = x_47;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_44, 0);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_44);
x_53 = l_Lean_Expr_isForall(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_6);
lean_ctor_set(x_54, 1, x_7);
lean_ctor_set(x_54, 2, x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
x_5 = x_42;
x_8 = x_51;
x_13 = x_52;
goto _start;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_44);
if (x_57 == 0)
{
return x_44;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getSubgoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = lean_infer_type(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_4);
x_16 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_getSubgoalsAux(x_1, x_2, x_3, x_14, x_15, x_13, x_4, x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Expr_getAppFn(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_8, x_19);
lean_dec(x_8);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1;
x_27 = l_Lean_TagAttribute_hasTag(x_26, x_25, x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
x_29 = l_List_reverse___rarg(x_28);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 2);
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_22, 0, x_32);
return x_22;
}
else
{
lean_ctor_set(x_22, 0, x_18);
return x_22;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1;
x_37 = l_Lean_TagAttribute_hasTag(x_36, x_35, x_21);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
x_39 = l_List_reverse___rarg(x_38);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_18, 2);
lean_inc(x_41);
lean_dec(x_18);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_34);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_18);
lean_ctor_set(x_44, 1, x_34);
return x_44;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_8);
return x_16;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_47 = l_Lean_Expr_getAppFn(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_47) == 4)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_get(x_8, x_46);
lean_dec(x_8);
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
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1;
x_55 = l_Lean_TagAttribute_hasTag(x_54, x_53, x_48);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_45, 0);
lean_inc(x_56);
x_57 = l_List_reverse___rarg(x_56);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_45, 2);
lean_inc(x_59);
lean_dec(x_45);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_59);
if (lean_is_scalar(x_52)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_52;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
return x_61;
}
else
{
lean_object* x_62; 
if (lean_is_scalar(x_52)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_52;
}
lean_ctor_set(x_62, 0, x_45);
lean_ctor_set(x_62, 1, x_51);
return x_62;
}
}
else
{
lean_object* x_63; 
lean_dec(x_47);
lean_dec(x_8);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_45);
lean_ctor_set(x_63, 1, x_46);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
lean_dec(x_4);
x_64 = !lean_is_exclusive(x_16);
if (x_64 == 0)
{
return x_16;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_16, 0);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_16);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_10);
if (x_68 == 0)
{
return x_10;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_10, 0);
x_70 = lean_ctor_get(x_10, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_10);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_Lean_Meta_SynthInstance_tryResolve___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_12);
x_13 = l_Lean_MetavarContext_getDecl(x_12, x_1);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_box(x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_20);
x_21 = l_Lean_MetavarContext_getDecl(x_20, x_1);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
}
static lean_object* _init_l_panic___at_Lean_Meta_SynthInstance_tryResolve___spec__5___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_instInhabitedBool;
x_3 = lean_box(x_2);
x_4 = l_instInhabited___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_SynthInstance_tryResolve___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Meta_SynthInstance_tryResolve___spec__5___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_tryResolve___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
x_15 = l_Lean_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_free_object(x_9);
x_16 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__4;
x_17 = l_panic___at_Lean_Meta_SynthInstance_tryResolve___spec__5(x_16, x_2, x_3, x_4, x_5, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = lean_box(x_20);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
x_26 = l_Lean_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(x_25, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
x_27 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__4;
x_28 = l_panic___at_Lean_Meta_SynthInstance_tryResolve___spec__5(x_27, x_2, x_3, x_4, x_5, x_23);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Level_hasMVar(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
case 2:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Level_hasMVar(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = l_Lean_Level_hasMVar(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
x_1 = x_13;
goto _start;
}
}
else
{
lean_object* x_19; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_hasAssignableLevelMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__3(x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_20);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = l_Lean_Level_hasMVar(x_13);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_box(x_25);
lean_ctor_set(x_19, 0, x_26);
return x_19;
}
else
{
lean_free_object(x_19);
x_1 = x_13;
x_6 = x_23;
goto _start;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Lean_Level_hasMVar(x_13);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
x_1 = x_13;
x_6 = x_28;
goto _start;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_19, 0);
lean_dec(x_34);
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
case 3:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lean_Level_hasMVar(x_41);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_41);
x_44 = l_Lean_Level_hasMVar(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_6);
return x_46;
}
else
{
x_1 = x_42;
goto _start;
}
}
else
{
lean_object* x_48; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_48 = l_Lean_hasAssignableLevelMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__3(x_41, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
if (x_50 == 0)
{
uint8_t x_51; 
lean_dec(x_49);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_48, 1);
x_53 = lean_ctor_get(x_48, 0);
lean_dec(x_53);
x_54 = l_Lean_Level_hasMVar(x_42);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_box(x_54);
lean_ctor_set(x_48, 0, x_55);
return x_48;
}
else
{
lean_free_object(x_48);
x_1 = x_42;
x_6 = x_52;
goto _start;
}
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_dec(x_48);
x_58 = l_Lean_Level_hasMVar(x_42);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
x_1 = x_42;
x_6 = x_57;
goto _start;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_48);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_48, 0);
lean_dec(x_63);
return x_48;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_dec(x_48);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_48);
if (x_66 == 0)
{
return x_48;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_48, 0);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_48);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
case 5:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
lean_dec(x_1);
x_71 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_tryResolve___spec__4(x_70, x_2, x_3, x_4, x_5, x_6);
return x_71;
}
default: 
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = 0;
x_73 = lean_box(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_6);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at_Lean_Meta_SynthInstance_tryResolve___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_hasAssignableLevelMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__3(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_1 = x_11;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_MVarId_isAssignable___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_hasAssignableLevelMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__3(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
case 4:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_List_anyM___at_Lean_Meta_SynthInstance_tryResolve___spec__6(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Expr_hasMVar(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = l_Lean_Expr_hasMVar(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
else
{
x_1 = x_14;
goto _start;
}
}
else
{
lean_object* x_20; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_21);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
x_26 = l_Lean_Expr_hasMVar(x_14);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(x_26);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_free_object(x_20);
x_1 = x_14;
x_6 = x_24;
goto _start;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = l_Lean_Expr_hasMVar(x_14);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
x_1 = x_14;
x_6 = x_29;
goto _start;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_20, 0);
lean_dec(x_35);
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
case 6:
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
lean_dec(x_1);
x_44 = l_Lean_Expr_hasMVar(x_42);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_42);
x_45 = l_Lean_Expr_hasMVar(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_6);
return x_47;
}
else
{
x_1 = x_43;
goto _start;
}
}
else
{
lean_object* x_49; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_49 = l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_42, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_50);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_49, 1);
x_54 = lean_ctor_get(x_49, 0);
lean_dec(x_54);
x_55 = l_Lean_Expr_hasMVar(x_43);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_box(x_55);
lean_ctor_set(x_49, 0, x_56);
return x_49;
}
else
{
lean_free_object(x_49);
x_1 = x_43;
x_6 = x_53;
goto _start;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_dec(x_49);
x_59 = l_Lean_Expr_hasMVar(x_43);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
x_1 = x_43;
x_6 = x_58;
goto _start;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_49);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_49, 0);
lean_dec(x_64);
return x_49;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_49, 1);
lean_inc(x_65);
lean_dec(x_49);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_50);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_49);
if (x_67 == 0)
{
return x_49;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_49, 0);
x_69 = lean_ctor_get(x_49, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_49);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 7:
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 2);
lean_inc(x_72);
lean_dec(x_1);
x_73 = l_Lean_Expr_hasMVar(x_71);
if (x_73 == 0)
{
uint8_t x_74; 
lean_dec(x_71);
x_74 = l_Lean_Expr_hasMVar(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_6);
return x_76;
}
else
{
x_1 = x_72;
goto _start;
}
}
else
{
lean_object* x_78; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_78 = l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_71, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
uint8_t x_81; 
lean_dec(x_79);
x_81 = !lean_is_exclusive(x_78);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_78, 1);
x_83 = lean_ctor_get(x_78, 0);
lean_dec(x_83);
x_84 = l_Lean_Expr_hasMVar(x_72);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = lean_box(x_84);
lean_ctor_set(x_78, 0, x_85);
return x_78;
}
else
{
lean_free_object(x_78);
x_1 = x_72;
x_6 = x_82;
goto _start;
}
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_78, 1);
lean_inc(x_87);
lean_dec(x_78);
x_88 = l_Lean_Expr_hasMVar(x_72);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = lean_box(x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
x_1 = x_72;
x_6 = x_87;
goto _start;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_78);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_78, 0);
lean_dec(x_93);
return x_78;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_78, 1);
lean_inc(x_94);
lean_dec(x_78);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_79);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_78);
if (x_96 == 0)
{
return x_78;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_78, 0);
x_98 = lean_ctor_get(x_78, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_78);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
case 8:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_1, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_1, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_1, 3);
lean_inc(x_102);
lean_dec(x_1);
x_103 = l_Lean_Expr_hasMVar(x_100);
if (x_103 == 0)
{
uint8_t x_104; 
lean_dec(x_100);
x_104 = l_Lean_Expr_hasMVar(x_101);
if (x_104 == 0)
{
uint8_t x_105; 
lean_dec(x_101);
x_105 = l_Lean_Expr_hasMVar(x_102);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = lean_box(x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_6);
return x_107;
}
else
{
x_1 = x_102;
goto _start;
}
}
else
{
lean_object* x_109; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_109 = l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_101, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
if (x_111 == 0)
{
uint8_t x_112; 
lean_dec(x_110);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_109, 1);
x_114 = lean_ctor_get(x_109, 0);
lean_dec(x_114);
x_115 = l_Lean_Expr_hasMVar(x_102);
if (x_115 == 0)
{
lean_object* x_116; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_box(x_115);
lean_ctor_set(x_109, 0, x_116);
return x_109;
}
else
{
lean_free_object(x_109);
x_1 = x_102;
x_6 = x_113;
goto _start;
}
}
else
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_109, 1);
lean_inc(x_118);
lean_dec(x_109);
x_119 = l_Lean_Expr_hasMVar(x_102);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_box(x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
else
{
x_1 = x_102;
x_6 = x_118;
goto _start;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_109);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_109, 0);
lean_dec(x_124);
return x_109;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_109, 1);
lean_inc(x_125);
lean_dec(x_109);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_110);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_127 = !lean_is_exclusive(x_109);
if (x_127 == 0)
{
return x_109;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_109, 0);
x_129 = lean_ctor_get(x_109, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_109);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
else
{
lean_object* x_131; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_131 = l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_100, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
if (x_133 == 0)
{
uint8_t x_134; 
lean_dec(x_132);
x_134 = !lean_is_exclusive(x_131);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_131, 1);
x_136 = lean_ctor_get(x_131, 0);
lean_dec(x_136);
x_137 = l_Lean_Expr_hasMVar(x_101);
if (x_137 == 0)
{
uint8_t x_138; 
lean_dec(x_101);
x_138 = l_Lean_Expr_hasMVar(x_102);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = lean_box(x_138);
lean_ctor_set(x_131, 0, x_139);
return x_131;
}
else
{
lean_free_object(x_131);
x_1 = x_102;
x_6 = x_135;
goto _start;
}
}
else
{
lean_object* x_141; 
lean_free_object(x_131);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_141 = l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_101, x_2, x_3, x_4, x_5, x_135);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
if (x_143 == 0)
{
uint8_t x_144; 
lean_dec(x_142);
x_144 = !lean_is_exclusive(x_141);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_141, 1);
x_146 = lean_ctor_get(x_141, 0);
lean_dec(x_146);
x_147 = l_Lean_Expr_hasMVar(x_102);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_box(x_147);
lean_ctor_set(x_141, 0, x_148);
return x_141;
}
else
{
lean_free_object(x_141);
x_1 = x_102;
x_6 = x_145;
goto _start;
}
}
else
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_141, 1);
lean_inc(x_150);
lean_dec(x_141);
x_151 = l_Lean_Expr_hasMVar(x_102);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_box(x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_150);
return x_153;
}
else
{
x_1 = x_102;
x_6 = x_150;
goto _start;
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_155 = !lean_is_exclusive(x_141);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_141, 0);
lean_dec(x_156);
return x_141;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_141, 1);
lean_inc(x_157);
lean_dec(x_141);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_142);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_159 = !lean_is_exclusive(x_141);
if (x_159 == 0)
{
return x_141;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_141, 0);
x_161 = lean_ctor_get(x_141, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_141);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_131, 1);
lean_inc(x_163);
lean_dec(x_131);
x_164 = l_Lean_Expr_hasMVar(x_101);
if (x_164 == 0)
{
uint8_t x_165; 
lean_dec(x_101);
x_165 = l_Lean_Expr_hasMVar(x_102);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_166 = lean_box(x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_163);
return x_167;
}
else
{
x_1 = x_102;
x_6 = x_163;
goto _start;
}
}
else
{
lean_object* x_169; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_169 = l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_101, x_2, x_3, x_4, x_5, x_163);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_170);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_173 = x_169;
} else {
 lean_dec_ref(x_169);
 x_173 = lean_box(0);
}
x_174 = l_Lean_Expr_hasMVar(x_102);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_175 = lean_box(x_174);
if (lean_is_scalar(x_173)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_173;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_172);
return x_176;
}
else
{
lean_dec(x_173);
x_1 = x_102;
x_6 = x_172;
goto _start;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = lean_ctor_get(x_169, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_179 = x_169;
} else {
 lean_dec_ref(x_169);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_170);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_181 = lean_ctor_get(x_169, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_169, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_183 = x_169;
} else {
 lean_dec_ref(x_169);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_131);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_131, 0);
lean_dec(x_186);
return x_131;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_131, 1);
lean_inc(x_187);
lean_dec(x_131);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_132);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_189 = !lean_is_exclusive(x_131);
if (x_189 == 0)
{
return x_131;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_131, 0);
x_191 = lean_ctor_get(x_131, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_131);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
case 10:
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_1, 1);
lean_inc(x_193);
lean_dec(x_1);
x_194 = l_Lean_Expr_hasMVar(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_193);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_195 = lean_box(x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_6);
return x_196;
}
else
{
x_1 = x_193;
goto _start;
}
}
case 11:
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_1, 2);
lean_inc(x_198);
lean_dec(x_1);
x_199 = l_Lean_Expr_hasMVar(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_198);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_200 = lean_box(x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_6);
return x_201;
}
else
{
x_1 = x_198;
goto _start;
}
}
default: 
{
uint8_t x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = 0;
x_204 = lean_box(x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_6);
return x_205;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__7___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_tryResolve___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_tryResolve___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_apply_5(x_3, x_5, x_6, x_7, x_8, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_7, 5);
lean_inc(x_16);
x_17 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_processPostponed___spec__2___rarg(x_8, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = lean_apply_5(x_3, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_24 = lean_apply_6(x_2, x_23, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_7);
x_27 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_processPostponed___spec__3(x_18, x_1, x_16, x_25, x_4, x_5, x_6, x_7, x_8, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_tryResolve___spec__9(x_23, x_5, x_6, x_7, x_8, x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_23);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_34);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_37 = lean_apply_6(x_2, x_36, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_7);
x_40 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_processPostponed___spec__3(x_18, x_1, x_16, x_38, x_4, x_5, x_6, x_7, x_8, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_tryResolve___spec__9(x_36, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_36);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
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
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ≟ ", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_2, x_4, x_5, x_6, x_7, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_exceptOptionEmoji___rarg(x_3);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_10);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_14);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_12, 0, x_27);
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = l_Lean_exceptOptionEmoji___rarg(x_3);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_10);
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__4;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_28);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_32);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_29);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolve___lambda__1___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_4);
x_11 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__7___rarg(x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolve___lambda__3___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_SynthInstance_tryResolve___lambda__4___closed__1;
x_16 = lean_unbox(x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_apply_6(x_15, x_17, x_7, x_8, x_9, x_10, x_14);
return x_18;
}
else
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = 0;
x_20 = 1;
x_21 = 1;
x_22 = l_Lean_Meta_mkLambdaFVars(x_3, x_4, x_19, x_20, x_21, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Lean_Meta_isExprDefEq(x_5, x_23, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = lean_apply_6(x_15, x_29, x_7, x_8, x_9, x_10, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_7);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_st_ref_get(x_10, x_31);
lean_dec(x_10);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_get(x_8, x_33);
lean_dec(x_8);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
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
lean_inc(x_42);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_22);
if (x_50 == 0)
{
return x_22;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_22, 0);
x_52 = lean_ctor_get(x_22, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_22);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
return x_12;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_12);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tryResolve", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_3 = l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_12 = l_Lean_Meta_SynthInstance_getSubgoals(x_1, x_2, x_5, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 2);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_st_ref_get(x_10, x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_8, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_17);
lean_inc(x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolve___lambda__2), 9, 3);
lean_closure_set(x_24, 0, x_6);
lean_closure_set(x_24, 1, x_17);
lean_closure_set(x_24, 2, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolve___lambda__4), 11, 6);
lean_closure_set(x_25, 0, x_6);
lean_closure_set(x_25, 1, x_17);
lean_closure_set(x_25, 2, x_5);
lean_closure_set(x_25, 3, x_16);
lean_closure_set(x_25, 4, x_4);
lean_closure_set(x_25, 5, x_15);
x_26 = l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__2;
x_27 = 1;
x_28 = l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_tryResolve___spec__8(x_26, x_24, x_25, x_27, x_7, x_8, x_9, x_10, x_22);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = l_Lean_Meta_getLocalInstances(x_4, x_5, x_6, x_7, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolve___lambda__5), 11, 4);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_1);
x_17 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_10, x_16, x_4, x_5, x_6, x_7, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_11 = l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_st_ref_get(x_6, x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_4, x_16);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_SynthInstance_tryResolve___lambda__6(x_9, x_2, x_32, x_3, x_4, x_5, x_6, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
return x_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_Lean_Meta_SynthInstance_tryResolve___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssignable___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_tryResolve___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_tryResolve___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_tryResolve___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_tryResolve___spec__8(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_tryResolve___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_tryResolve___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_tryResolve___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_openAbstractMVarsResult(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_6);
x_12 = l_Lean_Meta_isExprDefEq(x_1, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_st_ref_get(x_8, x_21);
lean_dec(x_8);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_6, x_23);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryAnswer___lambda__1___boxed), 8, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryAnswer___lambda__2___boxed), 9, 1);
lean_closure_set(x_13, 0, x_2);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_tryAnswer___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_tryAnswer___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_wakeUp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_15, 3);
x_19 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_20 = 0;
x_21 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_20);
lean_inc(x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_PersistentArray_push___rarg(x_18, x_22);
lean_ctor_set(x_15, 3, x_23);
x_24 = lean_st_ref_set(x_8, x_15, x_16);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
x_33 = lean_ctor_get(x_15, 2);
x_34 = lean_ctor_get(x_15, 3);
x_35 = lean_ctor_get(x_15, 4);
x_36 = lean_ctor_get(x_15, 5);
x_37 = lean_ctor_get(x_15, 6);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_38 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_39 = 0;
x_40 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_12);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_39);
lean_inc(x_10);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_PersistentArray_push___rarg(x_34, x_41);
x_43 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_32);
lean_ctor_set(x_43, 2, x_33);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_35);
lean_ctor_set(x_43, 5, x_36);
lean_ctor_set(x_43, 6, x_37);
x_44 = lean_st_ref_set(x_8, x_43, x_16);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("skip answer containing metavariables ", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_wakeUp___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_wakeUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_14, 2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_1);
x_19 = lean_array_push(x_17, x_18);
lean_ctor_set(x_14, 2, x_19);
x_20 = lean_st_ref_set(x_4, x_14, x_15);
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
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
x_29 = lean_ctor_get(x_14, 2);
x_30 = lean_ctor_get(x_14, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_1);
x_32 = lean_array_push(x_29, x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_30);
x_34 = lean_st_ref_set(x_4, x_33, x_15);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_eq(x_40, x_41);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_inc(x_5);
x_43 = l_Lean_Meta_openAbstractMVarsResult(x_39, x_5, x_6, x_7, x_8, x_9);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
x_49 = l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_47);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_49, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_49, 0, x_54);
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_dec(x_49);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_47);
x_60 = l_Lean_Meta_SynthInstance_wakeUp___closed__2;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_wakeUp___spec__1(x_48, x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_58);
lean_dec(x_5);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_5);
x_65 = lean_st_ref_get(x_8, x_9);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_take(x_4, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_39);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_68, 0);
lean_dec(x_72);
lean_ctor_set(x_68, 0, x_70);
x_73 = lean_st_ref_set(x_4, x_68, x_69);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_68, 1);
x_81 = lean_ctor_get(x_68, 2);
x_82 = lean_ctor_get(x_68, 3);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_68);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_70);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set(x_83, 2, x_81);
lean_ctor_set(x_83, 3, x_82);
x_84 = lean_st_ref_set(x_4, x_83, x_69);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_wakeUp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_wakeUp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_wakeUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_wakeUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_expr_eqv(x_7, x_8);
lean_dec(x_7);
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
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SynthInstance_isNewAnswer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 1;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(x_2, x_1, x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_isNewAnswer___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SynthInstance_isNewAnswer(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Meta_abstractMVars(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
x_13 = lean_infer_type(x_12, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_2, 4);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_16, x_17);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_22, x_23);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_10);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("newAnswer", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_3 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("size: ", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", val: ", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__2;
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_11, x_3, x_4, x_5, x_6, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__1(x_9, x_2, x_16, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_2, 4);
lean_inc(x_19);
x_20 = l_Nat_repr(x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__6;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_9);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_9);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_11, x_30, x_3, x_4, x_5, x_6, x_18);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__1(x_9, x_2, x_32, x_3, x_4, x_5, x_6, x_33);
lean_dec(x_32);
lean_dec(x_2);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2), 7, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
x_10 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__7___rarg(x_7, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Meta_SynthInstance_addAnswer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_8);
lean_inc(x_1);
x_15 = l_Lean_Meta_SynthInstance_wakeUp(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
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
lean_dec(x_8);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_addAnswer___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_addAnswer___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_9, 5);
lean_inc(x_18);
x_19 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg(x_10, x_17);
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
x_22 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_25);
x_26 = lean_apply_8(x_2, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_9);
x_29 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__12(x_20, x_1, x_18, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_addAnswer___spec__4(x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_25);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_22, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_dec(x_22);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_36);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_38);
x_39 = lean_apply_8(x_2, x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_9);
x_42 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__12(x_20, x_1, x_18, x_40, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_addAnswer___spec__4(x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_38);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_38);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_checkEmoji;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_2 = l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__1;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2;
x_2 = l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__2;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = lean_infer_type(x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__3;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__3;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
return x_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
x_11 = l_Lean_Meta_SynthInstance_getEntry(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = l_Lean_Meta_SynthInstance_isNewAnswer(x_17, x_2);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_13);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_11);
lean_inc(x_2);
x_20 = lean_array_push(x_17, x_2);
lean_inc(x_16);
lean_ctor_set(x_13, 1, x_20);
x_21 = lean_st_ref_get(x_8, x_15);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_take(x_4, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 3);
x_28 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_27, x_10, x_13);
lean_ctor_set(x_24, 3, x_28);
x_29 = lean_st_ref_set(x_4, x_24, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_array_get_size(x_16);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_lt(x_34, x_33);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_box(0);
lean_ctor_set(x_29, 0, x_36);
return x_29;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_33, x_33);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
lean_ctor_set(x_29, 0, x_38);
return x_29;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_29);
x_39 = 0;
x_40 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_41 = lean_box(0);
x_42 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(x_2, x_16, x_39, x_40, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_16);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_array_get_size(x_16);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_lt(x_45, x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_44, x_44);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_44);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
return x_51;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_54 = lean_box(0);
x_55 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(x_2, x_16, x_52, x_53, x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_16);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_56 = lean_ctor_get(x_24, 0);
x_57 = lean_ctor_get(x_24, 1);
x_58 = lean_ctor_get(x_24, 2);
x_59 = lean_ctor_get(x_24, 3);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_24);
x_60 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_59, x_10, x_13);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_60);
x_62 = lean_st_ref_set(x_4, x_61, x_25);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_array_get_size(x_16);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_lt(x_66, x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_65);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
else
{
uint8_t x_70; 
x_70 = lean_nat_dec_le(x_65, x_65);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_65);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_64;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_63);
return x_72;
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_64);
x_73 = 0;
x_74 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_75 = lean_box(0);
x_76 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(x_2, x_16, x_73, x_74, x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_16);
return x_76;
}
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_11, 1);
x_78 = lean_ctor_get(x_13, 0);
x_79 = lean_ctor_get(x_13, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_13);
x_80 = l_Lean_Meta_SynthInstance_isNewAnswer(x_79, x_2);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = lean_box(0);
lean_ctor_set(x_11, 0, x_81);
return x_11;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_free_object(x_11);
lean_inc(x_2);
x_82 = lean_array_push(x_79, x_2);
lean_inc(x_78);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_st_ref_get(x_8, x_77);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_st_ref_take(x_4, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 3);
lean_inc(x_92);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 x_93 = x_87;
} else {
 lean_dec_ref(x_87);
 x_93 = lean_box(0);
}
x_94 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_92, x_10, x_83);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 4, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_90);
lean_ctor_set(x_95, 2, x_91);
lean_ctor_set(x_95, 3, x_94);
x_96 = lean_st_ref_set(x_4, x_95, x_88);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = lean_array_get_size(x_78);
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_nat_dec_lt(x_100, x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_99);
lean_dec(x_78);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = lean_box(0);
if (lean_is_scalar(x_98)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_98;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_97);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_99, x_99);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_99);
lean_dec(x_78);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_105 = lean_box(0);
if (lean_is_scalar(x_98)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_98;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_97);
return x_106;
}
else
{
size_t x_107; size_t x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_98);
x_107 = 0;
x_108 = lean_usize_of_nat(x_99);
lean_dec(x_99);
x_109 = lean_box(0);
x_110 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(x_2, x_78, x_107, x_108, x_109, x_3, x_4, x_5, x_6, x_7, x_8, x_97);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_78);
return x_110;
}
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_111 = lean_ctor_get(x_11, 0);
x_112 = lean_ctor_get(x_11, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_11);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_115 = x_111;
} else {
 lean_dec_ref(x_111);
 x_115 = lean_box(0);
}
x_116 = l_Lean_Meta_SynthInstance_isNewAnswer(x_114, x_2);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_112);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_inc(x_2);
x_119 = lean_array_push(x_114, x_2);
lean_inc(x_113);
if (lean_is_scalar(x_115)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_115;
}
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_st_ref_get(x_8, x_112);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_st_ref_take(x_4, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_124, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_124, 3);
lean_inc(x_129);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 x_130 = x_124;
} else {
 lean_dec_ref(x_124);
 x_130 = lean_box(0);
}
x_131 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_129, x_10, x_120);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 4, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_126);
lean_ctor_set(x_132, 1, x_127);
lean_ctor_set(x_132, 2, x_128);
lean_ctor_set(x_132, 3, x_131);
x_133 = lean_st_ref_set(x_4, x_132, x_125);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
x_136 = lean_array_get_size(x_113);
x_137 = lean_unsigned_to_nat(0u);
x_138 = lean_nat_dec_lt(x_137, x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_136);
lean_dec(x_113);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = lean_box(0);
if (lean_is_scalar(x_135)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_135;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_134);
return x_140;
}
else
{
uint8_t x_141; 
x_141 = lean_nat_dec_le(x_136, x_136);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_136);
lean_dec(x_113);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = lean_box(0);
if (lean_is_scalar(x_135)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_135;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_134);
return x_143;
}
else
{
size_t x_144; size_t x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_135);
x_144 = 0;
x_145 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_146 = lean_box(0);
x_147 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(x_2, x_113, x_144, x_145, x_146, x_3, x_4, x_5, x_6, x_7, x_8, x_134);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_113);
return x_147;
}
}
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = !lean_is_exclusive(x_11);
if (x_148 == 0)
{
return x_11;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_11, 0);
x_150 = lean_ctor_get(x_11, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_11);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("answer", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_3 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_crossEmoji;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_2 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__3;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__4;
x_2 = l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__2;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(size: ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ≥ ", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
x_12 = lean_nat_dec_le(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_dec(x_11);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_addAnswer___lambda__1___boxed), 9, 1);
lean_closure_set(x_13, 0, x_1);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_addAnswer___lambda__2___boxed), 8, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_addAnswer___lambda__3), 9, 1);
lean_closure_set(x_15, 0, x_1);
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__2;
x_18 = 1;
x_19 = l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_addAnswer___spec__3(x_17, x_13, x_16, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__2;
x_21 = l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_32 = lean_infer_type(x_31, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__5;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__6;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__8;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Nat_repr(x_11);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__10;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_ctor_get(x_3, 0);
lean_inc(x_53);
x_54 = l_Nat_repr(x_53);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__12;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_wakeUp___spec__1(x_20, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_60;
}
else
{
uint8_t x_61; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_32);
if (x_61 == 0)
{
return x_32;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_32, 0);
x_63 = lean_ctor_get(x_32, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_32);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Meta_SynthInstance_addAnswer___spec__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_addAnswer___lambda__4), 9, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Meta_SynthInstance_addAnswer___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(x_9, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Meta_SynthInstance_addAnswer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_ReaderT_read___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_addAnswer___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_addAnswer___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_addAnswer___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_addAnswer___spec__3(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_addAnswer___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_addAnswer___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
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
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
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
x_17 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_1, x_15);
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
uint8_t x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_1, x_21);
lean_dec(x_21);
if (x_23 == 0)
{
x_2 = x_12;
x_7 = x_22;
goto _start;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_inc(x_14);
x_15 = l_Lean_Expr_fvarId_x21(x_14);
x_16 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_15, x_1);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_List_anyM___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__1(x_15, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_14);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_3 = x_13;
x_10 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
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
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_inc(x_14);
x_15 = l_Lean_Expr_fvarId_x21(x_14);
x_16 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_15, x_1);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_List_anyM___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__1(x_15, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_14);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_3 = x_13;
x_10 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
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
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unusedArgs", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_3 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nhas unused arguments, reduced type", 35);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nTransformer", 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
lean_inc(x_5);
x_11 = l_Lean_mkAppN(x_5, x_1);
x_12 = 0;
x_13 = 1;
x_14 = 1;
x_15 = l_Lean_Meta_mkLambdaFVars(x_2, x_11, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__3;
x_19 = lean_array_push(x_18, x_5);
x_20 = l_Lean_Meta_mkLambdaFVars(x_19, x_16, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__2;
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_23, x_6, x_7, x_8, x_9, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__1(x_3, x_21, x_28, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_8);
lean_dec(x_6);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_4);
x_32 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_3);
x_36 = l_Lean_indentExpr(x_3);
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__6;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_21);
x_40 = l_Lean_indentExpr(x_21);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_32);
x_43 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_23, x_42, x_6, x_7, x_8, x_9, x_30);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__1(x_3, x_21, x_44, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_20);
if (x_47 == 0)
{
return x_20;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_20, 0);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_20);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_15);
if (x_51 == 0)
{
return x_15;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_15, 0);
x_53 = lean_ctor_get(x_15, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_15);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("redf", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_box(0);
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_le(x_10, x_10);
if (x_11 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_10);
if (x_34 == 0)
{
lean_dec(x_10);
x_12 = x_9;
x_13 = x_8;
goto block_32;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_36 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__3(x_3, x_2, x_35, x_36, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_12 = x_38;
x_13 = x_39;
goto block_32;
}
else
{
uint8_t x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
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
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_lt(x_44, x_10);
if (x_45 == 0)
{
lean_dec(x_10);
x_12 = x_9;
x_13 = x_8;
goto block_32;
}
else
{
size_t x_46; size_t x_47; lean_object* x_48; 
x_46 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_47 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_48 = l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__4(x_3, x_2, x_46, x_47, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_12 = x_49;
x_13 = x_50;
goto block_32;
}
else
{
uint8_t x_51; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
block_32:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = l_List_redLength___rarg(x_12);
x_15 = lean_mk_empty_array_with_capacity(x_14);
lean_dec(x_14);
x_16 = l_List_toArrayAux___rarg(x_12, x_15);
x_17 = 0;
x_18 = 1;
x_19 = 1;
lean_inc(x_16);
x_20 = l_Lean_Meta_mkForallFVars(x_16, x_3, x_17, x_18, x_19, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_21);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___boxed), 10, 4);
lean_closure_set(x_23, 0, x_16);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_1);
x_24 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__2;
x_25 = 0;
x_26 = 0;
x_27 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_24, x_25, x_21, x_23, x_26, x_4, x_5, x_6, x_7, x_22);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_8, x_2, x_3, x_4, x_5, x_9);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_10);
lean_inc(x_12);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3), 8, 1);
lean_closure_set(x_16, 0, x_12);
x_17 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_12, x_16, x_2, x_3, x_4, x_5, x_13);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_hasUnusedArguments(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_inc(x_18);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3), 8, 1);
lean_closure_set(x_23, 0, x_18);
x_24 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_18, x_23, x_2, x_3, x_4, x_5, x_19);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__4), 6, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__7___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_anyM___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__3(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__4(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__3;
x_13 = lean_array_push(x_12, x_4);
x_14 = 0;
x_15 = l_Lean_Expr_betaRev(x_1, x_13, x_14, x_14);
lean_dec(x_13);
lean_inc(x_15);
x_16 = lean_infer_type(x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_2, 2);
lean_dec(x_20);
lean_ctor_set(x_2, 2, x_15);
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_15);
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_16, 0, x_28);
return x_16;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_33 = x_2;
} else {
 lean_dec_ref(x_2);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 3, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_15);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_15);
lean_dec(x_2);
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
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_array_uget(x_5, x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_5, x_4, x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1___boxed), 8, 1);
lean_closure_set(x_20, 0, x_19);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__1___boxed), 11, 3);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_18);
lean_closure_set(x_21, 2, x_15);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_23 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(x_1, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_28 = lean_array_uset(x_17, x_4, x_24);
x_4 = x_27;
x_5 = x_28;
x_12 = x_25;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
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
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
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
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_box(0);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_consume___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_consume___lambda__2___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_addAnswer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_15);
lean_inc(x_13);
x_17 = l_Lean_Meta_SynthInstance_mkTableKeyFor(x_13, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_18);
x_20 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
lean_inc(x_13);
x_23 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f(x_13, x_15, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_1);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_SynthInstance_newSubgoal(x_13, x_18, x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_18);
lean_dec(x_15);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
lean_inc(x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2___boxed), 8, 1);
lean_closure_set(x_32, 0, x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_33 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(x_13, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_34);
x_36 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_1);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_ctor_set(x_24, 0, x_30);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_consume___lambda__1___boxed), 8, 1);
lean_closure_set(x_39, 0, x_24);
x_40 = l_Lean_Meta_SynthInstance_consume___closed__1;
x_41 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 2);
lean_closure_set(x_41, 0, x_39);
lean_closure_set(x_41, 1, x_40);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_42 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(x_13, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
lean_inc(x_46);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_9);
lean_inc(x_45);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_11);
lean_ctor_set(x_48, 1, x_12);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 4, x_14);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_Meta_SynthInstance_newSubgoal(x_45, x_34, x_46, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_44);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_34);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_42);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
x_55 = lean_ctor_get(x_37, 0);
lean_inc(x_55);
lean_dec(x_37);
x_56 = lean_ctor_get(x_36, 1);
lean_inc(x_56);
lean_dec(x_36);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_ctor_get(x_55, 1);
x_60 = lean_array_get_size(x_59);
x_61 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_62 = 0;
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_59);
x_63 = l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1(x_13, x_31, x_61, x_62, x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_st_ref_get(x_7, x_65);
lean_dec(x_7);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_st_ref_take(x_3, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_69, 2);
x_73 = lean_ctor_get(x_69, 3);
x_74 = lean_array_get_size(x_64);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_lt(x_75, x_74);
x_77 = lean_array_push(x_58, x_16);
lean_ctor_set(x_55, 0, x_77);
x_78 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_73, x_34, x_55);
if (x_76 == 0)
{
lean_object* x_79; uint8_t x_80; 
lean_dec(x_74);
lean_dec(x_64);
lean_dec(x_1);
lean_ctor_set(x_69, 3, x_78);
x_79 = lean_st_ref_set(x_3, x_69, x_70);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
x_82 = lean_box(0);
lean_ctor_set(x_79, 0, x_82);
return x_79;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_74, x_74);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
lean_dec(x_74);
lean_dec(x_64);
lean_dec(x_1);
lean_ctor_set(x_69, 3, x_78);
x_87 = lean_st_ref_set(x_3, x_69, x_70);
lean_dec(x_3);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
x_90 = lean_box(0);
lean_ctor_set(x_87, 0, x_90);
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
size_t x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_95 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2(x_1, x_64, x_62, x_94, x_72);
lean_dec(x_64);
lean_ctor_set(x_69, 3, x_78);
lean_ctor_set(x_69, 2, x_95);
x_96 = lean_st_ref_set(x_3, x_69, x_70);
lean_dec(x_3);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_96, 0);
lean_dec(x_98);
x_99 = lean_box(0);
lean_ctor_set(x_96, 0, x_99);
return x_96;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_69, 0);
x_104 = lean_ctor_get(x_69, 1);
x_105 = lean_ctor_get(x_69, 2);
x_106 = lean_ctor_get(x_69, 3);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_69);
x_107 = lean_array_get_size(x_64);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_nat_dec_lt(x_108, x_107);
x_110 = lean_array_push(x_58, x_16);
lean_ctor_set(x_55, 0, x_110);
x_111 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_106, x_34, x_55);
if (x_109 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_107);
lean_dec(x_64);
lean_dec(x_1);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_103);
lean_ctor_set(x_112, 1, x_104);
lean_ctor_set(x_112, 2, x_105);
lean_ctor_set(x_112, 3, x_111);
x_113 = lean_st_ref_set(x_3, x_112, x_70);
lean_dec(x_3);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
x_116 = lean_box(0);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
else
{
uint8_t x_118; 
x_118 = lean_nat_dec_le(x_107, x_107);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_107);
lean_dec(x_64);
lean_dec(x_1);
x_119 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_119, 0, x_103);
lean_ctor_set(x_119, 1, x_104);
lean_ctor_set(x_119, 2, x_105);
lean_ctor_set(x_119, 3, x_111);
x_120 = lean_st_ref_set(x_3, x_119, x_70);
lean_dec(x_3);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
else
{
size_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_126 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2(x_1, x_64, x_62, x_125, x_105);
lean_dec(x_64);
x_127 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_127, 0, x_103);
lean_ctor_set(x_127, 1, x_104);
lean_ctor_set(x_127, 2, x_126);
lean_ctor_set(x_127, 3, x_111);
x_128 = lean_st_ref_set(x_3, x_127, x_70);
lean_dec(x_3);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
x_131 = lean_box(0);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
}
}
}
else
{
uint8_t x_133; 
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_34);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_63);
if (x_133 == 0)
{
return x_63;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_63, 0);
x_135 = lean_ctor_get(x_63, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_63);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; size_t x_140; size_t x_141; lean_object* x_142; 
x_137 = lean_ctor_get(x_55, 0);
x_138 = lean_ctor_get(x_55, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_55);
x_139 = lean_array_get_size(x_138);
x_140 = lean_usize_of_nat(x_139);
lean_dec(x_139);
x_141 = 0;
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_138);
x_142 = l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1(x_13, x_31, x_140, x_141, x_138, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_st_ref_get(x_7, x_144);
lean_dec(x_7);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_st_ref_take(x_3, x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_148, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_148, 3);
lean_inc(x_153);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 x_154 = x_148;
} else {
 lean_dec_ref(x_148);
 x_154 = lean_box(0);
}
x_155 = lean_array_get_size(x_143);
x_156 = lean_unsigned_to_nat(0u);
x_157 = lean_nat_dec_lt(x_156, x_155);
x_158 = lean_array_push(x_137, x_16);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_138);
x_160 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_153, x_34, x_159);
if (x_157 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_155);
lean_dec(x_143);
lean_dec(x_1);
if (lean_is_scalar(x_154)) {
 x_161 = lean_alloc_ctor(0, 4, 0);
} else {
 x_161 = x_154;
}
lean_ctor_set(x_161, 0, x_150);
lean_ctor_set(x_161, 1, x_151);
lean_ctor_set(x_161, 2, x_152);
lean_ctor_set(x_161, 3, x_160);
x_162 = lean_st_ref_set(x_3, x_161, x_149);
lean_dec(x_3);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
x_165 = lean_box(0);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
else
{
uint8_t x_167; 
x_167 = lean_nat_dec_le(x_155, x_155);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_155);
lean_dec(x_143);
lean_dec(x_1);
if (lean_is_scalar(x_154)) {
 x_168 = lean_alloc_ctor(0, 4, 0);
} else {
 x_168 = x_154;
}
lean_ctor_set(x_168, 0, x_150);
lean_ctor_set(x_168, 1, x_151);
lean_ctor_set(x_168, 2, x_152);
lean_ctor_set(x_168, 3, x_160);
x_169 = lean_st_ref_set(x_3, x_168, x_149);
lean_dec(x_3);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
x_172 = lean_box(0);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_170);
return x_173;
}
else
{
size_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_174 = lean_usize_of_nat(x_155);
lean_dec(x_155);
x_175 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2(x_1, x_143, x_141, x_174, x_152);
lean_dec(x_143);
if (lean_is_scalar(x_154)) {
 x_176 = lean_alloc_ctor(0, 4, 0);
} else {
 x_176 = x_154;
}
lean_ctor_set(x_176, 0, x_150);
lean_ctor_set(x_176, 1, x_151);
lean_ctor_set(x_176, 2, x_175);
lean_ctor_set(x_176, 3, x_160);
x_177 = lean_st_ref_set(x_3, x_176, x_149);
lean_dec(x_3);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
x_180 = lean_box(0);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_34);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_182 = lean_ctor_get(x_142, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_142, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_184 = x_142;
} else {
 lean_dec_ref(x_142);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_33);
if (x_186 == 0)
{
return x_33;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_33, 0);
x_188 = lean_ctor_get(x_33, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_33);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_190 = lean_ctor_get(x_24, 0);
lean_inc(x_190);
lean_dec(x_24);
x_191 = lean_ctor_get(x_23, 1);
lean_inc(x_191);
lean_dec(x_23);
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec(x_190);
lean_inc(x_192);
x_194 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2___boxed), 8, 1);
lean_closure_set(x_194, 0, x_192);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_195 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(x_13, x_194, x_2, x_3, x_4, x_5, x_6, x_7, x_191);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
lean_inc(x_196);
x_198 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_196, x_2, x_3, x_4, x_5, x_6, x_7, x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_193);
lean_dec(x_16);
lean_dec(x_1);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_192);
x_202 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_consume___lambda__1___boxed), 8, 1);
lean_closure_set(x_202, 0, x_201);
x_203 = l_Lean_Meta_SynthInstance_consume___closed__1;
x_204 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 2);
lean_closure_set(x_204, 0, x_202);
lean_closure_set(x_204, 1, x_203);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_205 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(x_13, x_204, x_2, x_3, x_4, x_5, x_6, x_7, x_200);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_ctor_get(x_206, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec(x_206);
lean_inc(x_209);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_9);
lean_inc(x_208);
x_211 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_211, 0, x_11);
lean_ctor_set(x_211, 1, x_12);
lean_ctor_set(x_211, 2, x_208);
lean_ctor_set(x_211, 3, x_210);
lean_ctor_set(x_211, 4, x_14);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_213 = l_Lean_Meta_SynthInstance_newSubgoal(x_208, x_196, x_209, x_212, x_2, x_3, x_4, x_5, x_6, x_7, x_207);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_196);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_214 = lean_ctor_get(x_205, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_205, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_216 = x_205;
} else {
 lean_dec_ref(x_205);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; size_t x_224; size_t x_225; lean_object* x_226; 
lean_dec(x_192);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
x_218 = lean_ctor_get(x_199, 0);
lean_inc(x_218);
lean_dec(x_199);
x_219 = lean_ctor_get(x_198, 1);
lean_inc(x_219);
lean_dec(x_198);
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_222 = x_218;
} else {
 lean_dec_ref(x_218);
 x_222 = lean_box(0);
}
x_223 = lean_array_get_size(x_221);
x_224 = lean_usize_of_nat(x_223);
lean_dec(x_223);
x_225 = 0;
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_221);
x_226 = l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1(x_13, x_193, x_224, x_225, x_221, x_2, x_3, x_4, x_5, x_6, x_7, x_219);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_st_ref_get(x_7, x_228);
lean_dec(x_7);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_231 = lean_st_ref_take(x_3, x_230);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_232, 2);
lean_inc(x_236);
x_237 = lean_ctor_get(x_232, 3);
lean_inc(x_237);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 lean_ctor_release(x_232, 2);
 lean_ctor_release(x_232, 3);
 x_238 = x_232;
} else {
 lean_dec_ref(x_232);
 x_238 = lean_box(0);
}
x_239 = lean_array_get_size(x_227);
x_240 = lean_unsigned_to_nat(0u);
x_241 = lean_nat_dec_lt(x_240, x_239);
x_242 = lean_array_push(x_220, x_16);
if (lean_is_scalar(x_222)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_222;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_221);
x_244 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_237, x_196, x_243);
if (x_241 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_239);
lean_dec(x_227);
lean_dec(x_1);
if (lean_is_scalar(x_238)) {
 x_245 = lean_alloc_ctor(0, 4, 0);
} else {
 x_245 = x_238;
}
lean_ctor_set(x_245, 0, x_234);
lean_ctor_set(x_245, 1, x_235);
lean_ctor_set(x_245, 2, x_236);
lean_ctor_set(x_245, 3, x_244);
x_246 = lean_st_ref_set(x_3, x_245, x_233);
lean_dec(x_3);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_248 = x_246;
} else {
 lean_dec_ref(x_246);
 x_248 = lean_box(0);
}
x_249 = lean_box(0);
if (lean_is_scalar(x_248)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_248;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_247);
return x_250;
}
else
{
uint8_t x_251; 
x_251 = lean_nat_dec_le(x_239, x_239);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_239);
lean_dec(x_227);
lean_dec(x_1);
if (lean_is_scalar(x_238)) {
 x_252 = lean_alloc_ctor(0, 4, 0);
} else {
 x_252 = x_238;
}
lean_ctor_set(x_252, 0, x_234);
lean_ctor_set(x_252, 1, x_235);
lean_ctor_set(x_252, 2, x_236);
lean_ctor_set(x_252, 3, x_244);
x_253 = lean_st_ref_set(x_3, x_252, x_233);
lean_dec(x_3);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
x_256 = lean_box(0);
if (lean_is_scalar(x_255)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_255;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_254);
return x_257;
}
else
{
size_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_258 = lean_usize_of_nat(x_239);
lean_dec(x_239);
x_259 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2(x_1, x_227, x_225, x_258, x_236);
lean_dec(x_227);
if (lean_is_scalar(x_238)) {
 x_260 = lean_alloc_ctor(0, 4, 0);
} else {
 x_260 = x_238;
}
lean_ctor_set(x_260, 0, x_234);
lean_ctor_set(x_260, 1, x_235);
lean_ctor_set(x_260, 2, x_259);
lean_ctor_set(x_260, 3, x_244);
x_261 = lean_st_ref_set(x_3, x_260, x_233);
lean_dec(x_3);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
x_264 = lean_box(0);
if (lean_is_scalar(x_263)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_263;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_262);
return x_265;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_196);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_266 = lean_ctor_get(x_226, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_226, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_268 = x_226;
} else {
 lean_dec_ref(x_226);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = lean_ctor_get(x_195, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_195, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_272 = x_195;
} else {
 lean_dec_ref(x_195);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_23);
if (x_274 == 0)
{
return x_23;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_23, 0);
x_276 = lean_ctor_get(x_23, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_23);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
return x_277;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_278 = lean_ctor_get(x_20, 1);
lean_inc(x_278);
lean_dec(x_20);
x_279 = lean_ctor_get(x_21, 0);
lean_inc(x_279);
lean_dec(x_21);
x_280 = lean_st_ref_get(x_7, x_278);
lean_dec(x_7);
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
lean_dec(x_280);
x_282 = lean_st_ref_take(x_3, x_281);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = !lean_is_exclusive(x_283);
if (x_285 == 0)
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_279);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; 
x_287 = lean_ctor_get(x_283, 2);
x_288 = lean_ctor_get(x_283, 3);
x_289 = lean_ctor_get(x_279, 0);
x_290 = lean_ctor_get(x_279, 1);
x_291 = lean_array_get_size(x_290);
x_292 = lean_unsigned_to_nat(0u);
x_293 = lean_nat_dec_lt(x_292, x_291);
x_294 = lean_array_push(x_289, x_16);
lean_inc(x_290);
lean_ctor_set(x_279, 0, x_294);
x_295 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_288, x_18, x_279);
if (x_293 == 0)
{
lean_object* x_296; uint8_t x_297; 
lean_dec(x_291);
lean_dec(x_290);
lean_dec(x_1);
lean_ctor_set(x_283, 3, x_295);
x_296 = lean_st_ref_set(x_3, x_283, x_284);
lean_dec(x_3);
x_297 = !lean_is_exclusive(x_296);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_296, 0);
lean_dec(x_298);
x_299 = lean_box(0);
lean_ctor_set(x_296, 0, x_299);
return x_296;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_296, 1);
lean_inc(x_300);
lean_dec(x_296);
x_301 = lean_box(0);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
else
{
uint8_t x_303; 
x_303 = lean_nat_dec_le(x_291, x_291);
if (x_303 == 0)
{
lean_object* x_304; uint8_t x_305; 
lean_dec(x_291);
lean_dec(x_290);
lean_dec(x_1);
lean_ctor_set(x_283, 3, x_295);
x_304 = lean_st_ref_set(x_3, x_283, x_284);
lean_dec(x_3);
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_304, 0);
lean_dec(x_306);
x_307 = lean_box(0);
lean_ctor_set(x_304, 0, x_307);
return x_304;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_304, 1);
lean_inc(x_308);
lean_dec(x_304);
x_309 = lean_box(0);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
else
{
size_t x_311; size_t x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_311 = 0;
x_312 = lean_usize_of_nat(x_291);
lean_dec(x_291);
x_313 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3(x_1, x_290, x_311, x_312, x_287);
lean_dec(x_290);
lean_ctor_set(x_283, 3, x_295);
lean_ctor_set(x_283, 2, x_313);
x_314 = lean_st_ref_set(x_3, x_283, x_284);
lean_dec(x_3);
x_315 = !lean_is_exclusive(x_314);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_314, 0);
lean_dec(x_316);
x_317 = lean_box(0);
lean_ctor_set(x_314, 0, x_317);
return x_314;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_314, 1);
lean_inc(x_318);
lean_dec(x_314);
x_319 = lean_box(0);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_321 = lean_ctor_get(x_283, 2);
x_322 = lean_ctor_get(x_283, 3);
x_323 = lean_ctor_get(x_279, 0);
x_324 = lean_ctor_get(x_279, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_279);
x_325 = lean_array_get_size(x_324);
x_326 = lean_unsigned_to_nat(0u);
x_327 = lean_nat_dec_lt(x_326, x_325);
x_328 = lean_array_push(x_323, x_16);
lean_inc(x_324);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_324);
x_330 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_322, x_18, x_329);
if (x_327 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_1);
lean_ctor_set(x_283, 3, x_330);
x_331 = lean_st_ref_set(x_3, x_283, x_284);
lean_dec(x_3);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_333 = x_331;
} else {
 lean_dec_ref(x_331);
 x_333 = lean_box(0);
}
x_334 = lean_box(0);
if (lean_is_scalar(x_333)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_333;
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_332);
return x_335;
}
else
{
uint8_t x_336; 
x_336 = lean_nat_dec_le(x_325, x_325);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_1);
lean_ctor_set(x_283, 3, x_330);
x_337 = lean_st_ref_set(x_3, x_283, x_284);
lean_dec(x_3);
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_339 = x_337;
} else {
 lean_dec_ref(x_337);
 x_339 = lean_box(0);
}
x_340 = lean_box(0);
if (lean_is_scalar(x_339)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_339;
}
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_338);
return x_341;
}
else
{
size_t x_342; size_t x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_342 = 0;
x_343 = lean_usize_of_nat(x_325);
lean_dec(x_325);
x_344 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3(x_1, x_324, x_342, x_343, x_321);
lean_dec(x_324);
lean_ctor_set(x_283, 3, x_330);
lean_ctor_set(x_283, 2, x_344);
x_345 = lean_st_ref_set(x_3, x_283, x_284);
lean_dec(x_3);
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_347 = x_345;
} else {
 lean_dec_ref(x_345);
 x_347 = lean_box(0);
}
x_348 = lean_box(0);
if (lean_is_scalar(x_347)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_347;
}
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_346);
return x_349;
}
}
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_350 = lean_ctor_get(x_283, 0);
x_351 = lean_ctor_get(x_283, 1);
x_352 = lean_ctor_get(x_283, 2);
x_353 = lean_ctor_get(x_283, 3);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_283);
x_354 = lean_ctor_get(x_279, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_279, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_356 = x_279;
} else {
 lean_dec_ref(x_279);
 x_356 = lean_box(0);
}
x_357 = lean_array_get_size(x_355);
x_358 = lean_unsigned_to_nat(0u);
x_359 = lean_nat_dec_lt(x_358, x_357);
x_360 = lean_array_push(x_354, x_16);
lean_inc(x_355);
if (lean_is_scalar(x_356)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_356;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_355);
x_362 = l_Lean_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_353, x_18, x_361);
if (x_359 == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_357);
lean_dec(x_355);
lean_dec(x_1);
x_363 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_363, 0, x_350);
lean_ctor_set(x_363, 1, x_351);
lean_ctor_set(x_363, 2, x_352);
lean_ctor_set(x_363, 3, x_362);
x_364 = lean_st_ref_set(x_3, x_363, x_284);
lean_dec(x_3);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_366 = x_364;
} else {
 lean_dec_ref(x_364);
 x_366 = lean_box(0);
}
x_367 = lean_box(0);
if (lean_is_scalar(x_366)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_366;
}
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_365);
return x_368;
}
else
{
uint8_t x_369; 
x_369 = lean_nat_dec_le(x_357, x_357);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_357);
lean_dec(x_355);
lean_dec(x_1);
x_370 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_370, 0, x_350);
lean_ctor_set(x_370, 1, x_351);
lean_ctor_set(x_370, 2, x_352);
lean_ctor_set(x_370, 3, x_362);
x_371 = lean_st_ref_set(x_3, x_370, x_284);
lean_dec(x_3);
x_372 = lean_ctor_get(x_371, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_373 = x_371;
} else {
 lean_dec_ref(x_371);
 x_373 = lean_box(0);
}
x_374 = lean_box(0);
if (lean_is_scalar(x_373)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_373;
}
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_372);
return x_375;
}
else
{
size_t x_376; size_t x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_376 = 0;
x_377 = lean_usize_of_nat(x_357);
lean_dec(x_357);
x_378 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3(x_1, x_355, x_376, x_377, x_352);
lean_dec(x_355);
x_379 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_379, 0, x_350);
lean_ctor_set(x_379, 1, x_351);
lean_ctor_set(x_379, 2, x_378);
lean_ctor_set(x_379, 3, x_362);
x_380 = lean_st_ref_set(x_3, x_379, x_284);
lean_dec(x_3);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_382 = x_380;
} else {
 lean_dec_ref(x_380);
 x_382 = lean_box(0);
}
x_383 = lean_box(0);
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_381);
return x_384;
}
}
}
}
}
else
{
uint8_t x_385; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_385 = !lean_is_exclusive(x_17);
if (x_385 == 0)
{
return x_17;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_17, 0);
x_387 = lean_ctor_get(x_17, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_17);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_consume___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_consume___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode;
x_14 = l_Array_back___rarg(x_13, x_12);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode;
x_19 = l_Array_back___rarg(x_18, x_17);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getTop___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_getTop___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_getTop(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_16, x_17);
x_19 = lean_nat_dec_lt(x_18, x_16);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_18);
lean_dec(x_1);
x_20 = lean_st_ref_set(x_3, x_12, x_13);
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
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_array_fget(x_15, x_18);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_15, x_18, x_28);
x_30 = lean_apply_1(x_1, x_27);
x_31 = lean_array_fset(x_29, x_18, x_30);
lean_dec(x_18);
lean_ctor_set(x_12, 1, x_31);
x_32 = lean_st_ref_set(x_3, x_12, x_13);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_28);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
x_39 = lean_ctor_get(x_12, 2);
x_40 = lean_ctor_get(x_12, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_41 = lean_array_get_size(x_38);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_41, x_42);
x_44 = lean_nat_dec_lt(x_43, x_41);
lean_dec(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
lean_dec(x_1);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_38);
lean_ctor_set(x_45, 2, x_39);
lean_ctor_set(x_45, 3, x_40);
x_46 = lean_st_ref_set(x_3, x_45, x_13);
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
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_array_fget(x_38, x_43);
x_52 = lean_box(0);
x_53 = lean_array_fset(x_38, x_43, x_52);
x_54 = lean_apply_1(x_1, x_51);
x_55 = lean_array_fset(x_53, x_43, x_54);
lean_dec(x_43);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_37);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_39);
lean_ctor_set(x_56, 3, x_40);
x_57 = lean_st_ref_set(x_3, x_56, x_13);
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
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_modifyTop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_generate___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_generate___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_9, 5);
lean_inc(x_18);
x_19 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg(x_10, x_17);
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
x_22 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_25);
x_26 = lean_apply_8(x_2, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_9);
x_29 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__12(x_20, x_1, x_18, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_generate___spec__2(x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_25);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_22, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_dec(x_22);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_36);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_38);
x_39 = lean_apply_8(x_2, x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_9);
x_42 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_SynthInstance_newSubgoal___spec__12(x_20, x_1, x_18, x_40, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_generate___spec__2(x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_38);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_38);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" apply ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_generate___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" to ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_generate___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = lean_infer_type(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_exceptOptionEmoji___rarg(x_3);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_2);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_SynthInstance_generate___lambda__1___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_16);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_14, 0, x_29);
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = l_Lean_exceptOptionEmoji___rarg(x_3);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_2);
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_SynthInstance_generate___lambda__1___closed__4;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_30);
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_34);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_31);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 4);
lean_dec(x_4);
lean_ctor_set(x_2, 4, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 4, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_generate___lambda__3___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_Meta_SynthInstance_tryResolve(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_SynthInstance_generate___lambda__4___closed__1;
x_16 = lean_box(0);
x_17 = lean_apply_8(x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set(x_23, 4, x_22);
x_24 = l_Lean_Meta_SynthInstance_consume(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = l_Lean_Meta_SynthInstance_generate___lambda__4___closed__2;
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lean_Meta_SynthInstance_generate___lambda__4___closed__2;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_12);
if (x_35 == 0)
{
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = l_Lean_Meta_SynthInstance_getTop___rarg(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 4);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_array_get(x_20, x_14, x_19);
lean_dec(x_14);
lean_inc(x_21);
lean_inc(x_11);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_generate___lambda__1___boxed), 10, 2);
lean_closure_set(x_22, 0, x_11);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_generate___lambda__2), 2, 1);
lean_closure_set(x_23, 0, x_19);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_modifyTop___boxed), 8, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_generate___lambda__4___boxed), 11, 3);
lean_closure_set(x_25, 0, x_11);
lean_closure_set(x_25, 1, x_21);
lean_closure_set(x_25, 2, x_12);
x_26 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_generate___spec__1___boxed), 11, 4);
lean_closure_set(x_30, 0, x_27);
lean_closure_set(x_30, 1, x_22);
lean_closure_set(x_30, 2, x_26);
lean_closure_set(x_30, 3, x_29);
x_31 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(x_13, x_30, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_st_ref_get(x_6, x_10);
lean_dec(x_6);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_st_ref_take(x_2, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_array_pop(x_48);
lean_ctor_set(x_45, 1, x_49);
x_50 = lean_st_ref_set(x_2, x_45, x_46);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_45, 0);
x_58 = lean_ctor_get(x_45, 1);
x_59 = lean_ctor_get(x_45, 2);
x_60 = lean_ctor_get(x_45, 3);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_45);
x_61 = lean_array_pop(x_58);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_60);
x_63 = lean_st_ref_set(x_2, x_62, x_46);
lean_dec(x_2);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_generate___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_MonadExcept_ofExcept___at_Lean_Meta_SynthInstance_generate___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_generate___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_generate___spec__1(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_SynthInstance_generate___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_generate___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_SynthInstance_generate___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getNextToResume___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedConsumerNode;
x_2 = l_Lean_Meta_SynthInstance_instInhabitedAnswer;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_SynthInstance_getNextToResume___rarg___closed__1;
x_14 = l_Array_back___rarg(x_13, x_12);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_5, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_1, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 2);
x_22 = lean_array_pop(x_21);
lean_ctor_set(x_18, 2, x_22);
x_23 = lean_st_ref_set(x_1, x_18, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_14);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_32 = lean_array_pop(x_30);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_31);
x_34 = lean_st_ref_set(x_1, x_33, x_19);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_14);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getNextToResume___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_getNextToResume___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_getNextToResume(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_SynthInstance_resume___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("propagating ", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" to subgoal ", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" of ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_3);
x_18 = l_Lean_Meta_SynthInstance_resume___lambda__1___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_SynthInstance_resume___lambda__1___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_12);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Meta_SynthInstance_resume___lambda__1___closed__6;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_16);
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_14, 0, x_29);
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_3);
x_33 = l_Lean_Meta_SynthInstance_resume___lambda__1___closed__2;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Meta_SynthInstance_resume___lambda__1___closed__4;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_12);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Meta_SynthInstance_resume___lambda__1___closed__6;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_30);
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_31);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1___boxed), 8, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lambda__1___boxed), 10, 2);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_3);
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_nat_add(x_2, x_15);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_17, 2, x_5);
lean_ctor_set(x_17, 3, x_6);
lean_ctor_set(x_17, 4, x_16);
x_18 = l_Lean_Meta_SynthInstance_consume(x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (x_8 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = l_Lean_Meta_SynthInstance_resume___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_nat_add(x_2, x_18);
x_20 = l_Nat_repr(x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_wakeUp___spec__1(x_7, x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_SynthInstance_resume___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_28, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
lean_dec(x_28);
return x_30;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("resume", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_3 = l_Lean_Meta_SynthInstance_resume___lambda__5___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___lambda__5___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___boxed), 8, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_17 = lean_infer_type(x_1, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lambda__2___boxed), 12, 4);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_9);
lean_closure_set(x_20, 3, x_3);
x_21 = l_Lean_Meta_SynthInstance_resume___lambda__5___closed__2;
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lambda__4___boxed), 15, 7);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_4);
lean_closure_set(x_22, 2, x_5);
lean_closure_set(x_22, 3, x_6);
lean_closure_set(x_22, 4, x_7);
lean_closure_set(x_22, 5, x_8);
lean_closure_set(x_22, 6, x_21);
x_23 = l_Lean_Meta_SynthInstance_resume___lambda__5___closed__3;
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_22);
x_25 = 1;
x_26 = l_Lean_withTraceNode___at_Lean_Meta_SynthInstance_addAnswer___spec__3(x_21, x_20, x_24, x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_14);
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
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.SynthInstance.resume", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("resume found no remaining subgoals", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__1;
x_2 = l_Lean_Meta_SynthInstance_resume___closed__1;
x_3 = lean_unsigned_to_nat(543u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Meta_SynthInstance_resume___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Meta_SynthInstance_getNextToResume___rarg(x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_dec(x_8);
x_13 = l_Lean_Meta_SynthInstance_resume___closed__3;
x_14 = l_panic___at_Lean_Meta_SynthInstance_resume___spec__1(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 4);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_16);
lean_inc(x_21);
lean_inc(x_19);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
lean_inc(x_17);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1___boxed), 8, 1);
lean_closure_set(x_33, 0, x_17);
lean_inc(x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lambda__5), 16, 8);
lean_closure_set(x_34, 0, x_21);
lean_closure_set(x_34, 1, x_16);
lean_closure_set(x_34, 2, x_19);
lean_closure_set(x_34, 3, x_20);
lean_closure_set(x_34, 4, x_17);
lean_closure_set(x_34, 5, x_18);
lean_closure_set(x_34, 6, x_32);
lean_closure_set(x_34, 7, x_22);
x_35 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___rarg), 9, 2);
lean_closure_set(x_35, 0, x_33);
lean_closure_set(x_35, 1, x_34);
x_36 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__14___rarg(x_32, x_35, x_1, x_2, x_3, x_4, x_5, x_6, x_31);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_SynthInstance_resume___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_SynthInstance_resume___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_SynthInstance_resume___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_8);
lean_dec(x_8);
x_17 = l_Lean_Meta_SynthInstance_resume___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_checkMaxHeartbeats(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
x_17 = l_Array_isEmpty___rarg(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_12);
lean_dec(x_14);
x_18 = l_Lean_Meta_SynthInstance_resume(x_1, x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = l_Array_isEmpty___rarg(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_free_object(x_12);
x_33 = l_Lean_Meta_SynthInstance_generate(x_1, x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = 1;
x_37 = lean_box(x_36);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = 1;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; lean_object* x_47; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = 0;
x_47 = lean_box(x_46);
lean_ctor_set(x_12, 0, x_47);
return x_12;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_12, 0);
x_49 = lean_ctor_get(x_12, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_12);
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
x_51 = l_Array_isEmpty___rarg(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_48);
x_52 = l_Lean_Meta_SynthInstance_resume(x_1, x_2, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
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
x_55 = 1;
x_56 = lean_box(x_55);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_60 = x_52;
} else {
 lean_dec_ref(x_52);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_dec(x_48);
x_63 = l_Array_isEmpty___rarg(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_Meta_SynthInstance_generate(x_1, x_2, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
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
x_67 = 1;
x_68 = lean_box(x_67);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = 0;
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_49);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_8);
if (x_77 == 0)
{
return x_8;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_8, 0);
x_79 = lean_ctor_get(x_8, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_8);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getResult___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_getResult___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_getResult(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_synth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_8);
x_18 = l_Lean_Meta_SynthInstance_getResult___rarg(x_2, x_3, x_4, x_5, x_6, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_7 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_29 = x_19;
} else {
 lean_dec_ref(x_19);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1;
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_12);
x_16 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_1, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_5, x_11);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_3, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_19);
x_27 = lean_st_ref_set(x_3, x_23, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_17);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_23, 1);
x_33 = lean_ctor_get(x_23, 2);
x_34 = lean_ctor_get(x_23, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_st_ref_set(x_3, x_35, x_24);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_SynthInstance_main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_Lean_Meta_SynthInstance_main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___rarg(x_7, x_4, x_5, x_6);
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
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to synthesize", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_3 = l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_9 = 0;
x_10 = lean_box(0);
lean_inc(x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
x_14 = l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_main___spec__1(x_2, x_4, x_5, x_6, x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_33 = lean_ctor_get(x_6, 2);
lean_inc(x_33);
x_34 = l_Lean_Meta_SynthInstance_getMaxHeartbeats(x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_st_ref_get(x_7, x_16);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__5;
x_39 = lean_st_mk_ref(x_38, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_st_ref_get(x_7, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_st_ref_get(x_5, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_40);
lean_inc(x_35);
x_49 = l_Lean_Meta_SynthInstance_newSubgoal(x_47, x_15, x_12, x_48, x_35, x_40, x_4, x_5, x_6, x_7, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_40);
x_51 = l_Lean_Meta_SynthInstance_synth(x_35, x_40, x_4, x_5, x_6, x_7, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_st_ref_get(x_7, x_53);
lean_dec(x_7);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_get(x_40, x_55);
lean_dec(x_40);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_52);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_40);
x_61 = lean_ctor_get(x_51, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_51, 1);
lean_inc(x_62);
lean_dec(x_51);
x_18 = x_61;
x_19 = x_62;
goto block_32;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_40);
lean_dec(x_35);
x_63 = lean_ctor_get(x_49, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_49, 1);
lean_inc(x_64);
lean_dec(x_49);
x_18 = x_63;
x_19 = x_64;
goto block_32;
}
block_32:
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isMaxHeartbeat(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_17;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_17);
x_22 = l_Lean_indentExpr(x_2);
x_23 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Exception_toMessageData(x_18);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_Meta_SynthInstance_main___spec__2(x_30, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_main___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_Core_withCurrHeartbeats___at_Lean_Meta_SynthInstance_main___spec__3(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_mkTableKey___at_Lean_Meta_SynthInstance_main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_SynthInstance_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_SynthInstance_main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_whnf(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
x_12 = 1;
x_13 = 1;
x_14 = l_Lean_Meta_mkForallFVars(x_1, x_9, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1;
x_8 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = l_Lean_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_9, x_3, x_4, x_5, x_6, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Level_hasMVar(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_array_push(x_13, x_15);
lean_ctor_set(x_2, 1, x_18);
x_1 = x_10;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_12);
x_20 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_push(x_13, x_21);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_25);
x_1 = x_10;
x_7 = x_22;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_29 = l_Lean_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_9, x_3, x_4, x_5, x_6, x_7);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Level_hasMVar(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_array_push(x_28, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
x_1 = x_10;
x_2 = x_34;
x_7 = x_31;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_30);
lean_dec(x_27);
x_36 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_array_push(x_28, x_37);
x_40 = 1;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
x_1 = x_10;
x_2 = x_42;
x_7 = x_38;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___closed__1;
x_8 = l_List_forIn_loop___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___spec__1(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_to_list(lean_box(0), x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_array_to_list(lean_box(0), x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_loop___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_4);
x_10 = lean_array_fset(x_1, x_2, x_4);
x_11 = lean_expr_instantiate1(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_14 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs(x_11, x_13, x_10, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type class resolution failed, insufficient number of arguments", 62);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_whnf(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 7)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_array_fget(x_3, x_2);
lean_inc(x_15);
x_18 = lean_is_out_param(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
x_19 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___lambda__1(x_3, x_2, x_16, x_17, x_4, x_5, x_6, x_7, x_14);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_21 = 0;
x_22 = lean_box(0);
lean_inc(x_4);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_20, x_21, x_22, x_4, x_5, x_6, x_7, x_14);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___lambda__1(x_3, x_2, x_16, x_24, x_4, x_5, x_6, x_7, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_dec(x_12);
x_28 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__2;
x_29 = l_Lean_throwError___at_Lean_Meta_collectForwardDeps___spec__1(x_28, x_4, x_5, x_6, x_7, x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_has_out_params(x_15, x_10);
if (x_16 == 0)
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_11);
lean_dec(x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_17);
x_19 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lambda__1___closed__1;
lean_inc(x_18);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_18, x_21);
lean_dec(x_18);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_20, x_22);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_24 = lean_infer_type(x_9, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs(x_25, x_17, x_23, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_mkAppN(x_9, x_28);
x_31 = 0;
x_32 = 1;
x_33 = 1;
x_34 = l_Lean_Meta_mkForallFVars(x_2, x_30, x_31, x_32, x_33, x_4, x_5, x_6, x_7, x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_11, 0);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_11);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_has_out_params(x_45, x_10);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_48);
x_50 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lambda__1___closed__1;
lean_inc(x_49);
x_51 = lean_mk_array(x_49, x_50);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_49, x_52);
lean_dec(x_49);
x_54 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_51, x_53);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_55 = lean_infer_type(x_9, x_4, x_5, x_6, x_7, x_44);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_58 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs(x_56, x_48, x_54, x_4, x_5, x_6, x_7, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_mkAppN(x_9, x_59);
x_62 = 0;
x_63 = 1;
x_64 = 1;
x_65 = l_Lean_Meta_mkForallFVars(x_2, x_61, x_62, x_63, x_64, x_4, x_5, x_6, x_7, x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_68 = x_58;
} else {
 lean_dec_ref(x_58);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_70 = lean_ctor_get(x_55, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_55, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_72 = x_55;
} else {
 lean_dec_ref(x_55);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_8);
return x_74;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lambda__1), 8, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_synthInstance_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_expr_eqv(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_expr_eqv(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_synthInstance_x3f___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Expr_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_synthInstance_x3f___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_expr_eqv(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_expr_eqv(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
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
x_28 = lean_expr_eqv(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_expr_eqv(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_synthInstance_x3f___spec__7(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_synthInstance_x3f___spec__7(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Expr_hash(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_synthInstance_x3f___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_synthInstance_x3f___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_apply_5(x_3, x_5, x_6, x_7, x_8, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_7, 5);
lean_inc(x_16);
x_17 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_processPostponed___spec__2___rarg(x_8, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = lean_apply_5(x_3, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_24 = lean_apply_6(x_2, x_23, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_7);
x_27 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_processPostponed___spec__3(x_18, x_1, x_16, x_25, x_4, x_5, x_6, x_7, x_8, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_MonadExcept_ofExcept___at_Lean_Meta_synthInstance_x3f___spec__9(x_23, x_5, x_6, x_7, x_8, x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_23);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_34);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_37 = lean_apply_6(x_2, x_36, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_7);
x_40 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_processPostponed___spec__3(x_18, x_1, x_16, x_38, x_4, x_5, x_6, x_7, x_8, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_MonadExcept_ofExcept___at_Lean_Meta_synthInstance_x3f___spec__9(x_36, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_36);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
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
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_4(x_3, x_4, x_5, x_6, x_7);
x_10 = l_Lean_profileitIOUnsafe___rarg(x_1, x_2, x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__10___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_exceptOptionEmoji___rarg(x_2);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_10);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
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
x_22 = l_Lean_exceptOptionEmoji___rarg(x_2);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__2;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_20);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_SynthInstance_main(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_hasMVar(x_1);
if (x_9 == 0)
{
if (x_2 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_3);
x_20 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__4(x_19, x_1, x_3);
lean_ctor_set(x_14, 2, x_20);
x_21 = lean_st_ref_set(x_5, x_13, x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_3);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
x_28 = lean_ctor_get(x_14, 3);
x_29 = lean_ctor_get(x_14, 4);
x_30 = lean_ctor_get(x_14, 5);
x_31 = lean_ctor_get(x_14, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_31);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
lean_inc(x_3);
x_32 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__4(x_31, x_1, x_3);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 4, x_29);
lean_ctor_set(x_33, 5, x_30);
lean_ctor_set(x_13, 1, x_33);
x_34 = lean_st_ref_set(x_5, x_13, x_15);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get(x_13, 2);
x_40 = lean_ctor_get(x_13, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_13);
x_41 = lean_ctor_get(x_14, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_14, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_14, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_14, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_14, 2);
lean_inc(x_46);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 x_47 = x_14;
} else {
 lean_dec_ref(x_14);
 x_47 = lean_box(0);
}
lean_inc(x_3);
x_48 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__4(x_46, x_1, x_3);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 6, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_43);
lean_ctor_set(x_49, 4, x_44);
lean_ctor_set(x_49, 5, x_45);
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_39);
lean_ctor_set(x_50, 3, x_40);
x_51 = lean_st_ref_set(x_5, x_50, x_15);
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
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_3);
lean_ctor_set(x_55, 1, x_8);
return x_55;
}
}
else
{
lean_object* x_56; 
lean_dec(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_3);
lean_ctor_set(x_56, 1, x_8);
return x_56;
}
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" result type", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__4;
x_2 = l_Lean_Meta_synthInstance_x3f___lambda__4___closed__2;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nis not definitionally equal to", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___lambda__4___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = lean_infer_type(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 5);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = 1;
x_22 = 1;
lean_ctor_set_uint8(x_12, 5, x_21);
lean_ctor_set_uint8(x_12, 10, x_22);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_13);
lean_inc(x_2);
x_24 = l_Lean_Meta_isExprDefEq(x_2, x_13, x_23, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_3);
x_28 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_6, x_7, x_8, x_9, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = lean_apply_6(x_4, x_32, x_6, x_7, x_8, x_9, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = l_Lean_indentExpr(x_13);
x_36 = l_Lean_Meta_synthInstance_x3f___lambda__4___closed__3;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Meta_synthInstance_x3f___lambda__4___closed__5;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_indentExpr(x_2);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_43, x_6, x_7, x_8, x_9, x_34);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_apply_6(x_4, x_46, x_6, x_7, x_8, x_9, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_ctor_get(x_24, 1);
lean_inc(x_48);
lean_dec(x_24);
x_49 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_1, x_6, x_7, x_8, x_9, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_50);
x_52 = l_Lean_Meta_check(x_50, x_6, x_7, x_8, x_9, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_50);
x_55 = lean_apply_6(x_4, x_54, x_6, x_7, x_8, x_9, x_53);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_50);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_64 = lean_ctor_get_uint8(x_12, 0);
x_65 = lean_ctor_get_uint8(x_12, 1);
x_66 = lean_ctor_get_uint8(x_12, 2);
x_67 = lean_ctor_get_uint8(x_12, 3);
x_68 = lean_ctor_get_uint8(x_12, 4);
x_69 = lean_ctor_get_uint8(x_12, 6);
x_70 = lean_ctor_get_uint8(x_12, 7);
x_71 = lean_ctor_get_uint8(x_12, 8);
x_72 = lean_ctor_get_uint8(x_12, 9);
x_73 = lean_ctor_get_uint8(x_12, 11);
x_74 = lean_ctor_get_uint8(x_12, 12);
x_75 = lean_ctor_get_uint8(x_12, 13);
lean_dec(x_12);
x_76 = 1;
x_77 = 1;
x_78 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_78, 0, x_64);
lean_ctor_set_uint8(x_78, 1, x_65);
lean_ctor_set_uint8(x_78, 2, x_66);
lean_ctor_set_uint8(x_78, 3, x_67);
lean_ctor_set_uint8(x_78, 4, x_68);
lean_ctor_set_uint8(x_78, 5, x_76);
lean_ctor_set_uint8(x_78, 6, x_69);
lean_ctor_set_uint8(x_78, 7, x_70);
lean_ctor_set_uint8(x_78, 8, x_71);
lean_ctor_set_uint8(x_78, 9, x_72);
lean_ctor_set_uint8(x_78, 10, x_77);
lean_ctor_set_uint8(x_78, 11, x_73);
lean_ctor_set_uint8(x_78, 12, x_74);
lean_ctor_set_uint8(x_78, 13, x_75);
x_79 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_15);
lean_ctor_set(x_79, 2, x_16);
lean_ctor_set(x_79, 3, x_17);
lean_ctor_set(x_79, 4, x_18);
lean_ctor_set(x_79, 5, x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_13);
lean_inc(x_2);
x_80 = l_Lean_Meta_isExprDefEq(x_2, x_13, x_79, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_1);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
lean_inc(x_3);
x_84 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_6, x_7, x_8, x_9, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_box(0);
x_89 = lean_apply_6(x_4, x_88, x_6, x_7, x_8, x_9, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_dec(x_84);
x_91 = l_Lean_indentExpr(x_13);
x_92 = l_Lean_Meta_synthInstance_x3f___lambda__4___closed__3;
x_93 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Lean_Meta_synthInstance_x3f___lambda__4___closed__5;
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_indentExpr(x_2);
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_99, x_6, x_7, x_8, x_9, x_90);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_box(0);
x_103 = lean_apply_6(x_4, x_102, x_6, x_7, x_8, x_9, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_ctor_get(x_80, 1);
lean_inc(x_104);
lean_dec(x_80);
x_105 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_1, x_6, x_7, x_8, x_9, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_106);
x_108 = l_Lean_Meta_check(x_106, x_6, x_7, x_8, x_9, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_106);
x_111 = lean_apply_6(x_4, x_110, x_6, x_7, x_8, x_9, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_106);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_114 = x_108;
} else {
 lean_dec_ref(x_108);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = lean_ctor_get(x_80, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_80, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_118 = x_80;
} else {
 lean_dec_ref(x_80);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_11);
if (x_120 == 0)
{
return x_11;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_11, 0);
x_122 = lean_ctor_get(x_11, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_11);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("result ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_40; 
x_40 = 0;
x_12 = x_40;
goto block_39;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_10, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Array_isEmpty___rarg(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = 1;
x_12 = x_44;
goto block_39;
}
else
{
uint8_t x_45; 
x_45 = 0;
x_12 = x_45;
goto block_39;
}
}
block_39:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_synthInstance_x3f___lambda__3(x_2, x_12, x_13, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(x_12);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__3___boxed), 8, 2);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_16);
lean_inc(x_4);
x_18 = l_Lean_Meta_openAbstractMVarsResult(x_15, x_4, x_5, x_6, x_7, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_3);
x_23 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_4, x_5, x_6, x_7, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = l_Lean_Meta_synthInstance_x3f___lambda__4(x_22, x_2, x_3, x_17, x_27, x_4, x_5, x_6, x_7, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
lean_inc(x_22);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_22);
x_31 = l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_3);
x_35 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_34, x_4, x_5, x_6, x_7, x_29);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_synthInstance_x3f___lambda__4(x_22, x_2, x_3, x_17, x_36, x_4, x_5, x_6, x_7, x_37);
lean_dec(x_36);
return x_38;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_9);
if (x_46 == 0)
{
return x_9;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_9, 0);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_9);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_synthInstance_maxSize;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = l_Lean_Meta_synthInstance_x3f___lambda__6___closed__1;
x_10 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_8, x_9);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = 1;
x_15 = 0;
x_16 = 3;
x_17 = 1;
lean_ctor_set_uint8(x_12, 0, x_14);
lean_ctor_set_uint8(x_12, 1, x_14);
lean_ctor_set_uint8(x_12, 3, x_15);
lean_ctor_set_uint8(x_12, 4, x_14);
lean_ctor_set_uint8(x_12, 5, x_16);
lean_ctor_set_uint8(x_12, 13, x_17);
x_18 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_18, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_18, 1);
lean_inc(x_75);
lean_dec(x_18);
x_19 = x_10;
x_20 = x_74;
x_21 = x_75;
goto block_73;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_10);
x_76 = lean_ctor_get(x_2, 0);
lean_inc(x_76);
lean_dec(x_2);
x_77 = lean_ctor_get(x_18, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_18, 1);
lean_inc(x_78);
lean_dec(x_18);
x_19 = x_76;
x_20 = x_77;
x_21 = x_78;
goto block_73;
}
block_73:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_20, x_22, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_6, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_4, x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_24);
x_34 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__1(x_33, x_24);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_28);
lean_inc(x_24);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__1___boxed), 7, 1);
lean_closure_set(x_35, 0, x_24);
lean_inc(x_24);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__2), 7, 2);
lean_closure_set(x_36, 0, x_24);
lean_closure_set(x_36, 1, x_19);
x_37 = l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__5), 8, 3);
lean_closure_set(x_38, 0, x_36);
lean_closure_set(x_38, 1, x_24);
lean_closure_set(x_38, 2, x_37);
x_39 = l_Lean_withTraceNode___at_Lean_Meta_synthInstance_x3f___spec__8(x_37, x_35, x_38, x_14, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
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
else
{
lean_object* x_48; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = lean_ctor_get(x_34, 0);
lean_inc(x_48);
lean_dec(x_34);
lean_ctor_set(x_28, 0, x_48);
return x_28;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_28, 0);
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_28);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_24);
x_53 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__1(x_52, x_24);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_inc(x_24);
x_54 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__1___boxed), 7, 1);
lean_closure_set(x_54, 0, x_24);
lean_inc(x_24);
x_55 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__2), 7, 2);
lean_closure_set(x_55, 0, x_24);
lean_closure_set(x_55, 1, x_19);
x_56 = l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
x_57 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__5), 8, 3);
lean_closure_set(x_57, 0, x_55);
lean_closure_set(x_57, 1, x_24);
lean_closure_set(x_57, 2, x_56);
x_58 = l_Lean_withTraceNode___at_Lean_Meta_synthInstance_x3f___spec__8(x_56, x_54, x_57, x_14, x_3, x_4, x_5, x_6, x_50);
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
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = lean_ctor_get(x_53, 0);
lean_inc(x_67);
lean_dec(x_53);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_50);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_23);
if (x_69 == 0)
{
return x_23;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_23, 0);
x_71 = lean_ctor_get(x_23, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_23);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_79 = lean_ctor_get_uint8(x_12, 2);
x_80 = lean_ctor_get_uint8(x_12, 6);
x_81 = lean_ctor_get_uint8(x_12, 7);
x_82 = lean_ctor_get_uint8(x_12, 8);
x_83 = lean_ctor_get_uint8(x_12, 9);
x_84 = lean_ctor_get_uint8(x_12, 10);
x_85 = lean_ctor_get_uint8(x_12, 11);
x_86 = lean_ctor_get_uint8(x_12, 12);
lean_dec(x_12);
x_87 = 1;
x_88 = 0;
x_89 = 3;
x_90 = 1;
x_91 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_91, 0, x_87);
lean_ctor_set_uint8(x_91, 1, x_87);
lean_ctor_set_uint8(x_91, 2, x_79);
lean_ctor_set_uint8(x_91, 3, x_88);
lean_ctor_set_uint8(x_91, 4, x_87);
lean_ctor_set_uint8(x_91, 5, x_89);
lean_ctor_set_uint8(x_91, 6, x_80);
lean_ctor_set_uint8(x_91, 7, x_81);
lean_ctor_set_uint8(x_91, 8, x_82);
lean_ctor_set_uint8(x_91, 9, x_83);
lean_ctor_set_uint8(x_91, 10, x_84);
lean_ctor_set_uint8(x_91, 11, x_85);
lean_ctor_set_uint8(x_91, 12, x_86);
lean_ctor_set_uint8(x_91, 13, x_90);
lean_ctor_set(x_3, 0, x_91);
x_92 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_92, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_92, 1);
lean_inc(x_130);
lean_dec(x_92);
x_93 = x_10;
x_94 = x_129;
x_95 = x_130;
goto block_128;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_10);
x_131 = lean_ctor_get(x_2, 0);
lean_inc(x_131);
lean_dec(x_2);
x_132 = lean_ctor_get(x_92, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_92, 1);
lean_inc(x_133);
lean_dec(x_92);
x_93 = x_131;
x_94 = x_132;
x_95 = x_133;
goto block_128;
}
block_128:
{
lean_object* x_96; lean_object* x_97; 
x_96 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_97 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_94, x_96, x_3, x_4, x_5, x_6, x_95);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_st_ref_get(x_6, x_99);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_st_ref_get(x_4, x_101);
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
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_ctor_get(x_106, 2);
lean_inc(x_107);
lean_dec(x_106);
lean_inc(x_98);
x_108 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__1(x_107, x_98);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_105);
lean_inc(x_98);
x_109 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__1___boxed), 7, 1);
lean_closure_set(x_109, 0, x_98);
lean_inc(x_98);
x_110 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__2), 7, 2);
lean_closure_set(x_110, 0, x_98);
lean_closure_set(x_110, 1, x_93);
x_111 = l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
x_112 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__5), 8, 3);
lean_closure_set(x_112, 0, x_110);
lean_closure_set(x_112, 1, x_98);
lean_closure_set(x_112, 2, x_111);
x_113 = l_Lean_withTraceNode___at_Lean_Meta_synthInstance_x3f___spec__8(x_111, x_109, x_112, x_87, x_3, x_4, x_5, x_6, x_104);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_113, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_120 = x_113;
} else {
 lean_dec_ref(x_113);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_98);
lean_dec(x_93);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_122 = lean_ctor_get(x_108, 0);
lean_inc(x_122);
lean_dec(x_108);
if (lean_is_scalar(x_105)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_105;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_104);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_93);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_124 = lean_ctor_get(x_97, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_97, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_126 = x_97;
} else {
 lean_dec_ref(x_97);
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
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; lean_object* x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_134 = lean_ctor_get(x_3, 0);
x_135 = lean_ctor_get(x_3, 1);
x_136 = lean_ctor_get(x_3, 2);
x_137 = lean_ctor_get(x_3, 3);
x_138 = lean_ctor_get(x_3, 4);
x_139 = lean_ctor_get(x_3, 5);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_3);
x_140 = lean_ctor_get_uint8(x_134, 2);
x_141 = lean_ctor_get_uint8(x_134, 6);
x_142 = lean_ctor_get_uint8(x_134, 7);
x_143 = lean_ctor_get_uint8(x_134, 8);
x_144 = lean_ctor_get_uint8(x_134, 9);
x_145 = lean_ctor_get_uint8(x_134, 10);
x_146 = lean_ctor_get_uint8(x_134, 11);
x_147 = lean_ctor_get_uint8(x_134, 12);
if (lean_is_exclusive(x_134)) {
 x_148 = x_134;
} else {
 lean_dec_ref(x_134);
 x_148 = lean_box(0);
}
x_149 = 1;
x_150 = 0;
x_151 = 3;
x_152 = 1;
if (lean_is_scalar(x_148)) {
 x_153 = lean_alloc_ctor(0, 0, 14);
} else {
 x_153 = x_148;
}
lean_ctor_set_uint8(x_153, 0, x_149);
lean_ctor_set_uint8(x_153, 1, x_149);
lean_ctor_set_uint8(x_153, 2, x_140);
lean_ctor_set_uint8(x_153, 3, x_150);
lean_ctor_set_uint8(x_153, 4, x_149);
lean_ctor_set_uint8(x_153, 5, x_151);
lean_ctor_set_uint8(x_153, 6, x_141);
lean_ctor_set_uint8(x_153, 7, x_142);
lean_ctor_set_uint8(x_153, 8, x_143);
lean_ctor_set_uint8(x_153, 9, x_144);
lean_ctor_set_uint8(x_153, 10, x_145);
lean_ctor_set_uint8(x_153, 11, x_146);
lean_ctor_set_uint8(x_153, 12, x_147);
lean_ctor_set_uint8(x_153, 13, x_152);
x_154 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_135);
lean_ctor_set(x_154, 2, x_136);
lean_ctor_set(x_154, 3, x_137);
lean_ctor_set(x_154, 4, x_138);
lean_ctor_set(x_154, 5, x_139);
x_155 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_1, x_154, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_155, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_155, 1);
lean_inc(x_193);
lean_dec(x_155);
x_156 = x_10;
x_157 = x_192;
x_158 = x_193;
goto block_191;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_10);
x_194 = lean_ctor_get(x_2, 0);
lean_inc(x_194);
lean_dec(x_2);
x_195 = lean_ctor_get(x_155, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_155, 1);
lean_inc(x_196);
lean_dec(x_155);
x_156 = x_194;
x_157 = x_195;
x_158 = x_196;
goto block_191;
}
block_191:
{
lean_object* x_159; lean_object* x_160; 
x_159 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_154);
x_160 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_157, x_159, x_154, x_4, x_5, x_6, x_158);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_st_ref_get(x_6, x_162);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_st_ref_get(x_4, x_164);
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
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_ctor_get(x_169, 2);
lean_inc(x_170);
lean_dec(x_169);
lean_inc(x_161);
x_171 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__1(x_170, x_161);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_168);
lean_inc(x_161);
x_172 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__1___boxed), 7, 1);
lean_closure_set(x_172, 0, x_161);
lean_inc(x_161);
x_173 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__2), 7, 2);
lean_closure_set(x_173, 0, x_161);
lean_closure_set(x_173, 1, x_156);
x_174 = l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
x_175 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__5), 8, 3);
lean_closure_set(x_175, 0, x_173);
lean_closure_set(x_175, 1, x_161);
lean_closure_set(x_175, 2, x_174);
x_176 = l_Lean_withTraceNode___at_Lean_Meta_synthInstance_x3f___spec__8(x_174, x_172, x_175, x_149, x_154, x_4, x_5, x_6, x_167);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_176, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_176, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_161);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_185 = lean_ctor_get(x_171, 0);
lean_inc(x_185);
lean_dec(x_171);
if (lean_is_scalar(x_168)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_168;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_167);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_187 = lean_ctor_get(x_160, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_160, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_189 = x_160;
} else {
 lean_dec_ref(x_160);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeclass inference", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__6), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_Meta_synthInstance_x3f___closed__1;
x_11 = l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__10___rarg(x_10, x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_synthInstance_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_synthInstance_x3f___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_synthInstance_x3f___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_MonadExcept_ofExcept___at_Lean_Meta_synthInstance_x3f___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_synthInstance_x3f___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_withTraceNode___at_Lean_Meta_synthInstance_x3f___spec__8(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__10___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_synthInstance_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_synthInstance_x3f___lambda__3(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_synthInstance_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_trySynthInstance___closed__1() {
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
x_11 = l_Option_toLOption___rarg(x_10);
lean_dec(x_10);
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
x_14 = l_Option_toLOption___rarg(x_12);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_8, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
x_24 = l_Lean_Meta_trySynthInstance___closed__1;
x_25 = lean_nat_dec_eq(x_24, x_23);
lean_dec(x_23);
if (x_25 == 0)
{
return x_8;
}
else
{
lean_object* x_26; 
lean_dec(x_16);
x_26 = lean_box(2);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_26);
return x_8;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
x_29 = l_Lean_Meta_trySynthInstance___closed__1;
x_30 = lean_nat_dec_eq(x_29, x_28);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
x_32 = lean_box(2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_22; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_22 = l_Lean_Meta_synthInstance_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_1);
x_25 = l_Lean_indentExpr(x_1);
x_26 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__2;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_29, x_3, x_4, x_5, x_6, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_8 = x_31;
x_9 = x_32;
goto block_21;
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_22, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
lean_ctor_set(x_22, 0, x_35);
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_dec(x_22);
x_37 = lean_ctor_get(x_23, 0);
lean_inc(x_37);
lean_dec(x_23);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_dec(x_22);
x_8 = x_39;
x_9 = x_40;
goto block_21;
}
block_21:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = l_Lean_Meta_trySynthInstance___closed__1;
x_13 = lean_nat_dec_eq(x_12, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
x_15 = l_Lean_indentExpr(x_1);
x_16 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_19, x_3, x_4, x_5, x_6, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 6);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isAssigned___spec__1(x_13, x_1);
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 6);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isAssigned___spec__1(x_19, x_1);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_38; 
x_9 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Meta_synthInstance_x3f(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_10 = x_39;
x_11 = x_40;
goto block_37;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_38, 0);
lean_dec(x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_38, 1);
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
x_50 = l_Lean_Meta_trySynthInstance___closed__1;
x_51 = lean_nat_dec_eq(x_50, x_49);
lean_dec(x_49);
if (x_51 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_38;
}
else
{
lean_free_object(x_38);
lean_dec(x_41);
x_10 = x_9;
x_11 = x_47;
goto block_37;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
lean_dec(x_38);
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_53);
x_54 = l_Lean_Meta_trySynthInstance___closed__1;
x_55 = lean_nat_dec_eq(x_54, x_53);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
else
{
lean_dec(x_41);
x_10 = x_9;
x_11 = x_52;
goto block_37;
}
}
}
}
block_37:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
lean_inc(x_1);
x_16 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_1, x_4, x_5, x_6, x_7, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_15, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
lean_dec(x_30);
x_31 = 0;
x_32 = lean_box(x_31);
lean_ctor_set(x_16, 0, x_32);
return x_16;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("synthPending", 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_2 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("synthPending ", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("too many nested synthPending invocations", 40);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getDecl(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*7);
x_10 = lean_box(x_9);
if (lean_obj_tag(x_10) == 2)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_8, 2);
lean_inc(x_20);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_20);
x_21 = l_Lean_Meta_isClass_x3f(x_20, x_2, x_3, x_4, x_5, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_22);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 4);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 5);
lean_inc(x_37);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_dec_lt(x_38, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_2);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_41 = lean_ctor_get(x_2, 5);
lean_dec(x_41);
x_42 = lean_ctor_get(x_2, 4);
lean_dec(x_42);
x_43 = lean_ctor_get(x_2, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_2, 2);
lean_dec(x_44);
x_45 = lean_ctor_get(x_2, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_2, 0);
lean_dec(x_46);
x_47 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
x_48 = lean_nat_add(x_36, x_38);
lean_dec(x_36);
lean_ctor_set(x_2, 4, x_48);
x_49 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_47, x_2, x_3, x_4, x_5, x_31);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_box(0);
x_54 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_20, x_53, x_2, x_3, x_4, x_5, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
lean_inc(x_1);
x_56 = l_Lean_Expr_mvar___override(x_1);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__4;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_47, x_61, x_2, x_3, x_4, x_5, x_55);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_20, x_63, x_2, x_3, x_4, x_5, x_64);
lean_dec(x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_2);
x_66 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
x_67 = lean_nat_add(x_36, x_38);
lean_dec(x_36);
x_68 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_68, 0, x_32);
lean_ctor_set(x_68, 1, x_33);
lean_ctor_set(x_68, 2, x_34);
lean_ctor_set(x_68, 3, x_35);
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 5, x_37);
x_69 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_66, x_68, x_3, x_4, x_5, x_31);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_box(0);
x_74 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_20, x_73, x_68, x_3, x_4, x_5, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_dec(x_69);
lean_inc(x_1);
x_76 = l_Lean_Expr_mvar___override(x_1);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__4;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_66, x_81, x_68, x_3, x_4, x_5, x_75);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_20, x_83, x_68, x_3, x_4, x_5, x_84);
lean_dec(x_83);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_1);
x_86 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
x_87 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_86, x_2, x_3, x_4, x_5, x_31);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
uint8_t x_90; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 0);
lean_dec(x_91);
x_92 = 0;
x_93 = lean_box(x_92);
lean_ctor_set(x_87, 0, x_93);
return x_87;
}
else
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = 0;
x_96 = lean_box(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_87, 1);
lean_inc(x_98);
lean_dec(x_87);
x_99 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__6;
x_100 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_86, x_99, x_2, x_3, x_4, x_5, x_98);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_100, 0);
lean_dec(x_102);
x_103 = 0;
x_104 = lean_box(x_103);
lean_ctor_set(x_100, 0, x_104);
return x_100;
}
else
{
lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_dec(x_100);
x_106 = 0;
x_107 = lean_box(x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
}
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_7);
if (x_109 == 0)
{
return x_7;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_7, 0);
x_111 = lean_ctor_get(x_7, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_7);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* lean_synth_pending(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 7);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 8);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 9);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 10);
lean_inc(x_18);
x_19 = lean_nat_dec_eq(x_11, x_12);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_4, 10);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 9);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 8);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 7);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 6);
lean_dec(x_25);
x_26 = lean_ctor_get(x_4, 5);
lean_dec(x_26);
x_27 = lean_ctor_get(x_4, 4);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 3);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_4, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_4, 0);
lean_dec(x_31);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_11, x_32);
lean_dec(x_11);
lean_ctor_set(x_4, 3, x_33);
x_34 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_4);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_11, x_35);
lean_dec(x_11);
x_37 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_9);
lean_ctor_set(x_37, 2, x_10);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_12);
lean_ctor_set(x_37, 5, x_13);
lean_ctor_set(x_37, 6, x_14);
lean_ctor_set(x_37, 7, x_15);
lean_ctor_set(x_37, 8, x_16);
lean_ctor_set(x_37, 9, x_17);
lean_ctor_set(x_37, 10, x_18);
x_38 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_7, x_2, x_3, x_37, x_5, x_6);
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_39 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3(x_13, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__4;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__6;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__8;
x_2 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__9;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__11;
x_2 = lean_unsigned_to_nat(10221u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
x_3 = 0;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__12;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_11 = 1;
x_12 = l_Lean_registerTraceClass(x_10, x_11, x_4, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__2;
x_15 = l_Lean_registerTraceClass(x_14, x_11, x_4, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Meta_SynthInstance_resume___lambda__5___closed__2;
x_18 = l_Lean_registerTraceClass(x_17, x_11, x_4, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__2;
x_21 = l_Lean_registerTraceClass(x_20, x_3, x_4, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__2;
x_24 = l_Lean_registerTraceClass(x_23, x_3, x_4, x_22);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
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
x_37 = !lean_is_exclusive(x_12);
if (x_37 == 0)
{
return x_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_5);
if (x_45 == 0)
{
return x_5;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Instances(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AbstractMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Profile(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
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
res = initialize_Lean_Meta_WHNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Profile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__9);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_synthInstance_maxHeartbeats = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_synthInstance_maxHeartbeats);
lean_dec_ref(res);
}l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49____closed__5);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_49_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_synthInstance_maxSize = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_synthInstance_maxSize);
lean_dec_ref(res);
}l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__1 = _init_l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__1);
l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__1 = _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__1);
l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__2 = _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__2);
l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__3 = _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__3);
l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__4 = _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__4);
l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__5 = _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__5);
l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__6 = _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__6);
l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__7 = _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97____closed__7);
if (builtin) {res = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_97_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_SynthInstance_inferTCGoalsRLAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_SynthInstance_inferTCGoalsRLAttr);
lean_dec_ref(res);
}l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1 = _init_l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1);
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
l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__1 = _init_l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__1);
l_Lean_Meta_SynthInstance_instInhabitedConsumerNode = _init_l_Lean_Meta_SynthInstance_instInhabitedConsumerNode();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedConsumerNode);
l_Lean_Meta_SynthInstance_MkTableKey_State_nextIdx___default = _init_l_Lean_Meta_SynthInstance_MkTableKey_State_nextIdx___default();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_State_nextIdx___default);
l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1 = _init_l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1);
l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default = _init_l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default);
l_Lean_Meta_SynthInstance_MkTableKey_State_emap___default = _init_l_Lean_Meta_SynthInstance_MkTableKey_State_emap___default();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_State_emap___default);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__1 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__1);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__2 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__2);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__3 = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM___closed__3);
l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM = _init_l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_instMonadMCtxM);
l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2___closed__1 = _init_l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2___closed__1);
l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2___closed__2 = _init_l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__2___closed__2);
l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__1 = _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__1();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__1);
l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__2 = _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__2();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__2);
l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__3 = _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__3();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__3);
l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__4 = _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__4();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___spec__1___closed__4);
l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1 = _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1);
l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2 = _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2);
l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1 = _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1);
l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__2 = _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__2);
l_Lean_Meta_SynthInstance_instInhabitedAnswer = _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedAnswer);
l_Lean_Meta_SynthInstance_TableEntry_answers___default = _init_l_Lean_Meta_SynthInstance_TableEntry_answers___default();
lean_mark_persistent(l_Lean_Meta_SynthInstance_TableEntry_answers___default);
l_Lean_Meta_SynthInstance_State_result_x3f___default = _init_l_Lean_Meta_SynthInstance_State_result_x3f___default();
lean_mark_persistent(l_Lean_Meta_SynthInstance_State_result_x3f___default);
l_Lean_Meta_SynthInstance_State_generatorStack___default = _init_l_Lean_Meta_SynthInstance_State_generatorStack___default();
lean_mark_persistent(l_Lean_Meta_SynthInstance_State_generatorStack___default);
l_Lean_Meta_SynthInstance_State_resumeStack___default = _init_l_Lean_Meta_SynthInstance_State_resumeStack___default();
lean_mark_persistent(l_Lean_Meta_SynthInstance_State_resumeStack___default);
l_Lean_Meta_SynthInstance_State_tableEntries___default = _init_l_Lean_Meta_SynthInstance_State_tableEntries___default();
lean_mark_persistent(l_Lean_Meta_SynthInstance_State_tableEntries___default);
l_Lean_Meta_SynthInstance_checkMaxHeartbeats___closed__1 = _init_l_Lean_Meta_SynthInstance_checkMaxHeartbeats___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_checkMaxHeartbeats___closed__1);
l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__1 = _init_l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__1);
l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__2 = _init_l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__3);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__4 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__5___closed__4);
l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__1 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__1);
l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__2 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__2);
l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3);
l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4);
l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5);
l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6);
l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7);
l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__8 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__8);
l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__2);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__3 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg___closed__3);
l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___closed__1 = _init_l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___closed__1();
lean_mark_persistent(l_Lean_withTraceNode_x27___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___closed__1);
l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__1 = _init_l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__1);
l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__2 = _init_l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__2);
l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__3 = _init_l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__3);
l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__4 = _init_l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__4);
l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__5 = _init_l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___lambda__2___closed__5);
l_Lean_Meta_SynthInstance_newSubgoal___closed__1 = _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___closed__1);
l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1___closed__1 = _init_l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1___closed__1);
l_Lean_Meta_SynthInstance_getEntry___closed__1 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__1);
l_Lean_Meta_SynthInstance_getEntry___closed__2 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__2);
l_Lean_Meta_SynthInstance_getEntry___closed__3 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__3);
l_Lean_Meta_SynthInstance_mkTableKeyFor___closed__1 = _init_l_Lean_Meta_SynthInstance_mkTableKeyFor___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKeyFor___closed__1);
l_panic___at_Lean_Meta_SynthInstance_tryResolve___spec__5___closed__1 = _init_l_panic___at_Lean_Meta_SynthInstance_tryResolve___spec__5___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_SynthInstance_tryResolve___spec__5___closed__1);
l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__3);
l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__4 = _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lambda__1___closed__4);
l_Lean_Meta_SynthInstance_tryResolve___lambda__4___closed__1 = _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lambda__4___closed__1);
l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__1 = _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__1);
l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__2 = _init_l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolve___lambda__5___closed__2);
l_Lean_Meta_SynthInstance_wakeUp___closed__1 = _init_l_Lean_Meta_SynthInstance_wakeUp___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___closed__1);
l_Lean_Meta_SynthInstance_wakeUp___closed__2 = _init_l_Lean_Meta_SynthInstance_wakeUp___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___closed__2);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__2 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__2);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__3 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__3);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__4 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__4);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__5 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__5);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__6 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__6);
l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__3);
l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__1 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__1);
l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__2 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__2);
l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__3 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__3);
l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__4 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__4);
l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__5 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__5);
l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__6 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__6);
l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__7 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__7);
l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__8 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__8();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__8);
l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__9 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__9();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__9);
l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__10 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__10();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__10);
l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__11 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__11();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__11);
l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__12 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__12();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__4___closed__12);
l_Lean_Meta_SynthInstance_addAnswer___closed__1 = _init_l_Lean_Meta_SynthInstance_addAnswer___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__2 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__2);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__3 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__3);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__4 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__4);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__5 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__5);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__6 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__6);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__2 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__2);
l_Lean_Meta_SynthInstance_consume___closed__1 = _init_l_Lean_Meta_SynthInstance_consume___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_consume___closed__1);
l_Lean_Meta_SynthInstance_generate___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_generate___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lambda__1___closed__3);
l_Lean_Meta_SynthInstance_generate___lambda__1___closed__4 = _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lambda__1___closed__4);
l_Lean_Meta_SynthInstance_generate___lambda__4___closed__1 = _init_l_Lean_Meta_SynthInstance_generate___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lambda__4___closed__1);
l_Lean_Meta_SynthInstance_generate___lambda__4___closed__2 = _init_l_Lean_Meta_SynthInstance_generate___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lambda__4___closed__2);
l_Lean_Meta_SynthInstance_getNextToResume___rarg___closed__1 = _init_l_Lean_Meta_SynthInstance_getNextToResume___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getNextToResume___rarg___closed__1);
l_Lean_Meta_SynthInstance_resume___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_resume___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_resume___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__1___closed__3);
l_Lean_Meta_SynthInstance_resume___lambda__1___closed__4 = _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__1___closed__4);
l_Lean_Meta_SynthInstance_resume___lambda__1___closed__5 = _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__1___closed__5);
l_Lean_Meta_SynthInstance_resume___lambda__1___closed__6 = _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__1___closed__6);
l_Lean_Meta_SynthInstance_resume___lambda__5___closed__1 = _init_l_Lean_Meta_SynthInstance_resume___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__5___closed__1);
l_Lean_Meta_SynthInstance_resume___lambda__5___closed__2 = _init_l_Lean_Meta_SynthInstance_resume___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__5___closed__2);
l_Lean_Meta_SynthInstance_resume___lambda__5___closed__3 = _init_l_Lean_Meta_SynthInstance_resume___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__5___closed__3);
l_Lean_Meta_SynthInstance_resume___closed__1 = _init_l_Lean_Meta_SynthInstance_resume___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__1);
l_Lean_Meta_SynthInstance_resume___closed__2 = _init_l_Lean_Meta_SynthInstance_resume___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__2);
l_Lean_Meta_SynthInstance_resume___closed__3 = _init_l_Lean_Meta_SynthInstance_resume___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__3);
l_Lean_Meta_SynthInstance_main___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_main___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_main___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lambda__1___closed__3);
l_Lean_Meta_SynthInstance_main___lambda__1___closed__4 = _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lambda__1___closed__4);
l_Lean_Meta_SynthInstance_main___lambda__1___closed__5 = _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lambda__1___closed__5);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__2 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__2);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lambda__1___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lambda__1___closed__1);
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__1();
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1);
l_Lean_Meta_synthInstance_x3f___lambda__4___closed__1 = _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__4___closed__1);
l_Lean_Meta_synthInstance_x3f___lambda__4___closed__2 = _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__4___closed__2);
l_Lean_Meta_synthInstance_x3f___lambda__4___closed__3 = _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__4___closed__3);
l_Lean_Meta_synthInstance_x3f___lambda__4___closed__4 = _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__4___closed__4);
l_Lean_Meta_synthInstance_x3f___lambda__4___closed__5 = _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__4___closed__5);
l_Lean_Meta_synthInstance_x3f___lambda__5___closed__1 = _init_l_Lean_Meta_synthInstance_x3f___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__5___closed__1);
l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2 = _init_l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2);
l_Lean_Meta_synthInstance_x3f___lambda__6___closed__1 = _init_l_Lean_Meta_synthInstance_x3f___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__6___closed__1);
l_Lean_Meta_synthInstance_x3f___closed__1 = _init_l_Lean_Meta_synthInstance_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__1);
l_Lean_Meta_trySynthInstance___closed__1 = _init_l_Lean_Meta_trySynthInstance___closed__1();
lean_mark_persistent(l_Lean_Meta_trySynthInstance___closed__1);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___closed__1);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__3___closed__2);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__3 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__3);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__4 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__4);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__5 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__5);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__6 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221____closed__12);
res = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_10221_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

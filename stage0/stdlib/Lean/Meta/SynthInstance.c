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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getMaxHeartbeats___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__2;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkGeneratorNode_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_State_resumeStack___default;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_toLOption___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_SynthInstance_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__1;
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__2;
static lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_State_emap___default;
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__3;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___closed__1;
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_SynthInstance_getInstances___spec__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_getGlobalInstancesIndex___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___closed__2;
static lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__3;
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(lean_object*, lean_object*, size_t, size_t);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static uint64_t l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__2;
static lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__1;
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkMaxHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__3;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__3___closed__1;
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(lean_object*, lean_object*);
lean_object* l_Std_HashMap_insert___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__9;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_getSubgoalsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__1;
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_SynthInstance_resume___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_SynthInstance_getInstances___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__5;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_maxSize;
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_hasUnusedArguments(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_hasUnusedArguments___boxed(lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__2;
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__4;
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_wakeUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69_(lean_object*);
lean_object* l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__2;
LEAN_EXPORT uint8_t l_Lean_Meta_SynthInstance_Waiter_isRoot(lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__1;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___boxed(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_consume___closed__1;
lean_object* l_Lean_Meta_abstractMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__6;
static lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_synth___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_State_tableEntries___default___spec__1___boxed(lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__5;
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__1;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__4;
static lean_object* l_Lean_Meta_SynthInstance_generate___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mapMetaM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isDefEqStuckExceptionId;
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_SynthInstance_getInstances___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_out_param(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___closed__2;
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__4;
static lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_TableEntry_answers___default;
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_SynthInstance_getInstances___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs___closed__1;
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Meta_SynthInstance_getInstances___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_panic___at___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2;
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__5;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedConsumerNode;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__2;
static lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__6;
static lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_trySynthInstance___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__4;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_State_tableEntries___default___spec__1(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedConsumerNode___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_Lean_Meta_SynthInstance_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__3;
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__2___closed__2;
size_t lean_usize_modn(size_t, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__5;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
uint8_t l_Std_PersistentArray_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_getErasedInstances___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__2;
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__5___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_SynthInstance_getInstances___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__6;
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__3;
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedSynthM___rarg___closed__1;
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_6____spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_7767_(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessLevels___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_State_generatorStack___default;
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__2___closed__4;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_synth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__2;
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Meta_SynthInstance_addAnswer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__1;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__4;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_State_result_x3f___default;
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__2;
lean_object* l_Lean_Core_checkMaxHeartbeatsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__6;
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___closed__3;
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_State_tableEntries___default;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_wakeUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SynthInstance_isNewAnswer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__6;
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_synth___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__1;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getTop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_synthInstance_x3f___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__3;
lean_object* l_Std_PersistentArray_toArray___rarg(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__2;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___closed__1;
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_Waiter_isRoot___boxed(lean_object*);
static lean_object* l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_main___lambda__2___closed__1;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_synth___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getResult___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__3;
static lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_main___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__3;
lean_object* l_Lean_Meta_isExprMVarAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_SynthInstance_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__2;
static lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getNextToResume(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_isNewAnswer___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_isLevelAssignable(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__5;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getMaxHeartbeats(lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_synth_pending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__1;
lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_modifyTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_generate___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__2;
lean_object* l_Lean_profileitIOUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_generate___closed__1;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_SynthInstance_getInstances___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthInstance_x3f___closed__1;
static size_t l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_State_nextIdx___default;
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isExprAssignable(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2;
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__5;
static lean_object* l_Lean_Meta_SynthInstance_synth___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_consume(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_synthInstance_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7;
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___closed__2;
static size_t l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_addAnswer___closed__3;
static lean_object* l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Meta_SynthInstance_addAnswer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_instInhabitedAnswer;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4;
uint8_t l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_synthInstance_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__8(lean_object*);
lean_object* l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__1;
uint8_t lean_has_out_params(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__7___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_maxHeartbeats;
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__2;
static lean_object* l_Lean_Meta_SynthInstance_generate___closed__4;
static lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__3;
static lean_object* l_Lean_Meta_SynthInstance_resume___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkMaxHeartbeats___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Meta_SynthInstance_getInstances___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_checkMaxHeartbeats___closed__1;
static lean_object* l_Lean_Meta_SynthInstance_synth___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_inferTCGoalsRLAttr;
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("synthInstance");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maxHeartbeats");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum amount of heartbeats per typeclass resolution problem. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(20000u);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__5;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__7;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maxSize");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum number of instances used to construct a solution in the type class instance synthesis procedure");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(128u);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__5;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inferTCGoalsRL");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instruct type class resolution procedure to solve goals from right to left for this instance");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__2;
x_3 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__3;
x_4 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____lambda__1(x_1, x_2, x_3, x_4);
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
static uint64_t _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4;
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
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__4;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__5;
x_3 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__6;
x_4 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_3);
lean_ctor_set(x_4, 5, x_2);
lean_ctor_set(x_4, 6, x_2);
lean_ctor_set(x_4, 7, x_2);
return x_4;
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
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2;
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
x_2 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2;
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
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
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
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_tc");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Level_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_7, x_2, x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_level_update_succ(x_1, x_10);
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
x_14 = lean_level_update_succ(x_1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_16);
x_18 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_16, x_2, x_3);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set_uint64(x_22, sizeof(void*)*1, x_17);
x_23 = lean_level_update_succ(x_22, x_19);
if (lean_is_scalar(x_21)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_21;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
case 2:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_inc(x_26);
x_28 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_26, x_2, x_3);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_27);
x_31 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_27, x_2, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_level_update_max(x_1, x_29, x_33);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_level_update_max(x_1, x_29, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_39);
x_42 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_39, x_2, x_3);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_40);
x_45 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_40, x_2, x_44);
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
x_49 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set_uint64(x_49, sizeof(void*)*2, x_41);
x_50 = lean_level_update_max(x_49, x_43, x_46);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
case 3:
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_1);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_53 = lean_ctor_get(x_1, 0);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_inc(x_53);
x_55 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_53, x_2, x_3);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_54);
x_58 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_54, x_2, x_57);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_level_update_imax(x_1, x_56, x_60);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
x_64 = lean_level_update_imax(x_1, x_56, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_66 = lean_ctor_get(x_1, 0);
x_67 = lean_ctor_get(x_1, 1);
x_68 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_66);
x_69 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_66, x_2, x_3);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_67);
x_72 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_67, x_2, x_71);
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
x_76 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_76, 0, x_66);
lean_ctor_set(x_76, 1, x_67);
lean_ctor_set_uint64(x_76, sizeof(void*)*2, x_68);
x_77 = lean_level_update_imax(x_76, x_70, x_73);
if (lean_is_scalar(x_75)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_75;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
return x_78;
}
}
case 5:
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_1, 0);
lean_inc(x_79);
lean_inc(x_79);
x_80 = l_Lean_MetavarContext_isLevelAssignable(x_2, x_79);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_3);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_1);
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_3, 2);
lean_inc(x_85);
lean_inc(x_79);
lean_inc(x_84);
x_86 = l_Std_HashMapImp_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__1(x_84, x_79);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_3);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_88 = lean_ctor_get(x_3, 2);
lean_dec(x_88);
x_89 = lean_ctor_get(x_3, 1);
lean_dec(x_89);
x_90 = lean_ctor_get(x_3, 0);
lean_dec(x_90);
x_91 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2;
lean_inc(x_83);
x_92 = lean_name_mk_numeral(x_91, x_83);
x_93 = l_Lean_mkLevelParam(x_92);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_83, x_94);
lean_dec(x_83);
lean_inc(x_93);
x_96 = l_Std_HashMap_insert___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__3(x_84, x_79, x_93);
lean_ctor_set(x_3, 1, x_96);
lean_ctor_set(x_3, 0, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_3);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_3);
x_98 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2;
lean_inc(x_83);
x_99 = lean_name_mk_numeral(x_98, x_83);
x_100 = l_Lean_mkLevelParam(x_99);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_add(x_83, x_101);
lean_dec(x_83);
lean_inc(x_100);
x_103 = l_Std_HashMap_insert___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__3(x_84, x_79, x_100);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_85);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_100);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_79);
x_106 = lean_ctor_get(x_86, 0);
lean_inc(x_106);
lean_dec(x_86);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_3);
return x_107;
}
}
}
default: 
{
lean_object* x_108; 
lean_dec(x_2);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_1);
lean_ctor_set(x_108, 1, x_3);
return x_108;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_9 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_7, x_2, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___spec__1(x_8, x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_12, 0, x_1);
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
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_2);
x_20 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_18, x_2, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_List_mapM___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___spec__1(x_19, x_2, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_24);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_inc(x_6);
x_7 = l_Lean_MetavarContext_isExprAssignable(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
lean_inc(x_6);
lean_inc(x_11);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__1(x_11, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_3, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_dec(x_16);
x_17 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2;
lean_inc(x_9);
x_18 = lean_name_mk_numeral(x_17, x_9);
x_19 = l_Lean_mkFVar(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_9, x_20);
lean_dec(x_9);
lean_inc(x_19);
x_22 = l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(x_11, x_6, x_19);
lean_ctor_set(x_3, 2, x_22);
lean_ctor_set(x_3, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_24 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2;
lean_inc(x_9);
x_25 = lean_name_mk_numeral(x_24, x_9);
x_26 = l_Lean_mkFVar(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_9, x_27);
lean_dec(x_9);
lean_inc(x_26);
x_29 = l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(x_11, x_6, x_26);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_10);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
}
}
case 3:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_35, x_2, x_3);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_expr_update_sort(x_1, x_38);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_expr_update_sort(x_1, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_44);
lean_dec(x_1);
lean_inc(x_44);
x_46 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel(x_44, x_2, x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set_uint64(x_50, sizeof(void*)*1, x_45);
x_51 = lean_expr_update_sort(x_50, x_47);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
}
case 4:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_1);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
x_55 = l_List_mapM___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___spec__1(x_54, x_2, x_3);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_expr_update_const(x_1, x_57);
lean_ctor_set(x_55, 0, x_58);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_55, 0);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_55);
x_61 = lean_expr_update_const(x_1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_1, 0);
x_64 = lean_ctor_get(x_1, 1);
x_65 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_1);
lean_inc(x_64);
x_66 = l_List_mapM___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___spec__1(x_64, x_2, x_3);
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
x_70 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_64);
lean_ctor_set_uint64(x_70, sizeof(void*)*2, x_65);
x_71 = lean_expr_update_const(x_70, x_67);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
}
case 5:
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_74 = lean_ctor_get(x_1, 0);
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_inc(x_74);
x_76 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_74, x_2, x_3);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_75);
x_79 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_75, x_2, x_78);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_expr_update_app(x_1, x_77, x_81);
lean_ctor_set(x_79, 0, x_82);
return x_79;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_79, 0);
x_84 = lean_ctor_get(x_79, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_79);
x_85 = lean_expr_update_app(x_1, x_77, x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; uint64_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_87 = lean_ctor_get(x_1, 0);
x_88 = lean_ctor_get(x_1, 1);
x_89 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_87);
x_90 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_87, x_2, x_3);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_88);
x_93 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_88, x_2, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
x_97 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_88);
lean_ctor_set_uint64(x_97, sizeof(void*)*2, x_89);
x_98 = lean_expr_update_app(x_97, x_91, x_94);
if (lean_is_scalar(x_96)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_96;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_95);
return x_99;
}
}
case 6:
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_1);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint64_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_101 = lean_ctor_get(x_1, 1);
x_102 = lean_ctor_get(x_1, 2);
x_103 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_2);
lean_inc(x_101);
x_104 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_101, x_2, x_3);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_102);
x_107 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_102, x_2, x_106);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = (uint8_t)((x_103 << 24) >> 61);
x_111 = lean_expr_update_lambda(x_1, x_110, x_105, x_109);
lean_ctor_set(x_107, 0, x_111);
return x_107;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_107, 0);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_107);
x_114 = (uint8_t)((x_103 << 24) >> 61);
x_115 = lean_expr_update_lambda(x_1, x_114, x_105, x_112);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint64_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; 
x_117 = lean_ctor_get(x_1, 0);
x_118 = lean_ctor_get(x_1, 1);
x_119 = lean_ctor_get(x_1, 2);
x_120 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_118);
x_121 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_118, x_2, x_3);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_119);
x_124 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_119, x_2, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_128, 0, x_117);
lean_ctor_set(x_128, 1, x_118);
lean_ctor_set(x_128, 2, x_119);
lean_ctor_set_uint64(x_128, sizeof(void*)*3, x_120);
x_129 = (uint8_t)((x_120 << 24) >> 61);
x_130 = lean_expr_update_lambda(x_128, x_129, x_122, x_125);
if (lean_is_scalar(x_127)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_127;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
}
case 7:
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_1);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint64_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_133 = lean_ctor_get(x_1, 1);
x_134 = lean_ctor_get(x_1, 2);
x_135 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_2);
lean_inc(x_133);
x_136 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_133, x_2, x_3);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
lean_inc(x_134);
x_139 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_134, x_2, x_138);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = (uint8_t)((x_135 << 24) >> 61);
x_143 = lean_expr_update_forall(x_1, x_142, x_137, x_141);
lean_ctor_set(x_139, 0, x_143);
return x_139;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_139, 0);
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_139);
x_146 = (uint8_t)((x_135 << 24) >> 61);
x_147 = lean_expr_update_forall(x_1, x_146, x_137, x_144);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint64_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; 
x_149 = lean_ctor_get(x_1, 0);
x_150 = lean_ctor_get(x_1, 1);
x_151 = lean_ctor_get(x_1, 2);
x_152 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_150);
x_153 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_150, x_2, x_3);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_151);
x_156 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_151, x_2, x_155);
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
x_160 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_160, 0, x_149);
lean_ctor_set(x_160, 1, x_150);
lean_ctor_set(x_160, 2, x_151);
lean_ctor_set_uint64(x_160, sizeof(void*)*3, x_152);
x_161 = (uint8_t)((x_152 << 24) >> 61);
x_162 = lean_expr_update_forall(x_160, x_161, x_154, x_157);
if (lean_is_scalar(x_159)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_159;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_158);
return x_163;
}
}
case 8:
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_1);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_165 = lean_ctor_get(x_1, 1);
x_166 = lean_ctor_get(x_1, 2);
x_167 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_inc(x_165);
x_168 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_165, x_2, x_3);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_2);
lean_inc(x_166);
x_171 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_166, x_2, x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
lean_inc(x_167);
x_174 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_167, x_2, x_173);
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_174, 0);
x_177 = lean_expr_update_let(x_1, x_169, x_172, x_176);
lean_ctor_set(x_174, 0, x_177);
return x_174;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_174, 0);
x_179 = lean_ctor_get(x_174, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_174);
x_180 = lean_expr_update_let(x_1, x_169, x_172, x_178);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint64_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_182 = lean_ctor_get(x_1, 0);
x_183 = lean_ctor_get(x_1, 1);
x_184 = lean_ctor_get(x_1, 2);
x_185 = lean_ctor_get(x_1, 3);
x_186 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_183);
x_187 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_183, x_2, x_3);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
lean_inc(x_2);
lean_inc(x_184);
x_190 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_184, x_2, x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
lean_inc(x_185);
x_193 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_185, x_2, x_192);
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
x_197 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_197, 0, x_182);
lean_ctor_set(x_197, 1, x_183);
lean_ctor_set(x_197, 2, x_184);
lean_ctor_set(x_197, 3, x_185);
lean_ctor_set_uint64(x_197, sizeof(void*)*4, x_186);
x_198 = lean_expr_update_let(x_197, x_188, x_191, x_194);
if (lean_is_scalar(x_196)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_196;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_195);
return x_199;
}
}
case 10:
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_1);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_201 = lean_ctor_get(x_1, 1);
lean_inc(x_201);
x_202 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_201, x_2, x_3);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_202, 0);
x_205 = lean_expr_update_mdata(x_1, x_204);
lean_ctor_set(x_202, 0, x_205);
return x_202;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_202, 0);
x_207 = lean_ctor_get(x_202, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_202);
x_208 = lean_expr_update_mdata(x_1, x_206);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; uint64_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_210 = lean_ctor_get(x_1, 0);
x_211 = lean_ctor_get(x_1, 1);
x_212 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_1);
lean_inc(x_211);
x_213 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_211, x_2, x_3);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_216 = x_213;
} else {
 lean_dec_ref(x_213);
 x_216 = lean_box(0);
}
x_217 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_217, 0, x_210);
lean_ctor_set(x_217, 1, x_211);
lean_ctor_set_uint64(x_217, sizeof(void*)*2, x_212);
x_218 = lean_expr_update_mdata(x_217, x_214);
if (lean_is_scalar(x_216)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_216;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_215);
return x_219;
}
}
case 11:
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_1);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_221 = lean_ctor_get(x_1, 2);
lean_inc(x_221);
x_222 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_221, x_2, x_3);
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_222, 0);
x_225 = lean_expr_update_proj(x_1, x_224);
lean_ctor_set(x_222, 0, x_225);
return x_222;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_222, 0);
x_227 = lean_ctor_get(x_222, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_222);
x_228 = lean_expr_update_proj(x_1, x_226);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint64_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_230 = lean_ctor_get(x_1, 0);
x_231 = lean_ctor_get(x_1, 1);
x_232 = lean_ctor_get(x_1, 2);
x_233 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_1);
lean_inc(x_232);
x_234 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_232, x_2, x_3);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
x_238 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_238, 0, x_230);
lean_ctor_set(x_238, 1, x_231);
lean_ctor_set(x_238, 2, x_232);
lean_ctor_set_uint64(x_238, sizeof(void*)*3, x_233);
x_239 = lean_expr_update_proj(x_238, x_235);
if (lean_is_scalar(x_237)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_237;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_236);
return x_240;
}
}
default: 
{
lean_object* x_241; 
lean_dec(x_2);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_1);
lean_ctor_set(x_241, 1, x_3);
return x_241;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_SynthInstance_MkTableKey_State_lmap___default___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_SynthInstance_mkTableKey___closed__1;
x_4 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr(x_2, x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_instInhabitedAnswer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2;
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
x_2 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__2;
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
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_State_tableEntries___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_State_tableEntries___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_State_tableEntries___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Meta_SynthInstance_State_tableEntries___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_checkMaxHeartbeats___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeclass");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_checkMaxHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_Meta_SynthInstance_checkMaxHeartbeats___closed__1;
x_10 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__4;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_SynthInstance_getInstances___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
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
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_SynthInstance_getInstances___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_SynthInstance_getInstances___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Array_insertionSort_swapLoop___at_Lean_Meta_SynthInstance_getInstances___spec__3(x_1, x_2, lean_box(0));
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
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_SynthInstance_getInstances___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_mapM___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_10, x_2, x_3, x_4, x_5, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_13);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_6);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_List_mapM___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_21, x_2, x_3, x_4, x_5, x_24);
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
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.SynthInstance");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.SynthInstance.getInstances");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("global instance is not a constant");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__1;
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__2;
x_3 = lean_unsigned_to_nat(203u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_inc(x_1);
x_34 = l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(x_1, x_32);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
lean_inc(x_33);
x_35 = l_List_mapM___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_33, x_6, x_7, x_8, x_9, x_10);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_expr_update_const(x_30, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_35, 0, x_39);
x_13 = x_35;
goto block_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_expr_update_const(x_30, x_40);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
x_13 = x_44;
goto block_29;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_30);
lean_dec(x_33);
lean_dec(x_32);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_10);
x_13 = x_46;
goto block_29;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint64_t x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
x_49 = lean_ctor_get_uint64(x_30, sizeof(void*)*2);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
lean_inc(x_47);
lean_inc(x_1);
x_50 = l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(x_1, x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_inc(x_48);
x_51 = l_List_mapM___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_48, x_6, x_7, x_8, x_9, x_10);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set_uint64(x_55, sizeof(void*)*2, x_49);
x_56 = lean_expr_update_const(x_55, x_52);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
x_13 = x_58;
goto block_29;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_48);
lean_dec(x_47);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_10);
x_13 = x_60;
goto block_29;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_30);
x_61 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_62 = l_panic___at___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___spec__4(x_61, x_6, x_7, x_8, x_9, x_10);
x_13 = x_62;
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
lean_object* x_63; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_10);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Meta_SynthInstance_getInstances___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6(x_1, x_2, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__7(x_3, x_1, x_16, x_17, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type class instance expected");
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
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("globalInstances");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_2 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_isClass_x3f(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
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
x_17 = l_Lean_throwError___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_16, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Meta_DiscrTree_getUnify___rarg(x_21, x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_get_size(x_24);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_insertionSort_traverse___at_Lean_Meta_SynthInstance_getInstances___spec__2(x_24, x_27, x_26);
x_29 = l_Lean_Meta_getErasedInstances___rarg(x_7, x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_get_size(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Array_filterMapM___at_Lean_Meta_SynthInstance_getInstances___spec__5(x_30, x_28, x_27, x_32, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__8;
x_57 = lean_st_ref_get(x_7, x_35);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 3);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get_uint8(x_59, sizeof(void*)*1);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = 0;
x_37 = x_62;
x_38 = x_61;
goto block_56;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_36, x_4, x_5, x_6, x_7, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_37 = x_67;
x_38 = x_66;
goto block_56;
}
block_56:
{
if (x_37 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_3);
x_39 = lean_box(0);
x_40 = l_Lean_Meta_SynthInstance_getInstances___lambda__1(x_1, x_34, x_19, x_39, x_4, x_5, x_6, x_7, x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_1);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_3);
x_42 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__10;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_34);
x_46 = lean_array_to_list(lean_box(0), x_34);
x_47 = lean_box(0);
x_48 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_46, x_47);
x_49 = l_Lean_MessageData_ofList(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
x_52 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_36, x_51, x_4, x_5, x_6, x_7, x_38);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Meta_SynthInstance_getInstances___lambda__1(x_1, x_34, x_19, x_53, x_4, x_5, x_6, x_7, x_54);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_53);
lean_dec(x_19);
lean_dec(x_1);
return x_55;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_33);
if (x_68 == 0)
{
return x_33;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_33, 0);
x_70 = lean_ctor_get(x_33, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_33);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_23);
if (x_72 == 0)
{
return x_23;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_23, 0);
x_74 = lean_ctor_get(x_23, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_23);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_9);
if (x_76 == 0)
{
return x_9;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_9, 0);
x_78 = lean_ctor_get(x_9, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_9);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
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
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getInstances___lambda__2), 8, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_SynthInstance_getInstances___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_SynthInstance_getInstances___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Meta_SynthInstance_getInstances___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_filterMapM___at_Lean_Meta_SynthInstance_getInstances___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__7(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_getInstances___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
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
lean_inc(x_4);
x_11 = l_Lean_Meta_instantiateMVars(x_9, x_3, x_4, x_5, x_6, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_checkTraceOption(x_9, x_1);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg), 9, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Expr_hash(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_AssocList_replace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_1, x_2, x_8);
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
x_15 = l_Std_AssocList_replace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Expr_hash(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_traceMsg");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Util_Trace_0__Lean_addTraceOptions(x_12);
x_15 = lean_st_ref_take(x_8, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 3);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__2;
x_24 = l_Lean_Name_append(x_1, x_23);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_1);
x_26 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__4;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__6;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_14);
x_31 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_10);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Std_PersistentArray_push___rarg(x_22, x_34);
lean_ctor_set(x_17, 0, x_35);
x_36 = lean_st_ref_set(x_8, x_16, x_18);
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
uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_43 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_44 = lean_ctor_get(x_17, 0);
lean_inc(x_44);
lean_dec(x_17);
x_45 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__2;
x_46 = l_Lean_Name_append(x_1, x_45);
x_47 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_47, 0, x_1);
x_48 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__4;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__6;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_14);
x_53 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_10);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_10);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Std_PersistentArray_push___rarg(x_44, x_56);
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_43);
lean_ctor_set(x_16, 3, x_58);
x_59 = lean_st_ref_set(x_8, x_16, x_18);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_64 = lean_ctor_get(x_16, 0);
x_65 = lean_ctor_get(x_16, 1);
x_66 = lean_ctor_get(x_16, 2);
x_67 = lean_ctor_get(x_16, 4);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_16);
x_68 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_69 = lean_ctor_get(x_17, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_70 = x_17;
} else {
 lean_dec_ref(x_17);
 x_70 = lean_box(0);
}
x_71 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__2;
x_72 = l_Lean_Name_append(x_1, x_71);
x_73 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_73, 0, x_1);
x_74 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__4;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__6;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_14);
x_79 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_81, 0, x_72);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_10);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_10);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Std_PersistentArray_push___rarg(x_69, x_82);
if (lean_is_scalar(x_70)) {
 x_84 = lean_alloc_ctor(0, 1, 1);
} else {
 x_84 = x_70;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_68);
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_64);
lean_ctor_set(x_85, 1, x_65);
lean_ctor_set(x_85, 2, x_66);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_67);
x_86 = lean_st_ref_set(x_8, x_85, x_18);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
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
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_1);
x_12 = l_Lean_Meta_SynthInstance_mkGeneratorNode_x3f(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__3___closed__1;
x_23 = lean_array_push(x_22, x_3);
x_24 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_st_ref_get(x_10, x_20);
lean_dec(x_10);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_take(x_6, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_ctor_get(x_29, 3);
x_34 = lean_array_push(x_32, x_21);
x_35 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_33, x_1, x_25);
lean_ctor_set(x_29, 3, x_35);
lean_ctor_set(x_29, 1, x_34);
x_36 = lean_st_ref_set(x_6, x_29, x_30);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
x_45 = lean_ctor_get(x_29, 2);
x_46 = lean_ctor_get(x_29, 3);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
x_47 = lean_array_push(x_44, x_21);
x_48 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_46, x_1, x_25);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_45);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_st_ref_set(x_6, x_49, x_30);
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
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_12);
if (x_55 == 0)
{
return x_12;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_12, 0);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_12);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_5 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__3(x_1, x_2, x_3, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_1);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__3(x_1, x_2, x_3, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("newSubgoal");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_2 = l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_newSubgoal___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_newSubgoal___lambda__2), 9, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Lean_Meta_SynthInstance_newSubgoal___closed__3;
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg), 9, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_newSubgoal___lambda__4___boxed), 12, 4);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_4);
lean_closure_set(x_16, 3, x_12);
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg), 9, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__4(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
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
x_15 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(x_14, x_1);
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
x_19 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(x_18, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(x_1, x_2);
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
x_1 = lean_mk_string("Lean.Meta.SynthInstance.getEntry");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid key at synthInstance");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__1;
x_2 = l_Lean_Meta_SynthInstance_getEntry___closed__1;
x_3 = lean_unsigned_to_nat(242u);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_instantiateMVars(x_2, x_5, x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_12);
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
x_16 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1___boxed), 8, 1);
lean_closure_set(x_10, 0, x_2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__2___boxed), 9, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg), 9, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_getSubgoalsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_8) == 7)
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
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
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; 
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
x_32 = l_Lean_mkApp(x_7, x_31);
x_33 = (uint8_t)((x_16 << 24) >> 61);
x_34 = l_Lean_BinderInfo_isInstImplicit(x_33);
x_35 = lean_array_push(x_4, x_31);
if (x_34 == 0)
{
lean_dec(x_29);
x_4 = x_35;
x_7 = x_32;
x_8 = x_15;
x_13 = x_30;
goto _start;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_6);
x_4 = x_35;
x_6 = x_37;
x_7 = x_32;
x_8 = x_15;
x_13 = x_30;
goto _start;
}
}
else
{
uint8_t x_39; 
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
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_array_get_size(x_4);
x_44 = lean_expr_instantiate_rev_range(x_8, x_5, x_43, x_4);
lean_dec(x_5);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_45 = lean_whnf(x_44, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = l_Lean_Expr_isForall(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_43);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_6);
lean_ctor_set(x_50, 1, x_7);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_45, 0, x_50);
return x_45;
}
else
{
lean_free_object(x_45);
x_5 = x_43;
x_8 = x_47;
x_13 = x_48;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_45, 0);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_45);
x_54 = l_Lean_Expr_isForall(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_43);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_6);
lean_ctor_set(x_55, 1, x_7);
lean_ctor_set(x_55, 2, x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
x_5 = x_43;
x_8 = x_52;
x_13 = x_53;
goto _start;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_43);
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
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
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
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_List_reverse___rarg(x_29);
lean_ctor_set(x_18, 0, x_30);
lean_ctor_set(x_22, 0, x_18);
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
x_33 = lean_ctor_get(x_18, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_34 = l_List_reverse___rarg(x_31);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_22, 0, x_35);
return x_22;
}
}
else
{
lean_ctor_set(x_22, 0, x_18);
return x_22;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1;
x_40 = l_Lean_TagAttribute_hasTag(x_39, x_38, x_21);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 2);
lean_inc(x_43);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_44 = x_18;
} else {
 lean_dec_ref(x_18);
 x_44 = lean_box(0);
}
x_45 = l_List_reverse___rarg(x_41);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 3, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_37);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_18);
lean_ctor_set(x_48, 1, x_37);
return x_48;
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
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_16, 0);
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_16);
x_51 = l_Lean_Expr_getAppFn(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_51) == 4)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_get(x_8, x_50);
lean_dec(x_8);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1;
x_59 = l_Lean_TagAttribute_hasTag(x_58, x_57, x_52);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_49, 2);
lean_inc(x_62);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 x_63 = x_49;
} else {
 lean_dec_ref(x_49);
 x_63 = lean_box(0);
}
x_64 = l_List_reverse___rarg(x_60);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 3, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_62);
if (lean_is_scalar(x_56)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_56;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_55);
return x_66;
}
else
{
lean_object* x_67; 
if (lean_is_scalar(x_56)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_56;
}
lean_ctor_set(x_67, 0, x_49);
lean_ctor_set(x_67, 1, x_55);
return x_67;
}
}
else
{
lean_object* x_68; 
lean_dec(x_51);
lean_dec(x_8);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_49);
lean_ctor_set(x_68, 1, x_50);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_8);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_16);
if (x_69 == 0)
{
return x_16;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_16, 0);
x_71 = lean_ctor_get(x_16, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_16);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_10);
if (x_73 == 0)
{
return x_10;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_10, 0);
x_75 = lean_ctor_get(x_10, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_10);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failure");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failure assigning");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("success");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_29 = lean_st_ref_get(x_12, x_17);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = 0;
x_18 = x_34;
x_19 = x_33;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
lean_inc(x_3);
x_36 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_3, x_9, x_10, x_11, x_12, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_unbox(x_37);
lean_dec(x_37);
x_18 = x_39;
x_19 = x_38;
goto block_28;
}
block_28:
{
lean_object* x_20; 
x_20 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1;
if (x_18 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = lean_apply_6(x_20, x_21, x_9, x_10, x_11, x_12, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__3;
x_24 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_23, x_9, x_10, x_11, x_12, x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_apply_6(x_20, x_25, x_9, x_10, x_11, x_12, x_26);
return x_27;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_dec(x_14);
x_41 = 0;
x_42 = 1;
x_43 = 1;
x_44 = l_Lean_Meta_mkLambdaFVars(x_4, x_5, x_41, x_42, x_43, x_9, x_10, x_11, x_12, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_47 = l_Lean_Meta_isExprDefEq(x_6, x_45, x_9, x_10, x_11, x_12, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_7);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_62 = lean_st_ref_get(x_12, x_50);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 3);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_51 = x_41;
x_52 = x_66;
goto block_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
lean_inc(x_3);
x_68 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_3, x_9, x_10, x_11, x_12, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_51 = x_71;
x_52 = x_70;
goto block_61;
}
block_61:
{
lean_object* x_53; 
x_53 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1;
if (x_51 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_3);
x_54 = lean_box(0);
x_55 = lean_apply_6(x_53, x_54, x_9, x_10, x_11, x_12, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__5;
x_57 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_56, x_9, x_10, x_11, x_12, x_52);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_apply_6(x_53, x_58, x_9, x_10, x_11, x_12, x_59);
return x_60;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_72 = lean_ctor_get(x_47, 1);
lean_inc(x_72);
lean_dec(x_47);
x_83 = lean_st_ref_get(x_12, x_72);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 3);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_ctor_get_uint8(x_85, sizeof(void*)*1);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_73 = x_41;
x_74 = x_87;
goto block_82;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_dec(x_83);
lean_inc(x_3);
x_89 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_3, x_9, x_10, x_11, x_12, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_unbox(x_90);
lean_dec(x_90);
x_73 = x_92;
x_74 = x_91;
goto block_82;
}
block_82:
{
if (x_73 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_3);
x_75 = lean_box(0);
x_76 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2(x_7, x_75, x_9, x_10, x_11, x_12, x_74);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__7;
x_78 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_77, x_9, x_10, x_11, x_12, x_74);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2(x_7, x_79, x_9, x_10, x_11, x_12, x_80);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_79);
return x_81;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_47);
if (x_93 == 0)
{
return x_47;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_47, 0);
x_95 = lean_ctor_get(x_47, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_47);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_97 = !lean_is_exclusive(x_44);
if (x_97 == 0)
{
return x_44;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_44, 0);
x_99 = lean_ctor_get(x_44, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_44);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_14);
if (x_101 == 0)
{
return x_14;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_14, 0);
x_103 = lean_ctor_get(x_14, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_14);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tryResolve");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_2 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" =?= ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
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
x_18 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__2;
x_36 = lean_st_ref_get(x_10, x_14);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 3);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = 0;
x_19 = x_41;
x_20 = x_40;
goto block_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_18, x_7, x_8, x_9, x_10, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_19 = x_46;
x_20 = x_45;
goto block_35;
}
block_35:
{
if (x_19 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3(x_6, x_17, x_18, x_5, x_16, x_4, x_15, x_21, x_7, x_8, x_9, x_10, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_6);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_6);
x_24 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__4;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_17);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_17);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
x_31 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_18, x_30, x_7, x_8, x_9, x_10, x_20);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3(x_6, x_17, x_18, x_5, x_16, x_4, x_15, x_32, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_32);
return x_34;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_12);
if (x_47 == 0)
{
return x_12;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_12, 0);
x_49 = lean_ctor_get(x_12, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_12);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4), 11, 4);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_4);
x_8 = l_Lean_Meta_instantiateMVars(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Lean_Meta_hasAssignableMVar(x_9, x_3, x_4, x_5, x_6, x_10);
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
x_33 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5(x_9, x_2, x_32, x_3, x_4, x_5, x_6, x_31);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__2;
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 3);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__3;
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
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
x_23 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_22);
lean_ctor_set(x_9, 3, x_24);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_33 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_34 = x_10;
} else {
 lean_dec_ref(x_10);
 x_34 = lean_box(0);
}
x_35 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__3;
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 1, 1);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_33);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_32);
x_38 = lean_st_ref_set(x_1, x_37, x_11);
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
lean_ctor_set(x_41, 0, x_7);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___boxed), 2, 0);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_traceCtx");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_st_ref_take(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 3);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = l_Std_PersistentArray_isEmpty___rarg(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_20 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__2;
x_21 = l_Lean_Name_append(x_2, x_20);
x_22 = l_Std_PersistentArray_toArray___rarg(x_18);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_24, x_25, x_22);
x_27 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Std_PersistentArray_push___rarg(x_1, x_29);
lean_ctor_set(x_13, 0, x_30);
x_31 = lean_st_ref_set(x_9, x_12, x_14);
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
lean_object* x_38; uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_3);
lean_ctor_set(x_13, 0, x_1);
x_38 = lean_st_ref_set(x_9, x_12, x_14);
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
}
else
{
uint8_t x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
x_46 = lean_ctor_get(x_13, 0);
lean_inc(x_46);
lean_dec(x_13);
x_47 = l_Std_PersistentArray_isEmpty___rarg(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__2;
x_49 = l_Lean_Name_append(x_2, x_48);
x_50 = l_Std_PersistentArray_toArray___rarg(x_46);
x_51 = lean_array_get_size(x_50);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = 0;
x_54 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_52, x_53, x_50);
x_55 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Std_PersistentArray_push___rarg(x_1, x_57);
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_45);
lean_ctor_set(x_12, 3, x_59);
x_60 = lean_st_ref_set(x_9, x_12, x_14);
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
x_63 = lean_box(0);
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
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_46);
lean_dec(x_3);
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_45);
lean_ctor_set(x_12, 3, x_65);
x_66 = lean_st_ref_set(x_9, x_12, x_14);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_box(0);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_71 = lean_ctor_get(x_12, 0);
x_72 = lean_ctor_get(x_12, 1);
x_73 = lean_ctor_get(x_12, 2);
x_74 = lean_ctor_get(x_12, 4);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_12);
x_75 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
x_76 = lean_ctor_get(x_13, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_77 = x_13;
} else {
 lean_dec_ref(x_13);
 x_77 = lean_box(0);
}
x_78 = l_Std_PersistentArray_isEmpty___rarg(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_79 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__2;
x_80 = l_Lean_Name_append(x_2, x_79);
x_81 = l_Std_PersistentArray_toArray___rarg(x_76);
x_82 = lean_array_get_size(x_81);
x_83 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_84 = 0;
x_85 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_83, x_84, x_81);
x_86 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_3);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Std_PersistentArray_push___rarg(x_1, x_88);
if (lean_is_scalar(x_77)) {
 x_90 = lean_alloc_ctor(0, 1, 1);
} else {
 x_90 = x_77;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_75);
x_91 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_91, 0, x_71);
lean_ctor_set(x_91, 1, x_72);
lean_ctor_set(x_91, 2, x_73);
lean_ctor_set(x_91, 3, x_90);
lean_ctor_set(x_91, 4, x_74);
x_92 = lean_st_ref_set(x_9, x_91, x_14);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = lean_box(0);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_76);
lean_dec(x_3);
if (lean_is_scalar(x_77)) {
 x_97 = lean_alloc_ctor(0, 1, 1);
} else {
 x_97 = x_77;
}
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_75);
x_98 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_98, 0, x_71);
lean_ctor_set(x_98, 1, x_72);
lean_ctor_set(x_98, 2, x_73);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set(x_98, 4, x_74);
x_99 = lean_st_ref_set(x_9, x_98, x_14);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_tryResolveCore(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolve___lambda__1___boxed), 9, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
x_222 = lean_st_ref_get(x_9, x_10);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_223, 3);
lean_inc(x_224);
lean_dec(x_223);
x_225 = lean_ctor_get_uint8(x_224, sizeof(void*)*1);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = lean_ctor_get(x_222, 1);
lean_inc(x_226);
lean_dec(x_222);
x_227 = 0;
x_12 = x_227;
x_13 = x_226;
goto block_221;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_228 = lean_ctor_get(x_222, 1);
lean_inc(x_228);
lean_dec(x_222);
x_229 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__2;
x_230 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_229, x_4, x_5, x_6, x_7, x_8, x_9, x_228);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_unbox(x_231);
lean_dec(x_231);
x_12 = x_233;
x_13 = x_232;
goto block_221;
}
block_221:
{
if (x_12 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_st_ref_get(x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
lean_dec(x_16);
x_19 = lean_st_ref_take(x_9, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 3);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = 0;
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_26);
x_27 = lean_st_ref_set(x_9, x_20, x_22);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_9);
x_29 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_9, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_take(x_9, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_35, 3);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_18);
x_41 = lean_st_ref_set(x_9, x_35, x_37);
lean_dec(x_9);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_30);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_36, 0);
lean_inc(x_46);
lean_dec(x_36);
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_18);
lean_ctor_set(x_35, 3, x_47);
x_48 = lean_st_ref_set(x_9, x_35, x_37);
lean_dec(x_9);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_30);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
x_54 = lean_ctor_get(x_35, 2);
x_55 = lean_ctor_get(x_35, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_56 = lean_ctor_get(x_36, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_57 = x_36;
} else {
 lean_dec_ref(x_36);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 1, 1);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_18);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_53);
lean_ctor_set(x_59, 2, x_54);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set(x_59, 4, x_55);
x_60 = lean_st_ref_set(x_9, x_59, x_37);
lean_dec(x_9);
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
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_30);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_64 = lean_ctor_get(x_29, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_29, 1);
lean_inc(x_65);
lean_dec(x_29);
x_66 = lean_st_ref_get(x_9, x_65);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_st_ref_take(x_9, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_69, 3);
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_18);
x_75 = lean_st_ref_set(x_9, x_69, x_71);
lean_dec(x_9);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set_tag(x_75, 1);
lean_ctor_set(x_75, 0, x_64);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_64);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_70, 0);
lean_inc(x_80);
lean_dec(x_70);
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_18);
lean_ctor_set(x_69, 3, x_81);
x_82 = lean_st_ref_set(x_9, x_69, x_71);
lean_dec(x_9);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
 lean_ctor_set_tag(x_85, 1);
}
lean_ctor_set(x_85, 0, x_64);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_86 = lean_ctor_get(x_69, 0);
x_87 = lean_ctor_get(x_69, 1);
x_88 = lean_ctor_get(x_69, 2);
x_89 = lean_ctor_get(x_69, 4);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_69);
x_90 = lean_ctor_get(x_70, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_91 = x_70;
} else {
 lean_dec_ref(x_70);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 1, 1);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_18);
x_93 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_93, 0, x_86);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_92);
lean_ctor_set(x_93, 4, x_89);
x_94 = lean_st_ref_set(x_9, x_93, x_71);
lean_dec(x_9);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_64);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_21, 0);
lean_inc(x_98);
lean_dec(x_21);
x_99 = 0;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
lean_ctor_set(x_20, 3, x_100);
x_101 = lean_st_ref_set(x_9, x_20, x_22);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
lean_inc(x_9);
x_103 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_st_ref_get(x_9, x_105);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_take(x_9, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 4);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 lean_ctor_release(x_109, 2);
 lean_ctor_release(x_109, 3);
 lean_ctor_release(x_109, 4);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_110, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_118 = x_110;
} else {
 lean_dec_ref(x_110);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 1, 1);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_18);
if (lean_is_scalar(x_116)) {
 x_120 = lean_alloc_ctor(0, 5, 0);
} else {
 x_120 = x_116;
}
lean_ctor_set(x_120, 0, x_112);
lean_ctor_set(x_120, 1, x_113);
lean_ctor_set(x_120, 2, x_114);
lean_ctor_set(x_120, 3, x_119);
lean_ctor_set(x_120, 4, x_115);
x_121 = lean_st_ref_set(x_9, x_120, x_111);
lean_dec(x_9);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_104);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_125 = lean_ctor_get(x_103, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_103, 1);
lean_inc(x_126);
lean_dec(x_103);
x_127 = lean_st_ref_get(x_9, x_126);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_st_ref_take(x_9, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_130, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 4);
lean_inc(x_136);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 x_137 = x_130;
} else {
 lean_dec_ref(x_130);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_131, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_139 = x_131;
} else {
 lean_dec_ref(x_131);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 1, 1);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_18);
if (lean_is_scalar(x_137)) {
 x_141 = lean_alloc_ctor(0, 5, 0);
} else {
 x_141 = x_137;
}
lean_ctor_set(x_141, 0, x_133);
lean_ctor_set(x_141, 1, x_134);
lean_ctor_set(x_141, 2, x_135);
lean_ctor_set(x_141, 3, x_140);
lean_ctor_set(x_141, 4, x_136);
x_142 = lean_st_ref_set(x_9, x_141, x_132);
lean_dec(x_9);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
 lean_ctor_set_tag(x_145, 1);
}
lean_ctor_set(x_145, 0, x_125);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_146 = lean_ctor_get(x_20, 0);
x_147 = lean_ctor_get(x_20, 1);
x_148 = lean_ctor_get(x_20, 2);
x_149 = lean_ctor_get(x_20, 4);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_20);
x_150 = lean_ctor_get(x_21, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_151 = x_21;
} else {
 lean_dec_ref(x_21);
 x_151 = lean_box(0);
}
x_152 = 0;
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 1, 1);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_152);
x_154 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_154, 0, x_146);
lean_ctor_set(x_154, 1, x_147);
lean_ctor_set(x_154, 2, x_148);
lean_ctor_set(x_154, 3, x_153);
lean_ctor_set(x_154, 4, x_149);
x_155 = lean_st_ref_set(x_9, x_154, x_22);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
lean_inc(x_9);
x_157 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_st_ref_get(x_9, x_159);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_st_ref_take(x_9, x_161);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_163, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_163, 4);
lean_inc(x_169);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 lean_ctor_release(x_163, 3);
 lean_ctor_release(x_163, 4);
 x_170 = x_163;
} else {
 lean_dec_ref(x_163);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_164, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_172 = x_164;
} else {
 lean_dec_ref(x_164);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 1, 1);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_18);
if (lean_is_scalar(x_170)) {
 x_174 = lean_alloc_ctor(0, 5, 0);
} else {
 x_174 = x_170;
}
lean_ctor_set(x_174, 0, x_166);
lean_ctor_set(x_174, 1, x_167);
lean_ctor_set(x_174, 2, x_168);
lean_ctor_set(x_174, 3, x_173);
lean_ctor_set(x_174, 4, x_169);
x_175 = lean_st_ref_set(x_9, x_174, x_165);
lean_dec(x_9);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_177 = x_175;
} else {
 lean_dec_ref(x_175);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_158);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_179 = lean_ctor_get(x_157, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_157, 1);
lean_inc(x_180);
lean_dec(x_157);
x_181 = lean_st_ref_get(x_9, x_180);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_st_ref_take(x_9, x_182);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_184, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_187 = lean_ctor_get(x_184, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_184, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_184, 4);
lean_inc(x_190);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 x_191 = x_184;
} else {
 lean_dec_ref(x_184);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_185, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_193 = x_185;
} else {
 lean_dec_ref(x_185);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(0, 1, 1);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set_uint8(x_194, sizeof(void*)*1, x_18);
if (lean_is_scalar(x_191)) {
 x_195 = lean_alloc_ctor(0, 5, 0);
} else {
 x_195 = x_191;
}
lean_ctor_set(x_195, 0, x_187);
lean_ctor_set(x_195, 1, x_188);
lean_ctor_set(x_195, 2, x_189);
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set(x_195, 4, x_190);
x_196 = lean_st_ref_set(x_9, x_195, x_186);
lean_dec(x_9);
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
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
 lean_ctor_set_tag(x_199, 1);
}
lean_ctor_set(x_199, 0, x_179);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_8, 3);
lean_inc(x_200);
x_201 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(x_9, x_13);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_204 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__2;
x_208 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_202, x_207, x_200, x_4, x_5, x_6, x_7, x_8, x_9, x_206);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_208, 0);
lean_dec(x_210);
lean_ctor_set(x_208, 0, x_205);
return x_208;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_205);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_213 = lean_ctor_get(x_204, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_204, 1);
lean_inc(x_214);
lean_dec(x_204);
x_215 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__2;
x_216 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_202, x_215, x_200, x_4, x_5, x_6, x_7, x_8, x_9, x_214);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_216, 0);
lean_dec(x_218);
lean_ctor_set_tag(x_216, 1);
lean_ctor_set(x_216, 0, x_213);
return x_216;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_213);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_tryResolve___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_tryResolve___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
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
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg), 9, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("skip answer containing metavariables ");
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
lean_inc(x_10);
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
lean_inc(x_10);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_inc(x_5);
x_43 = l_Lean_Meta_openAbstractMVarsResult(x_39, x_5, x_6, x_7, x_8, x_9);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_47 = x_43;
} else {
 lean_dec_ref(x_43);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_61 = lean_st_ref_get(x_8, x_46);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 3);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get_uint8(x_63, sizeof(void*)*1);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = 0;
x_50 = x_66;
x_51 = x_65;
goto block_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_50 = x_71;
x_51 = x_70;
goto block_60;
}
block_60:
{
if (x_50 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_48);
lean_dec(x_5);
x_52 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_47;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_47);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_48);
x_55 = l_Lean_Meta_SynthInstance_wakeUp___closed__2;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_49, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
lean_dec(x_5);
return x_59;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_5);
x_72 = lean_st_ref_get(x_8, x_9);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_st_ref_take(x_4, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_39);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_75, 0);
lean_dec(x_79);
lean_ctor_set(x_75, 0, x_77);
x_80 = lean_st_ref_set(x_4, x_75, x_76);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
x_83 = lean_box(0);
lean_ctor_set(x_80, 0, x_83);
return x_80;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_75, 1);
x_88 = lean_ctor_get(x_75, 2);
x_89 = lean_ctor_get(x_75, 3);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_75);
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_77);
lean_ctor_set(x_90, 1, x_87);
lean_ctor_set(x_90, 2, x_88);
lean_ctor_set(x_90, 3, x_89);
x_91 = lean_st_ref_set(x_4, x_90, x_76);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
}
}
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___spec__1___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_5);
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
x_1 = lean_mk_string("val: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("size: ");
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_39; lean_object* x_40; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_st_ref_get(x_7, x_8);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_ctor_get_uint8(x_65, sizeof(void*)*1);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = 0;
x_39 = x_68;
x_40 = x_67;
goto block_62;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
lean_inc(x_2);
x_70 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_2, x_4, x_5, x_6, x_7, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unbox(x_71);
lean_dec(x_71);
x_39 = x_73;
x_40 = x_72;
goto block_62;
}
block_38:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_inc(x_5);
x_10 = l_Lean_Meta_instantiateMVars(x_1, x_4, x_5, x_6, x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_27 = lean_st_ref_get(x_7, x_12);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 3);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get_uint8(x_29, sizeof(void*)*1);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = 0;
x_13 = x_32;
x_14 = x_31;
goto block_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
lean_inc(x_2);
x_34 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_2, x_4, x_5, x_6, x_7, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_13 = x_37;
x_14 = x_36;
goto block_26;
}
block_26:
{
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__1(x_11, x_3, x_15, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_11);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_11);
x_18 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_21, x_4, x_5, x_6, x_7, x_14);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__1(x_11, x_3, x_23, x_4, x_5, x_6, x_7, x_24);
lean_dec(x_23);
lean_dec(x_3);
return x_25;
}
}
}
block_62:
{
if (x_39 == 0)
{
x_9 = x_40;
goto block_38;
}
else
{
lean_object* x_41; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_41 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_3, 4);
lean_inc(x_44);
x_45 = l_Nat_repr(x_44);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__4;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__10;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_42);
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_2);
x_56 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_55, x_4, x_5, x_6, x_7, x_43);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_9 = x_57;
goto block_38;
}
else
{
uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_41);
if (x_58 == 0)
{
return x_41;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_41, 0);
x_60 = lean_ctor_get(x_41, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_41);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("newAnswer");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_2 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__2;
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2), 8, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_1);
x_11 = l_Lean_Meta_withMCtx___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___spec__1___rarg(x_7, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
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
lean_dec(x_14);
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
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ≥ ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_infer_type(x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Nat_repr(x_2);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = l_Nat_repr(x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__10;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_14);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_12, 0, x_32);
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_12);
x_35 = l_Nat_repr(x_2);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__4;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
lean_dec(x_3);
x_43 = l_Nat_repr(x_42);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__10;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_33);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_34);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_3);
lean_dec(x_2);
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
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("discarded");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_2 = l_Lean_Meta_SynthInstance_addAnswer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___closed__3() {
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
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = lean_nat_dec_le(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_12 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_15);
x_16 = l_Lean_Meta_SynthInstance_getEntry(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = l_Lean_Meta_SynthInstance_isNewAnswer(x_22, x_13);
if (x_23 == 0)
{
lean_object* x_24; 
lean_free_object(x_18);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_box(0);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_16);
lean_inc(x_13);
x_25 = lean_array_push(x_22, x_13);
lean_inc(x_21);
lean_ctor_set(x_18, 1, x_25);
x_26 = lean_st_ref_get(x_7, x_20);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_take(x_3, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_29, 3);
x_33 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_32, x_15, x_18);
lean_ctor_set(x_29, 3, x_33);
x_34 = lean_st_ref_set(x_3, x_29, x_30);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_array_get_size(x_21);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_lt(x_39, x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_box(0);
lean_ctor_set(x_34, 0, x_41);
return x_34;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_38, x_38);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_38);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_box(0);
lean_ctor_set(x_34, 0, x_43);
return x_34;
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_34);
x_44 = 0;
x_45 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_46 = lean_box(0);
x_47 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(x_13, x_21, x_44, x_45, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_21);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
lean_dec(x_34);
x_49 = lean_array_get_size(x_21);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_lt(x_50, x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_49);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_49, x_49);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_49);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_48);
return x_56;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_59 = lean_box(0);
x_60 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(x_13, x_21, x_57, x_58, x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_21);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_61 = lean_ctor_get(x_29, 0);
x_62 = lean_ctor_get(x_29, 1);
x_63 = lean_ctor_get(x_29, 2);
x_64 = lean_ctor_get(x_29, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_29);
x_65 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_64, x_15, x_18);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_63);
lean_ctor_set(x_66, 3, x_65);
x_67 = lean_st_ref_set(x_3, x_66, x_30);
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
x_70 = lean_array_get_size(x_21);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_lt(x_71, x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_70);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_68);
return x_74;
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_le(x_70, x_70);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_69;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_68);
return x_77;
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_69);
x_78 = 0;
x_79 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_80 = lean_box(0);
x_81 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(x_13, x_21, x_78, x_79, x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_21);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_16, 1);
x_83 = lean_ctor_get(x_18, 0);
x_84 = lean_ctor_get(x_18, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_18);
x_85 = l_Lean_Meta_SynthInstance_isNewAnswer(x_84, x_13);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_box(0);
lean_ctor_set(x_16, 0, x_86);
return x_16;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_free_object(x_16);
lean_inc(x_13);
x_87 = lean_array_push(x_84, x_13);
lean_inc(x_83);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_st_ref_get(x_7, x_82);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_st_ref_take(x_3, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 3);
lean_inc(x_97);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 lean_ctor_release(x_92, 3);
 x_98 = x_92;
} else {
 lean_dec_ref(x_92);
 x_98 = lean_box(0);
}
x_99 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_97, x_15, x_88);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 4, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_95);
lean_ctor_set(x_100, 2, x_96);
lean_ctor_set(x_100, 3, x_99);
x_101 = lean_st_ref_set(x_3, x_100, x_93);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_array_get_size(x_83);
x_105 = lean_unsigned_to_nat(0u);
x_106 = lean_nat_dec_lt(x_105, x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_104);
lean_dec(x_83);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_107 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_103;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_102);
return x_108;
}
else
{
uint8_t x_109; 
x_109 = lean_nat_dec_le(x_104, x_104);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_104);
lean_dec(x_83);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_103;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_102);
return x_111;
}
else
{
size_t x_112; size_t x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_103);
x_112 = 0;
x_113 = lean_usize_of_nat(x_104);
lean_dec(x_104);
x_114 = lean_box(0);
x_115 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(x_13, x_83, x_112, x_113, x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_102);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_83);
return x_115;
}
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_116 = lean_ctor_get(x_16, 0);
x_117 = lean_ctor_get(x_16, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_16);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_120 = x_116;
} else {
 lean_dec_ref(x_116);
 x_120 = lean_box(0);
}
x_121 = l_Lean_Meta_SynthInstance_isNewAnswer(x_119, x_13);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_117);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_inc(x_13);
x_124 = lean_array_push(x_119, x_13);
lean_inc(x_118);
if (lean_is_scalar(x_120)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_120;
}
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_st_ref_get(x_7, x_117);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_st_ref_take(x_3, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_129, 3);
lean_inc(x_134);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 x_135 = x_129;
} else {
 lean_dec_ref(x_129);
 x_135 = lean_box(0);
}
x_136 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_134, x_15, x_125);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 4, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_132);
lean_ctor_set(x_137, 2, x_133);
lean_ctor_set(x_137, 3, x_136);
x_138 = lean_st_ref_set(x_3, x_137, x_130);
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
x_141 = lean_array_get_size(x_118);
x_142 = lean_unsigned_to_nat(0u);
x_143 = lean_nat_dec_lt(x_142, x_141);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_141);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_144 = lean_box(0);
if (lean_is_scalar(x_140)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_140;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_139);
return x_145;
}
else
{
uint8_t x_146; 
x_146 = lean_nat_dec_le(x_141, x_141);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_141);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_147 = lean_box(0);
if (lean_is_scalar(x_140)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_140;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_139);
return x_148;
}
else
{
size_t x_149; size_t x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_140);
x_149 = 0;
x_150 = lean_usize_of_nat(x_141);
lean_dec(x_141);
x_151 = lean_box(0);
x_152 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_addAnswer___spec__2(x_13, x_118, x_149, x_150, x_151, x_2, x_3, x_4, x_5, x_6, x_7, x_139);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_118);
return x_152;
}
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_153 = !lean_is_exclusive(x_16);
if (x_153 == 0)
{
return x_16;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_16, 0);
x_155 = lean_ctor_get(x_16, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_16);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_12);
if (x_157 == 0)
{
return x_12;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_12, 0);
x_159 = lean_ctor_get(x_12, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_12);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_161 = lean_ctor_get(x_1, 2);
lean_inc(x_161);
x_162 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_addAnswer___lambda__1___boxed), 10, 2);
lean_closure_set(x_162, 0, x_1);
lean_closure_set(x_162, 1, x_10);
x_163 = l_Lean_Meta_SynthInstance_addAnswer___closed__3;
x_164 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg), 9, 2);
lean_closure_set(x_164, 0, x_163);
lean_closure_set(x_164, 1, x_162);
x_165 = lean_st_ref_get(x_7, x_8);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_166, 3);
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_ctor_get_uint8(x_167, sizeof(void*)*1);
lean_dec(x_167);
if (x_168 == 0)
{
uint8_t x_169; 
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_169 = !lean_is_exclusive(x_165);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_165, 0);
lean_dec(x_170);
x_171 = lean_box(0);
lean_ctor_set(x_165, 0, x_171);
return x_165;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_165, 1);
lean_inc(x_172);
lean_dec(x_165);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_175 = lean_ctor_get(x_165, 1);
lean_inc(x_175);
lean_dec(x_165);
x_176 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_177 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_176, x_2, x_3, x_4, x_5, x_6, x_7, x_175);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_unbox(x_178);
lean_dec(x_178);
if (x_179 == 0)
{
uint8_t x_180; 
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_177);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_177, 0);
lean_dec(x_181);
x_182 = lean_box(0);
lean_ctor_set(x_177, 0, x_182);
return x_177;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_177, 1);
lean_inc(x_183);
lean_dec(x_177);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_177, 1);
lean_inc(x_186);
lean_dec(x_177);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_187 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_161, x_164, x_2, x_3, x_4, x_5, x_6, x_7, x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_176, x_188, x_2, x_3, x_4, x_5, x_6, x_7, x_189);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_190, 0);
lean_dec(x_192);
x_193 = lean_box(0);
lean_ctor_set(x_190, 0, x_193);
return x_190;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
lean_dec(x_190);
x_195 = lean_box(0);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
else
{
uint8_t x_197; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_197 = !lean_is_exclusive(x_187);
if (x_197 == 0)
{
return x_187;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_187, 0);
x_199 = lean_ctor_get(x_187, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_187);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_addAnswer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_SynthInstance_addAnswer___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg___boxed), 9, 0);
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
x_1 = lean_mk_string("unusedArgs");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_2 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nhas unused arguments, reduced type");
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
x_1 = lean_mk_string("\nTransformer");
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
x_18 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__3___closed__1;
x_19 = lean_array_push(x_18, x_5);
x_20 = l_Lean_Meta_mkLambdaFVars(x_19, x_16, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__2;
x_45 = lean_st_ref_get(x_9, x_22);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_24 = x_12;
x_25 = x_49;
goto block_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_23, x_6, x_7, x_8, x_9, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_unbox(x_52);
lean_dec(x_52);
x_24 = x_54;
x_25 = x_53;
goto block_44;
}
block_44:
{
if (x_24 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
x_26 = lean_box(0);
x_27 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__1(x_3, x_21, x_26, x_6, x_7, x_8, x_9, x_25);
lean_dec(x_8);
lean_dec(x_6);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_4);
x_29 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_3);
x_33 = l_Lean_indentExpr(x_3);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__6;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_21);
x_37 = l_Lean_indentExpr(x_21);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_29);
x_40 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_23, x_39, x_6, x_7, x_8, x_9, x_25);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__1(x_3, x_21, x_41, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_41);
return x_43;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_20);
if (x_55 == 0)
{
return x_20;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_20, 0);
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_20);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_15);
if (x_59 == 0)
{
return x_15;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_15, 0);
x_61 = lean_ctor_get(x_15, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_15);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("redf");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
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
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_10);
if (x_33 == 0)
{
lean_dec(x_10);
x_12 = x_9;
x_13 = x_8;
goto block_31;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_35 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__3(x_3, x_2, x_34, x_35, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_12 = x_37;
x_13 = x_38;
goto block_31;
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
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
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_10);
if (x_44 == 0)
{
lean_dec(x_10);
x_12 = x_9;
x_13 = x_8;
goto block_31;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_46 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_47 = l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__4(x_3, x_2, x_45, x_46, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_12 = x_48;
x_13 = x_49;
goto block_31;
}
else
{
uint8_t x_50; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
block_31:
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
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
x_26 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_24, x_25, x_21, x_23, x_4, x_5, x_6, x_7, x_22);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
lean_inc(x_3);
x_10 = l_Lean_Meta_instantiateMVars(x_8, x_2, x_3, x_4, x_5, x_9);
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
x_9 = l_Lean_Meta_withMCtx___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___spec__1___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_instantiateMVars(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__3___closed__1;
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
x_20 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__1___boxed), 8, 1);
lean_closure_set(x_20, 0, x_19);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__2___boxed), 11, 3);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_18);
lean_closure_set(x_21, 2, x_15);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg), 9, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_23 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_1, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
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
lean_inc(x_13);
x_32 = l_Lean_Meta_SynthInstance_mkTableKey(x_13, x_30);
lean_inc(x_32);
x_33 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_1);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_ctor_set(x_24, 0, x_30);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_consume___lambda__1___boxed), 8, 1);
lean_closure_set(x_36, 0, x_24);
x_37 = l_Lean_Meta_SynthInstance_consume___closed__1;
x_38 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg), 9, 2);
lean_closure_set(x_38, 0, x_36);
lean_closure_set(x_38, 1, x_37);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_39 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_13, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
lean_inc(x_43);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_9);
lean_inc(x_42);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_12);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 4, x_14);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_Meta_SynthInstance_newSubgoal(x_42, x_32, x_43, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_41);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_32);
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
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_39);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
x_52 = lean_ctor_get(x_34, 0);
lean_inc(x_52);
lean_dec(x_34);
x_53 = lean_ctor_get(x_33, 1);
lean_inc(x_53);
lean_dec(x_33);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
x_57 = lean_array_get_size(x_56);
x_58 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_59 = 0;
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_56);
x_60 = l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1(x_13, x_31, x_58, x_59, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_53);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_st_ref_get(x_7, x_62);
lean_dec(x_7);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_take(x_3, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_66, 2);
x_70 = lean_ctor_get(x_66, 3);
x_71 = lean_array_get_size(x_61);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_lt(x_72, x_71);
x_74 = lean_array_push(x_55, x_16);
lean_ctor_set(x_52, 0, x_74);
x_75 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_70, x_32, x_52);
if (x_73 == 0)
{
lean_object* x_76; uint8_t x_77; 
lean_dec(x_71);
lean_dec(x_61);
lean_dec(x_1);
lean_ctor_set(x_66, 3, x_75);
x_76 = lean_st_ref_set(x_3, x_66, x_67);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
x_79 = lean_box(0);
lean_ctor_set(x_76, 0, x_79);
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_71, x_71);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_61);
lean_dec(x_1);
lean_ctor_set(x_66, 3, x_75);
x_84 = lean_st_ref_set(x_3, x_66, x_67);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
x_87 = lean_box(0);
lean_ctor_set(x_84, 0, x_87);
return x_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
size_t x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_92 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2(x_1, x_61, x_59, x_91, x_69);
lean_dec(x_61);
lean_ctor_set(x_66, 3, x_75);
lean_ctor_set(x_66, 2, x_92);
x_93 = lean_st_ref_set(x_3, x_66, x_67);
lean_dec(x_3);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
lean_dec(x_95);
x_96 = lean_box(0);
lean_ctor_set(x_93, 0, x_96);
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_100 = lean_ctor_get(x_66, 0);
x_101 = lean_ctor_get(x_66, 1);
x_102 = lean_ctor_get(x_66, 2);
x_103 = lean_ctor_get(x_66, 3);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_66);
x_104 = lean_array_get_size(x_61);
x_105 = lean_unsigned_to_nat(0u);
x_106 = lean_nat_dec_lt(x_105, x_104);
x_107 = lean_array_push(x_55, x_16);
lean_ctor_set(x_52, 0, x_107);
x_108 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_103, x_32, x_52);
if (x_106 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_104);
lean_dec(x_61);
lean_dec(x_1);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_100);
lean_ctor_set(x_109, 1, x_101);
lean_ctor_set(x_109, 2, x_102);
lean_ctor_set(x_109, 3, x_108);
x_110 = lean_st_ref_set(x_3, x_109, x_67);
lean_dec(x_3);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_113 = lean_box(0);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
else
{
uint8_t x_115; 
x_115 = lean_nat_dec_le(x_104, x_104);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_104);
lean_dec(x_61);
lean_dec(x_1);
x_116 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_116, 0, x_100);
lean_ctor_set(x_116, 1, x_101);
lean_ctor_set(x_116, 2, x_102);
lean_ctor_set(x_116, 3, x_108);
x_117 = lean_st_ref_set(x_3, x_116, x_67);
lean_dec(x_3);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
else
{
size_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_usize_of_nat(x_104);
lean_dec(x_104);
x_123 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2(x_1, x_61, x_59, x_122, x_102);
lean_dec(x_61);
x_124 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_124, 0, x_100);
lean_ctor_set(x_124, 1, x_101);
lean_ctor_set(x_124, 2, x_123);
lean_ctor_set(x_124, 3, x_108);
x_125 = lean_st_ref_set(x_3, x_124, x_67);
lean_dec(x_3);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
x_128 = lean_box(0);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
}
}
}
else
{
uint8_t x_130; 
lean_free_object(x_52);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_60);
if (x_130 == 0)
{
return x_60;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_60, 0);
x_132 = lean_ctor_get(x_60, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_60);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; size_t x_137; size_t x_138; lean_object* x_139; 
x_134 = lean_ctor_get(x_52, 0);
x_135 = lean_ctor_get(x_52, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_52);
x_136 = lean_array_get_size(x_135);
x_137 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_138 = 0;
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_135);
x_139 = l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1(x_13, x_31, x_137, x_138, x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_53);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_st_ref_get(x_7, x_141);
lean_dec(x_7);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_st_ref_take(x_3, x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_145, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_145, 3);
lean_inc(x_150);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 lean_ctor_release(x_145, 2);
 lean_ctor_release(x_145, 3);
 x_151 = x_145;
} else {
 lean_dec_ref(x_145);
 x_151 = lean_box(0);
}
x_152 = lean_array_get_size(x_140);
x_153 = lean_unsigned_to_nat(0u);
x_154 = lean_nat_dec_lt(x_153, x_152);
x_155 = lean_array_push(x_134, x_16);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_135);
x_157 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_150, x_32, x_156);
if (x_154 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_152);
lean_dec(x_140);
lean_dec(x_1);
if (lean_is_scalar(x_151)) {
 x_158 = lean_alloc_ctor(0, 4, 0);
} else {
 x_158 = x_151;
}
lean_ctor_set(x_158, 0, x_147);
lean_ctor_set(x_158, 1, x_148);
lean_ctor_set(x_158, 2, x_149);
lean_ctor_set(x_158, 3, x_157);
x_159 = lean_st_ref_set(x_3, x_158, x_146);
lean_dec(x_3);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
x_162 = lean_box(0);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
return x_163;
}
else
{
uint8_t x_164; 
x_164 = lean_nat_dec_le(x_152, x_152);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_152);
lean_dec(x_140);
lean_dec(x_1);
if (lean_is_scalar(x_151)) {
 x_165 = lean_alloc_ctor(0, 4, 0);
} else {
 x_165 = x_151;
}
lean_ctor_set(x_165, 0, x_147);
lean_ctor_set(x_165, 1, x_148);
lean_ctor_set(x_165, 2, x_149);
lean_ctor_set(x_165, 3, x_157);
x_166 = lean_st_ref_set(x_3, x_165, x_146);
lean_dec(x_3);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_168 = x_166;
} else {
 lean_dec_ref(x_166);
 x_168 = lean_box(0);
}
x_169 = lean_box(0);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
return x_170;
}
else
{
size_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_171 = lean_usize_of_nat(x_152);
lean_dec(x_152);
x_172 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2(x_1, x_140, x_138, x_171, x_149);
lean_dec(x_140);
if (lean_is_scalar(x_151)) {
 x_173 = lean_alloc_ctor(0, 4, 0);
} else {
 x_173 = x_151;
}
lean_ctor_set(x_173, 0, x_147);
lean_ctor_set(x_173, 1, x_148);
lean_ctor_set(x_173, 2, x_172);
lean_ctor_set(x_173, 3, x_157);
x_174 = lean_st_ref_set(x_3, x_173, x_146);
lean_dec(x_3);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
x_177 = lean_box(0);
if (lean_is_scalar(x_176)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_176;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_179 = lean_ctor_get(x_139, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_139, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_181 = x_139;
} else {
 lean_dec_ref(x_139);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_183 = lean_ctor_get(x_24, 0);
lean_inc(x_183);
lean_dec(x_24);
x_184 = lean_ctor_get(x_23, 1);
lean_inc(x_184);
lean_dec(x_23);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
lean_inc(x_185);
lean_inc(x_13);
x_187 = l_Lean_Meta_SynthInstance_mkTableKey(x_13, x_185);
lean_inc(x_187);
x_188 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_187, x_2, x_3, x_4, x_5, x_6, x_7, x_184);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_186);
lean_dec(x_16);
lean_dec(x_1);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_185);
x_192 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_consume___lambda__1___boxed), 8, 1);
lean_closure_set(x_192, 0, x_191);
x_193 = l_Lean_Meta_SynthInstance_consume___closed__1;
x_194 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg), 9, 2);
lean_closure_set(x_194, 0, x_192);
lean_closure_set(x_194, 1, x_193);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_195 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_13, x_194, x_2, x_3, x_4, x_5, x_6, x_7, x_190);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
lean_inc(x_199);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_9);
lean_inc(x_198);
x_201 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_201, 0, x_11);
lean_ctor_set(x_201, 1, x_12);
lean_ctor_set(x_201, 2, x_198);
lean_ctor_set(x_201, 3, x_200);
lean_ctor_set(x_201, 4, x_14);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_203 = l_Lean_Meta_SynthInstance_newSubgoal(x_198, x_187, x_199, x_202, x_2, x_3, x_4, x_5, x_6, x_7, x_197);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_187);
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
x_204 = lean_ctor_get(x_195, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_195, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_206 = x_195;
} else {
 lean_dec_ref(x_195);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; size_t x_214; size_t x_215; lean_object* x_216; 
lean_dec(x_185);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
x_208 = lean_ctor_get(x_189, 0);
lean_inc(x_208);
lean_dec(x_189);
x_209 = lean_ctor_get(x_188, 1);
lean_inc(x_209);
lean_dec(x_188);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_212 = x_208;
} else {
 lean_dec_ref(x_208);
 x_212 = lean_box(0);
}
x_213 = lean_array_get_size(x_211);
x_214 = lean_usize_of_nat(x_213);
lean_dec(x_213);
x_215 = 0;
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_211);
x_216 = l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1(x_13, x_186, x_214, x_215, x_211, x_2, x_3, x_4, x_5, x_6, x_7, x_209);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_st_ref_get(x_7, x_218);
lean_dec(x_7);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = lean_st_ref_take(x_3, x_220);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_222, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_222, 3);
lean_inc(x_227);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 lean_ctor_release(x_222, 2);
 lean_ctor_release(x_222, 3);
 x_228 = x_222;
} else {
 lean_dec_ref(x_222);
 x_228 = lean_box(0);
}
x_229 = lean_array_get_size(x_217);
x_230 = lean_unsigned_to_nat(0u);
x_231 = lean_nat_dec_lt(x_230, x_229);
x_232 = lean_array_push(x_210, x_16);
if (lean_is_scalar(x_212)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_212;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_211);
x_234 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_227, x_187, x_233);
if (x_231 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_229);
lean_dec(x_217);
lean_dec(x_1);
if (lean_is_scalar(x_228)) {
 x_235 = lean_alloc_ctor(0, 4, 0);
} else {
 x_235 = x_228;
}
lean_ctor_set(x_235, 0, x_224);
lean_ctor_set(x_235, 1, x_225);
lean_ctor_set(x_235, 2, x_226);
lean_ctor_set(x_235, 3, x_234);
x_236 = lean_st_ref_set(x_3, x_235, x_223);
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
x_239 = lean_box(0);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
return x_240;
}
else
{
uint8_t x_241; 
x_241 = lean_nat_dec_le(x_229, x_229);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_229);
lean_dec(x_217);
lean_dec(x_1);
if (lean_is_scalar(x_228)) {
 x_242 = lean_alloc_ctor(0, 4, 0);
} else {
 x_242 = x_228;
}
lean_ctor_set(x_242, 0, x_224);
lean_ctor_set(x_242, 1, x_225);
lean_ctor_set(x_242, 2, x_226);
lean_ctor_set(x_242, 3, x_234);
x_243 = lean_st_ref_set(x_3, x_242, x_223);
lean_dec(x_3);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
x_246 = lean_box(0);
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
return x_247;
}
else
{
size_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_248 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_249 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__2(x_1, x_217, x_215, x_248, x_226);
lean_dec(x_217);
if (lean_is_scalar(x_228)) {
 x_250 = lean_alloc_ctor(0, 4, 0);
} else {
 x_250 = x_228;
}
lean_ctor_set(x_250, 0, x_224);
lean_ctor_set(x_250, 1, x_225);
lean_ctor_set(x_250, 2, x_249);
lean_ctor_set(x_250, 3, x_234);
x_251 = lean_st_ref_set(x_3, x_250, x_223);
lean_dec(x_3);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_253 = x_251;
} else {
 lean_dec_ref(x_251);
 x_253 = lean_box(0);
}
x_254 = lean_box(0);
if (lean_is_scalar(x_253)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_253;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_252);
return x_255;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_187);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_256 = lean_ctor_get(x_216, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_216, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_258 = x_216;
} else {
 lean_dec_ref(x_216);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
}
}
else
{
uint8_t x_260; 
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
x_260 = !lean_is_exclusive(x_23);
if (x_260 == 0)
{
return x_23;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_23, 0);
x_262 = lean_ctor_get(x_23, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_23);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
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
x_264 = lean_ctor_get(x_20, 1);
lean_inc(x_264);
lean_dec(x_20);
x_265 = lean_ctor_get(x_21, 0);
lean_inc(x_265);
lean_dec(x_21);
x_266 = lean_st_ref_get(x_7, x_264);
lean_dec(x_7);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = lean_st_ref_take(x_3, x_267);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = !lean_is_exclusive(x_269);
if (x_271 == 0)
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_265);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; 
x_273 = lean_ctor_get(x_269, 2);
x_274 = lean_ctor_get(x_269, 3);
x_275 = lean_ctor_get(x_265, 0);
x_276 = lean_ctor_get(x_265, 1);
x_277 = lean_array_get_size(x_276);
x_278 = lean_unsigned_to_nat(0u);
x_279 = lean_nat_dec_lt(x_278, x_277);
x_280 = lean_array_push(x_275, x_16);
lean_inc(x_276);
lean_ctor_set(x_265, 0, x_280);
x_281 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_274, x_18, x_265);
if (x_279 == 0)
{
lean_object* x_282; uint8_t x_283; 
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_1);
lean_ctor_set(x_269, 3, x_281);
x_282 = lean_st_ref_set(x_3, x_269, x_270);
lean_dec(x_3);
x_283 = !lean_is_exclusive(x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_282, 0);
lean_dec(x_284);
x_285 = lean_box(0);
lean_ctor_set(x_282, 0, x_285);
return x_282;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_282, 1);
lean_inc(x_286);
lean_dec(x_282);
x_287 = lean_box(0);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
else
{
uint8_t x_289; 
x_289 = lean_nat_dec_le(x_277, x_277);
if (x_289 == 0)
{
lean_object* x_290; uint8_t x_291; 
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_1);
lean_ctor_set(x_269, 3, x_281);
x_290 = lean_st_ref_set(x_3, x_269, x_270);
lean_dec(x_3);
x_291 = !lean_is_exclusive(x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_290, 0);
lean_dec(x_292);
x_293 = lean_box(0);
lean_ctor_set(x_290, 0, x_293);
return x_290;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_290, 1);
lean_inc(x_294);
lean_dec(x_290);
x_295 = lean_box(0);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
else
{
size_t x_297; size_t x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_297 = 0;
x_298 = lean_usize_of_nat(x_277);
lean_dec(x_277);
x_299 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3(x_1, x_276, x_297, x_298, x_273);
lean_dec(x_276);
lean_ctor_set(x_269, 3, x_281);
lean_ctor_set(x_269, 2, x_299);
x_300 = lean_st_ref_set(x_3, x_269, x_270);
lean_dec(x_3);
x_301 = !lean_is_exclusive(x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_300, 0);
lean_dec(x_302);
x_303 = lean_box(0);
lean_ctor_set(x_300, 0, x_303);
return x_300;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_300, 1);
lean_inc(x_304);
lean_dec(x_300);
x_305 = lean_box(0);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_307 = lean_ctor_get(x_269, 2);
x_308 = lean_ctor_get(x_269, 3);
x_309 = lean_ctor_get(x_265, 0);
x_310 = lean_ctor_get(x_265, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_265);
x_311 = lean_array_get_size(x_310);
x_312 = lean_unsigned_to_nat(0u);
x_313 = lean_nat_dec_lt(x_312, x_311);
x_314 = lean_array_push(x_309, x_16);
lean_inc(x_310);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_310);
x_316 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_308, x_18, x_315);
if (x_313 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_1);
lean_ctor_set(x_269, 3, x_316);
x_317 = lean_st_ref_set(x_3, x_269, x_270);
lean_dec(x_3);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_319 = x_317;
} else {
 lean_dec_ref(x_317);
 x_319 = lean_box(0);
}
x_320 = lean_box(0);
if (lean_is_scalar(x_319)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_319;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_318);
return x_321;
}
else
{
uint8_t x_322; 
x_322 = lean_nat_dec_le(x_311, x_311);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_1);
lean_ctor_set(x_269, 3, x_316);
x_323 = lean_st_ref_set(x_3, x_269, x_270);
lean_dec(x_3);
x_324 = lean_ctor_get(x_323, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_325 = x_323;
} else {
 lean_dec_ref(x_323);
 x_325 = lean_box(0);
}
x_326 = lean_box(0);
if (lean_is_scalar(x_325)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_325;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_324);
return x_327;
}
else
{
size_t x_328; size_t x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_328 = 0;
x_329 = lean_usize_of_nat(x_311);
lean_dec(x_311);
x_330 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3(x_1, x_310, x_328, x_329, x_307);
lean_dec(x_310);
lean_ctor_set(x_269, 3, x_316);
lean_ctor_set(x_269, 2, x_330);
x_331 = lean_st_ref_set(x_3, x_269, x_270);
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
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_336 = lean_ctor_get(x_269, 0);
x_337 = lean_ctor_get(x_269, 1);
x_338 = lean_ctor_get(x_269, 2);
x_339 = lean_ctor_get(x_269, 3);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_269);
x_340 = lean_ctor_get(x_265, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_265, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_342 = x_265;
} else {
 lean_dec_ref(x_265);
 x_342 = lean_box(0);
}
x_343 = lean_array_get_size(x_341);
x_344 = lean_unsigned_to_nat(0u);
x_345 = lean_nat_dec_lt(x_344, x_343);
x_346 = lean_array_push(x_340, x_16);
lean_inc(x_341);
if (lean_is_scalar(x_342)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_342;
}
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_341);
x_348 = l_Std_HashMap_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_339, x_18, x_347);
if (x_345 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_1);
x_349 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_349, 0, x_336);
lean_ctor_set(x_349, 1, x_337);
lean_ctor_set(x_349, 2, x_338);
lean_ctor_set(x_349, 3, x_348);
x_350 = lean_st_ref_set(x_3, x_349, x_270);
lean_dec(x_3);
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_352 = x_350;
} else {
 lean_dec_ref(x_350);
 x_352 = lean_box(0);
}
x_353 = lean_box(0);
if (lean_is_scalar(x_352)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_352;
}
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_351);
return x_354;
}
else
{
uint8_t x_355; 
x_355 = lean_nat_dec_le(x_343, x_343);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_1);
x_356 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_356, 0, x_336);
lean_ctor_set(x_356, 1, x_337);
lean_ctor_set(x_356, 2, x_338);
lean_ctor_set(x_356, 3, x_348);
x_357 = lean_st_ref_set(x_3, x_356, x_270);
lean_dec(x_3);
x_358 = lean_ctor_get(x_357, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_359 = x_357;
} else {
 lean_dec_ref(x_357);
 x_359 = lean_box(0);
}
x_360 = lean_box(0);
if (lean_is_scalar(x_359)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_359;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_358);
return x_361;
}
else
{
size_t x_362; size_t x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_362 = 0;
x_363 = lean_usize_of_nat(x_343);
lean_dec(x_343);
x_364 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_consume___spec__3(x_1, x_341, x_362, x_363, x_338);
lean_dec(x_341);
x_365 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_365, 0, x_336);
lean_ctor_set(x_365, 1, x_337);
lean_ctor_set(x_365, 2, x_364);
lean_ctor_set(x_365, 3, x_348);
x_366 = lean_st_ref_set(x_3, x_365, x_270);
lean_dec(x_3);
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_368 = x_366;
} else {
 lean_dec_ref(x_366);
 x_368 = lean_box(0);
}
x_369 = lean_box(0);
if (lean_is_scalar(x_368)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_368;
}
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_367);
return x_370;
}
}
}
}
}
else
{
uint8_t x_371; 
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
x_371 = !lean_is_exclusive(x_17);
if (x_371 == 0)
{
return x_17;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_17, 0);
x_373 = lean_ctor_get(x_17, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_17);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapMUnsafe_map___at_Lean_Meta_SynthInstance_consume___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_st_ref_get(x_12, x_13);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_take(x_8, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_array_get_size(x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_42, x_43);
x_45 = lean_nat_dec_lt(x_44, x_42);
lean_dec(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_44);
lean_dec(x_5);
x_46 = lean_st_ref_set(x_8, x_38, x_39);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_14 = x_47;
goto block_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_array_fget(x_41, x_44);
x_49 = lean_box(0);
x_50 = lean_array_fset(x_41, x_44, x_49);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 4);
lean_dec(x_52);
lean_ctor_set(x_48, 4, x_5);
x_53 = lean_array_fset(x_50, x_44, x_48);
lean_dec(x_44);
lean_ctor_set(x_38, 1, x_53);
x_54 = lean_st_ref_set(x_8, x_38, x_39);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_14 = x_55;
goto block_34;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
x_58 = lean_ctor_get(x_48, 2);
x_59 = lean_ctor_get(x_48, 3);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set(x_60, 4, x_5);
x_61 = lean_array_fset(x_50, x_44, x_60);
lean_dec(x_44);
lean_ctor_set(x_38, 1, x_61);
x_62 = lean_st_ref_set(x_8, x_38, x_39);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_14 = x_63;
goto block_34;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_38, 0);
x_65 = lean_ctor_get(x_38, 1);
x_66 = lean_ctor_get(x_38, 2);
x_67 = lean_ctor_get(x_38, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_38);
x_68 = lean_array_get_size(x_65);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_sub(x_68, x_69);
x_71 = lean_nat_dec_lt(x_70, x_68);
lean_dec(x_68);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_70);
lean_dec(x_5);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_64);
lean_ctor_set(x_72, 1, x_65);
lean_ctor_set(x_72, 2, x_66);
lean_ctor_set(x_72, 3, x_67);
x_73 = lean_st_ref_set(x_8, x_72, x_39);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_14 = x_74;
goto block_34;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_75 = lean_array_fget(x_65, x_70);
x_76 = lean_box(0);
x_77 = lean_array_fset(x_65, x_70, x_76);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 3);
lean_inc(x_81);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 x_82 = x_75;
} else {
 lean_dec_ref(x_75);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 5, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_81);
lean_ctor_set(x_83, 4, x_5);
x_84 = lean_array_fset(x_77, x_70, x_83);
lean_dec(x_70);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_64);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_66);
lean_ctor_set(x_85, 3, x_67);
x_86 = lean_st_ref_set(x_8, x_85, x_39);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_14 = x_87;
goto block_34;
}
}
block_34:
{
lean_object* x_15; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_15 = l_Lean_Meta_SynthInstance_tryResolve(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_4);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set(x_28, 4, x_27);
x_29 = l_Lean_Meta_SynthInstance_consume(x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("generate");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_2 = l_Lean_Meta_SynthInstance_generate___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instance ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_generate___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_array_get(x_20, x_14, x_19);
lean_dec(x_14);
x_22 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_37 = lean_st_ref_get(x_6, x_10);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = 0;
x_23 = x_42;
x_24 = x_41;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_22, x_1, x_2, x_3, x_4, x_5, x_6, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unbox(x_45);
lean_dec(x_45);
x_23 = x_47;
x_24 = x_46;
goto block_36;
}
block_36:
{
if (x_23 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Meta_SynthInstance_generate___lambda__1(x_13, x_11, x_21, x_12, x_19, x_25, x_1, x_2, x_3, x_4, x_5, x_6, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_21);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_21);
x_28 = l_Lean_Meta_SynthInstance_generate___closed__4;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_22, x_31, x_1, x_2, x_3, x_4, x_5, x_6, x_24);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_SynthInstance_generate___lambda__1(x_13, x_11, x_21, x_12, x_19, x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_34);
lean_dec(x_33);
return x_35;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = lean_st_ref_get(x_6, x_10);
lean_dec(x_6);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_st_ref_take(x_2, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_array_pop(x_54);
lean_ctor_set(x_51, 1, x_55);
x_56 = lean_st_ref_set(x_2, x_51, x_52);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_51, 0);
x_64 = lean_ctor_get(x_51, 1);
x_65 = lean_ctor_get(x_51, 2);
x_66 = lean_ctor_get(x_51, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_51);
x_67 = lean_array_pop(x_64);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_65);
lean_ctor_set(x_68, 3, x_66);
x_69 = lean_st_ref_set(x_2, x_68, x_52);
lean_dec(x_2);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_SynthInstance_generate___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
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
x_1 = lean_mk_string(" <== ");
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
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_6 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = lean_infer_type(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = lean_infer_type(x_2, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_nat_add(x_4, x_22);
x_24 = l_Nat_repr(x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___lambda__2___closed__4;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__10;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_17);
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Meta_SynthInstance_resume___lambda__1___closed__2;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_20);
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_5, x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_19);
if (x_40 == 0)
{
return x_19;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_19, 0);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_19);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
return x_16;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.SynthInstance.resume");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resume found no remaining subgoals");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__1;
x_2 = l_Lean_Meta_SynthInstance_resume___closed__1;
x_3 = lean_unsigned_to_nat(541u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Meta_SynthInstance_resume___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resume");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_2 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_newSubgoal___lambda__2), 9, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_newSubgoal___closed__3;
x_2 = l_Lean_Meta_SynthInstance_resume___closed__6;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg), 9, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
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
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 2);
x_21 = lean_ctor_get(x_10, 4);
x_22 = lean_ctor_get(x_10, 3);
lean_dec(x_22);
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_16);
lean_inc(x_23);
x_25 = l_Lean_Meta_SynthInstance_tryAnswer(x_20, x_23, x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_10);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = l_Lean_Meta_SynthInstance_resume___closed__5;
lean_inc(x_21);
lean_inc(x_16);
lean_inc(x_18);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lambda__1___boxed), 13, 5);
lean_closure_set(x_36, 0, x_18);
lean_closure_set(x_36, 1, x_23);
lean_closure_set(x_36, 2, x_16);
lean_closure_set(x_36, 3, x_21);
lean_closure_set(x_36, 4, x_35);
x_37 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_38 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg), 9, 2);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, x_36);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_34);
x_39 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_34, x_38, x_1, x_2, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_16, 2);
lean_inc(x_41);
lean_dec(x_16);
x_42 = lean_nat_add(x_21, x_41);
lean_dec(x_41);
lean_dec(x_21);
lean_ctor_set(x_10, 4, x_42);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_34);
x_43 = l_Lean_Meta_SynthInstance_consume(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_40);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_24);
lean_free_object(x_10);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
uint8_t x_48; 
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_10);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_25);
if (x_48 == 0)
{
return x_25;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_25, 0);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_25);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_10, 0);
x_53 = lean_ctor_get(x_10, 1);
x_54 = lean_ctor_get(x_10, 2);
x_55 = lean_ctor_get(x_10, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_10);
x_56 = lean_ctor_get(x_11, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_16);
lean_inc(x_56);
x_58 = l_Lean_Meta_SynthInstance_tryAnswer(x_54, x_56, x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = l_Lean_Meta_SynthInstance_resume___closed__5;
lean_inc(x_55);
lean_inc(x_16);
lean_inc(x_52);
x_67 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lambda__1___boxed), 13, 5);
lean_closure_set(x_67, 0, x_52);
lean_closure_set(x_67, 1, x_56);
lean_closure_set(x_67, 2, x_16);
lean_closure_set(x_67, 3, x_55);
lean_closure_set(x_67, 4, x_66);
x_68 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_69 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___rarg), 9, 2);
lean_closure_set(x_69, 0, x_68);
lean_closure_set(x_69, 1, x_67);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_65);
x_70 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(x_65, x_69, x_1, x_2, x_3, x_4, x_5, x_6, x_64);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get(x_16, 2);
lean_inc(x_72);
lean_dec(x_16);
x_73 = lean_nat_add(x_55, x_72);
lean_dec(x_72);
lean_dec(x_55);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_52);
lean_ctor_set(x_74, 1, x_53);
lean_ctor_set(x_74, 2, x_65);
lean_ctor_set(x_74, 3, x_57);
lean_ctor_set(x_74, 4, x_73);
x_75 = l_Lean_Meta_SynthInstance_consume(x_74, x_1, x_2, x_3, x_4, x_5, x_6, x_71);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_78 = x_70;
} else {
 lean_dec_ref(x_70);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_ctor_get(x_58, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_58, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_82 = x_58;
} else {
 lean_dec_ref(x_58);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Meta_SynthInstance_resume___lambda__1(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
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
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_synth___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_synth___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_24 = lean_st_ref_get(x_6, x_11);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*1);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = 0;
x_13 = x_29;
x_14 = x_28;
goto block_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unbox(x_32);
lean_dec(x_32);
x_13 = x_34;
x_14 = x_33;
goto block_23;
}
block_23:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_SynthInstance_synth___closed__1;
if (x_13 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_apply_8(x_15, x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lean_Meta_SynthInstance_synth___closed__3;
x_19 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_12, x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_apply_8(x_15, x_20, x_1, x_2, x_3, x_4, x_5, x_6, x_21);
return x_22;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_dec(x_8);
x_36 = l_Lean_Meta_SynthInstance_getResult___rarg(x_2, x_3, x_4, x_5, x_6, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_7 = x_38;
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_36, 0, x_44);
return x_36;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_47 = x_37;
} else {
 lean_dec_ref(x_37);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
return x_8;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_8, 0);
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_8);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_synth___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_synth___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_SynthInstance_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
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
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_Lean_Meta_SynthInstance_main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_1 = lean_mk_string("failed to synthesize");
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
x_1 = lean_mk_string("\n");
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
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_3);
lean_inc(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = 0;
x_11 = lean_box(0);
lean_inc(x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_9, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_7, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_5, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_1);
lean_inc(x_21);
x_22 = l_Lean_Meta_SynthInstance_mkTableKey(x_21, x_1);
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = l_Lean_Meta_SynthInstance_getMaxHeartbeats(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_st_ref_get(x_7, x_19);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__5;
x_44 = lean_st_mk_ref(x_43, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_45);
lean_inc(x_40);
x_48 = l_Lean_Meta_SynthInstance_newSubgoal(x_21, x_22, x_13, x_47, x_40, x_45, x_4, x_5, x_6, x_7, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_45);
x_50 = l_Lean_Meta_SynthInstance_synth(x_40, x_45, x_4, x_5, x_6, x_7, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_get(x_7, x_52);
lean_dec(x_7);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_get(x_45, x_54);
lean_dec(x_45);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_51);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_45);
x_60 = lean_ctor_get(x_50, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_50, 1);
lean_inc(x_61);
lean_dec(x_50);
x_23 = x_60;
x_24 = x_61;
goto block_37;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_45);
lean_dec(x_40);
x_62 = lean_ctor_get(x_48, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
lean_dec(x_48);
x_23 = x_62;
x_24 = x_63;
goto block_37;
}
block_37:
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isMaxHeartbeat(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_20)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_20;
 lean_ctor_set_tag(x_26, 1);
}
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_20);
x_27 = l_Lean_indentExpr(x_1);
x_28 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__2;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__4;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Exception_toMessageData(x_23);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Meta_SynthInstance_main___spec__1(x_35, x_4, x_5, x_6, x_7, x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("main goal ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_main___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_23; lean_object* x_24; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_402 = lean_st_ref_get(x_8, x_9);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_403, 3);
lean_inc(x_404);
lean_dec(x_403);
x_405 = lean_ctor_get_uint8(x_404, sizeof(void*)*1);
lean_dec(x_404);
if (x_405 == 0)
{
lean_object* x_406; uint8_t x_407; 
x_406 = lean_ctor_get(x_402, 1);
lean_inc(x_406);
lean_dec(x_402);
x_407 = 0;
x_23 = x_407;
x_24 = x_406;
goto block_401;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_408 = lean_ctor_get(x_402, 1);
lean_inc(x_408);
lean_dec(x_402);
lean_inc(x_4);
x_409 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_4, x_5, x_6, x_7, x_8, x_408);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_unbox(x_410);
lean_dec(x_410);
x_23 = x_412;
x_24 = x_411;
goto block_401;
}
block_22:
{
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
block_401:
{
if (x_23 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_4);
x_25 = lean_st_ref_get(x_8, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get_uint8(x_27, sizeof(void*)*1);
lean_dec(x_27);
x_30 = lean_st_ref_take(x_8, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 3);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_86; lean_object* x_87; uint8_t x_121; lean_object* x_122; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_37 = 0;
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_37);
x_38 = lean_st_ref_set(x_8, x_31, x_33);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_143 = lean_st_ref_get(x_8, x_39);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_144, 3);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_ctor_get_uint8(x_145, sizeof(void*)*1);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_dec(x_143);
x_121 = x_37;
x_122 = x_147;
goto block_142;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
lean_dec(x_143);
lean_inc(x_3);
x_149 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_3, x_5, x_6, x_7, x_8, x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_unbox(x_150);
lean_dec(x_150);
x_121 = x_152;
x_122 = x_151;
goto block_142;
}
block_85:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_42 = lean_st_ref_get(x_8, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 3);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
x_47 = lean_st_ref_take(x_8, x_44);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_48, 3);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_29);
x_54 = lean_st_ref_set(x_8, x_48, x_50);
lean_dec(x_8);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_box(x_46);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_40);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_54, 0, x_58);
x_10 = x_54;
goto block_22;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_box(x_46);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_40);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
x_10 = x_62;
goto block_22;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_49, 0);
lean_inc(x_63);
lean_dec(x_49);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_29);
lean_ctor_set(x_48, 3, x_64);
x_65 = lean_st_ref_set(x_8, x_48, x_50);
lean_dec(x_8);
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
x_68 = lean_box(x_46);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_40);
lean_ctor_set(x_69, 1, x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
x_10 = x_70;
goto block_22;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
x_73 = lean_ctor_get(x_48, 2);
x_74 = lean_ctor_get(x_48, 4);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_75 = lean_ctor_get(x_49, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_76 = x_49;
} else {
 lean_dec_ref(x_49);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 1, 1);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_29);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set(x_78, 2, x_73);
lean_ctor_set(x_78, 3, x_77);
lean_ctor_set(x_78, 4, x_74);
x_79 = lean_st_ref_set(x_8, x_78, x_50);
lean_dec(x_8);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_box(x_46);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_40);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
x_10 = x_84;
goto block_22;
}
}
block_120:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_88 = lean_st_ref_get(x_8, x_87);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_st_ref_take(x_8, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_91, 3);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_92);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_29);
x_97 = lean_st_ref_set(x_8, x_91, x_93);
lean_dec(x_8);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_97, 0);
lean_dec(x_99);
lean_ctor_set_tag(x_97, 1);
lean_ctor_set(x_97, 0, x_86);
x_10 = x_97;
goto block_22;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_86);
lean_ctor_set(x_101, 1, x_100);
x_10 = x_101;
goto block_22;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_92, 0);
lean_inc(x_102);
lean_dec(x_92);
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_29);
lean_ctor_set(x_91, 3, x_103);
x_104 = lean_st_ref_set(x_8, x_91, x_93);
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
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
 lean_ctor_set_tag(x_107, 1);
}
lean_ctor_set(x_107, 0, x_86);
lean_ctor_set(x_107, 1, x_105);
x_10 = x_107;
goto block_22;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_108 = lean_ctor_get(x_91, 0);
x_109 = lean_ctor_get(x_91, 1);
x_110 = lean_ctor_get(x_91, 2);
x_111 = lean_ctor_get(x_91, 4);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_91);
x_112 = lean_ctor_get(x_92, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_113 = x_92;
} else {
 lean_dec_ref(x_92);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 1, 1);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_29);
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_109);
lean_ctor_set(x_115, 2, x_110);
lean_ctor_set(x_115, 3, x_114);
lean_ctor_set(x_115, 4, x_111);
x_116 = lean_st_ref_set(x_8, x_115, x_93);
lean_dec(x_8);
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
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
 lean_ctor_set_tag(x_119, 1);
}
lean_ctor_set(x_119, 0, x_86);
lean_ctor_set(x_119, 1, x_117);
x_10 = x_119;
goto block_22;
}
}
block_142:
{
if (x_121 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_3);
x_123 = lean_box(0);
lean_inc(x_8);
x_124 = l_Lean_Meta_SynthInstance_main___lambda__1(x_1, x_2, x_123, x_5, x_6, x_7, x_8, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_40 = x_125;
x_41 = x_126;
goto block_85;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
lean_dec(x_124);
x_86 = x_127;
x_87 = x_128;
goto block_120;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_inc(x_1);
x_129 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_129, 0, x_1);
x_130 = l_Lean_Meta_SynthInstance_main___lambda__2___closed__2;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_133, x_5, x_6, x_7, x_8, x_122);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
lean_inc(x_8);
x_137 = l_Lean_Meta_SynthInstance_main___lambda__1(x_1, x_2, x_135, x_5, x_6, x_7, x_8, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_40 = x_138;
x_41 = x_139;
goto block_85;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_137, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_dec(x_137);
x_86 = x_140;
x_87 = x_141;
goto block_120;
}
}
}
}
else
{
lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_185; lean_object* x_186; uint8_t x_207; lean_object* x_208; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_153 = lean_ctor_get(x_32, 0);
lean_inc(x_153);
lean_dec(x_32);
x_154 = 0;
x_155 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_154);
lean_ctor_set(x_31, 3, x_155);
x_156 = lean_st_ref_set(x_8, x_31, x_33);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_229 = lean_st_ref_get(x_8, x_157);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_230, 3);
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_ctor_get_uint8(x_231, sizeof(void*)*1);
lean_dec(x_231);
if (x_232 == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_229, 1);
lean_inc(x_233);
lean_dec(x_229);
x_207 = x_154;
x_208 = x_233;
goto block_228;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_234 = lean_ctor_get(x_229, 1);
lean_inc(x_234);
lean_dec(x_229);
lean_inc(x_3);
x_235 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_3, x_5, x_6, x_7, x_8, x_234);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = lean_unbox(x_236);
lean_dec(x_236);
x_207 = x_238;
x_208 = x_237;
goto block_228;
}
block_184:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_160 = lean_st_ref_get(x_8, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 3);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get_uint8(x_163, sizeof(void*)*1);
lean_dec(x_163);
x_165 = lean_st_ref_take(x_8, x_162);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_166, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_169 = lean_ctor_get(x_166, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_166, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_166, 4);
lean_inc(x_172);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 lean_ctor_release(x_166, 4);
 x_173 = x_166;
} else {
 lean_dec_ref(x_166);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_167, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_175 = x_167;
} else {
 lean_dec_ref(x_167);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 1, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_29);
if (lean_is_scalar(x_173)) {
 x_177 = lean_alloc_ctor(0, 5, 0);
} else {
 x_177 = x_173;
}
lean_ctor_set(x_177, 0, x_169);
lean_ctor_set(x_177, 1, x_170);
lean_ctor_set(x_177, 2, x_171);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set(x_177, 4, x_172);
x_178 = lean_st_ref_set(x_8, x_177, x_168);
lean_dec(x_8);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_180 = x_178;
} else {
 lean_dec_ref(x_178);
 x_180 = lean_box(0);
}
x_181 = lean_box(x_164);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_158);
lean_ctor_set(x_182, 1, x_181);
if (lean_is_scalar(x_180)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_180;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_179);
x_10 = x_183;
goto block_22;
}
block_206:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_187 = lean_st_ref_get(x_8, x_186);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_189 = lean_st_ref_take(x_8, x_188);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_190, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec(x_189);
x_193 = lean_ctor_get(x_190, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_190, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_190, 4);
lean_inc(x_196);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 lean_ctor_release(x_190, 2);
 lean_ctor_release(x_190, 3);
 lean_ctor_release(x_190, 4);
 x_197 = x_190;
} else {
 lean_dec_ref(x_190);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_191, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 x_199 = x_191;
} else {
 lean_dec_ref(x_191);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 1, 1);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_29);
if (lean_is_scalar(x_197)) {
 x_201 = lean_alloc_ctor(0, 5, 0);
} else {
 x_201 = x_197;
}
lean_ctor_set(x_201, 0, x_193);
lean_ctor_set(x_201, 1, x_194);
lean_ctor_set(x_201, 2, x_195);
lean_ctor_set(x_201, 3, x_200);
lean_ctor_set(x_201, 4, x_196);
x_202 = lean_st_ref_set(x_8, x_201, x_192);
lean_dec(x_8);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_204 = x_202;
} else {
 lean_dec_ref(x_202);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
 lean_ctor_set_tag(x_205, 1);
}
lean_ctor_set(x_205, 0, x_185);
lean_ctor_set(x_205, 1, x_203);
x_10 = x_205;
goto block_22;
}
block_228:
{
if (x_207 == 0)
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_3);
x_209 = lean_box(0);
lean_inc(x_8);
x_210 = l_Lean_Meta_SynthInstance_main___lambda__1(x_1, x_2, x_209, x_5, x_6, x_7, x_8, x_208);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_158 = x_211;
x_159 = x_212;
goto block_184;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_210, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
lean_dec(x_210);
x_185 = x_213;
x_186 = x_214;
goto block_206;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_inc(x_1);
x_215 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_215, 0, x_1);
x_216 = l_Lean_Meta_SynthInstance_main___lambda__2___closed__2;
x_217 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
x_218 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_219 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_219, x_5, x_6, x_7, x_8, x_208);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
lean_inc(x_8);
x_223 = l_Lean_Meta_SynthInstance_main___lambda__1(x_1, x_2, x_221, x_5, x_6, x_7, x_8, x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_158 = x_224;
x_159 = x_225;
goto block_184;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_223, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
lean_dec(x_223);
x_185 = x_226;
x_186 = x_227;
goto block_206;
}
}
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_277; lean_object* x_278; uint8_t x_299; lean_object* x_300; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_239 = lean_ctor_get(x_31, 0);
x_240 = lean_ctor_get(x_31, 1);
x_241 = lean_ctor_get(x_31, 2);
x_242 = lean_ctor_get(x_31, 4);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_31);
x_243 = lean_ctor_get(x_32, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_244 = x_32;
} else {
 lean_dec_ref(x_32);
 x_244 = lean_box(0);
}
x_245 = 0;
if (lean_is_scalar(x_244)) {
 x_246 = lean_alloc_ctor(0, 1, 1);
} else {
 x_246 = x_244;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set_uint8(x_246, sizeof(void*)*1, x_245);
x_247 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_247, 0, x_239);
lean_ctor_set(x_247, 1, x_240);
lean_ctor_set(x_247, 2, x_241);
lean_ctor_set(x_247, 3, x_246);
lean_ctor_set(x_247, 4, x_242);
x_248 = lean_st_ref_set(x_8, x_247, x_33);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_321 = lean_st_ref_get(x_8, x_249);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_322, 3);
lean_inc(x_323);
lean_dec(x_322);
x_324 = lean_ctor_get_uint8(x_323, sizeof(void*)*1);
lean_dec(x_323);
if (x_324 == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_321, 1);
lean_inc(x_325);
lean_dec(x_321);
x_299 = x_245;
x_300 = x_325;
goto block_320;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_326 = lean_ctor_get(x_321, 1);
lean_inc(x_326);
lean_dec(x_321);
lean_inc(x_3);
x_327 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_3, x_5, x_6, x_7, x_8, x_326);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = lean_unbox(x_328);
lean_dec(x_328);
x_299 = x_330;
x_300 = x_329;
goto block_320;
}
block_276:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_252 = lean_st_ref_get(x_8, x_251);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_ctor_get(x_253, 3);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get_uint8(x_255, sizeof(void*)*1);
lean_dec(x_255);
x_257 = lean_st_ref_take(x_8, x_254);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_258, 3);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 1);
lean_inc(x_260);
lean_dec(x_257);
x_261 = lean_ctor_get(x_258, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_258, 1);
lean_inc(x_262);
x_263 = lean_ctor_get(x_258, 2);
lean_inc(x_263);
x_264 = lean_ctor_get(x_258, 4);
lean_inc(x_264);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 lean_ctor_release(x_258, 3);
 lean_ctor_release(x_258, 4);
 x_265 = x_258;
} else {
 lean_dec_ref(x_258);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_259, 0);
lean_inc(x_266);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_267 = x_259;
} else {
 lean_dec_ref(x_259);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(0, 1, 1);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set_uint8(x_268, sizeof(void*)*1, x_29);
if (lean_is_scalar(x_265)) {
 x_269 = lean_alloc_ctor(0, 5, 0);
} else {
 x_269 = x_265;
}
lean_ctor_set(x_269, 0, x_261);
lean_ctor_set(x_269, 1, x_262);
lean_ctor_set(x_269, 2, x_263);
lean_ctor_set(x_269, 3, x_268);
lean_ctor_set(x_269, 4, x_264);
x_270 = lean_st_ref_set(x_8, x_269, x_260);
lean_dec(x_8);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_272 = x_270;
} else {
 lean_dec_ref(x_270);
 x_272 = lean_box(0);
}
x_273 = lean_box(x_256);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_250);
lean_ctor_set(x_274, 1, x_273);
if (lean_is_scalar(x_272)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_272;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_271);
x_10 = x_275;
goto block_22;
}
block_298:
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_279 = lean_st_ref_get(x_8, x_278);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_281 = lean_st_ref_take(x_8, x_280);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_282, 3);
lean_inc(x_283);
x_284 = lean_ctor_get(x_281, 1);
lean_inc(x_284);
lean_dec(x_281);
x_285 = lean_ctor_get(x_282, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_282, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_282, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_282, 4);
lean_inc(x_288);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 lean_ctor_release(x_282, 2);
 lean_ctor_release(x_282, 3);
 lean_ctor_release(x_282, 4);
 x_289 = x_282;
} else {
 lean_dec_ref(x_282);
 x_289 = lean_box(0);
}
x_290 = lean_ctor_get(x_283, 0);
lean_inc(x_290);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_291 = x_283;
} else {
 lean_dec_ref(x_283);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(0, 1, 1);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set_uint8(x_292, sizeof(void*)*1, x_29);
if (lean_is_scalar(x_289)) {
 x_293 = lean_alloc_ctor(0, 5, 0);
} else {
 x_293 = x_289;
}
lean_ctor_set(x_293, 0, x_285);
lean_ctor_set(x_293, 1, x_286);
lean_ctor_set(x_293, 2, x_287);
lean_ctor_set(x_293, 3, x_292);
lean_ctor_set(x_293, 4, x_288);
x_294 = lean_st_ref_set(x_8, x_293, x_284);
lean_dec(x_8);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_296 = x_294;
} else {
 lean_dec_ref(x_294);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_296;
 lean_ctor_set_tag(x_297, 1);
}
lean_ctor_set(x_297, 0, x_277);
lean_ctor_set(x_297, 1, x_295);
x_10 = x_297;
goto block_22;
}
block_320:
{
if (x_299 == 0)
{
lean_object* x_301; lean_object* x_302; 
lean_dec(x_3);
x_301 = lean_box(0);
lean_inc(x_8);
x_302 = l_Lean_Meta_SynthInstance_main___lambda__1(x_1, x_2, x_301, x_5, x_6, x_7, x_8, x_300);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_250 = x_303;
x_251 = x_304;
goto block_276;
}
else
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_302, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_302, 1);
lean_inc(x_306);
lean_dec(x_302);
x_277 = x_305;
x_278 = x_306;
goto block_298;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_inc(x_1);
x_307 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_307, 0, x_1);
x_308 = l_Lean_Meta_SynthInstance_main___lambda__2___closed__2;
x_309 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_307);
x_310 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_311 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_311, x_5, x_6, x_7, x_8, x_300);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
lean_inc(x_8);
x_315 = l_Lean_Meta_SynthInstance_main___lambda__1(x_1, x_2, x_313, x_5, x_6, x_7, x_8, x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_250 = x_316;
x_251 = x_317;
goto block_276;
}
else
{
lean_object* x_318; lean_object* x_319; 
x_318 = lean_ctor_get(x_315, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_315, 1);
lean_inc(x_319);
lean_dec(x_315);
x_277 = x_318;
x_278 = x_319;
goto block_298;
}
}
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; 
x_331 = lean_ctor_get(x_7, 3);
lean_inc(x_331);
x_332 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__7___rarg(x_8, x_24);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_st_ref_get(x_8, x_334);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_336, 3);
lean_inc(x_337);
lean_dec(x_336);
x_338 = lean_ctor_get_uint8(x_337, sizeof(void*)*1);
lean_dec(x_337);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_3);
x_339 = lean_ctor_get(x_335, 1);
lean_inc(x_339);
lean_dec(x_335);
x_340 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_341 = l_Lean_Meta_SynthInstance_main___lambda__1(x_1, x_2, x_340, x_5, x_6, x_7, x_8, x_339);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_333, x_4, x_331, x_5, x_6, x_7, x_8, x_343);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_345 = !lean_is_exclusive(x_344);
if (x_345 == 0)
{
lean_object* x_346; 
x_346 = lean_ctor_get(x_344, 0);
lean_dec(x_346);
lean_ctor_set(x_344, 0, x_342);
return x_344;
}
else
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_344, 1);
lean_inc(x_347);
lean_dec(x_344);
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_342);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; 
x_349 = lean_ctor_get(x_341, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_341, 1);
lean_inc(x_350);
lean_dec(x_341);
x_351 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_333, x_4, x_331, x_5, x_6, x_7, x_8, x_350);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_352 = !lean_is_exclusive(x_351);
if (x_352 == 0)
{
lean_object* x_353; 
x_353 = lean_ctor_get(x_351, 0);
lean_dec(x_353);
lean_ctor_set_tag(x_351, 1);
lean_ctor_set(x_351, 0, x_349);
return x_351;
}
else
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_351, 1);
lean_inc(x_354);
lean_dec(x_351);
x_355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_355, 0, x_349);
lean_ctor_set(x_355, 1, x_354);
return x_355;
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_356 = lean_ctor_get(x_335, 1);
lean_inc(x_356);
lean_dec(x_335);
lean_inc(x_3);
x_357 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_3, x_5, x_6, x_7, x_8, x_356);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_unbox(x_358);
lean_dec(x_358);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_3);
x_360 = lean_ctor_get(x_357, 1);
lean_inc(x_360);
lean_dec(x_357);
x_361 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_362 = l_Lean_Meta_SynthInstance_main___lambda__1(x_1, x_2, x_361, x_5, x_6, x_7, x_8, x_360);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_365 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_333, x_4, x_331, x_5, x_6, x_7, x_8, x_364);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_366 = !lean_is_exclusive(x_365);
if (x_366 == 0)
{
lean_object* x_367; 
x_367 = lean_ctor_get(x_365, 0);
lean_dec(x_367);
lean_ctor_set(x_365, 0, x_363);
return x_365;
}
else
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_ctor_get(x_365, 1);
lean_inc(x_368);
lean_dec(x_365);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_363);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_370 = lean_ctor_get(x_362, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_362, 1);
lean_inc(x_371);
lean_dec(x_362);
x_372 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_333, x_4, x_331, x_5, x_6, x_7, x_8, x_371);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_373 = !lean_is_exclusive(x_372);
if (x_373 == 0)
{
lean_object* x_374; 
x_374 = lean_ctor_get(x_372, 0);
lean_dec(x_374);
lean_ctor_set_tag(x_372, 1);
lean_ctor_set(x_372, 0, x_370);
return x_372;
}
else
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_ctor_get(x_372, 1);
lean_inc(x_375);
lean_dec(x_372);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_370);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_377 = lean_ctor_get(x_357, 1);
lean_inc(x_377);
lean_dec(x_357);
lean_inc(x_1);
x_378 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_378, 0, x_1);
x_379 = l_Lean_Meta_SynthInstance_main___lambda__2___closed__2;
x_380 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_378);
x_381 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_382 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
x_383 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_382, x_5, x_6, x_7, x_8, x_377);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_386 = l_Lean_Meta_SynthInstance_main___lambda__1(x_1, x_2, x_384, x_5, x_6, x_7, x_8, x_385);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_333, x_4, x_331, x_5, x_6, x_7, x_8, x_388);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_390 = !lean_is_exclusive(x_389);
if (x_390 == 0)
{
lean_object* x_391; 
x_391 = lean_ctor_get(x_389, 0);
lean_dec(x_391);
lean_ctor_set(x_389, 0, x_387);
return x_389;
}
else
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_ctor_get(x_389, 1);
lean_inc(x_392);
lean_dec(x_389);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_387);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_394 = lean_ctor_get(x_386, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_386, 1);
lean_inc(x_395);
lean_dec(x_386);
x_396 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_333, x_4, x_331, x_5, x_6, x_7, x_8, x_395);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_397 = !lean_is_exclusive(x_396);
if (x_397 == 0)
{
lean_object* x_398; 
x_398 = lean_ctor_get(x_396, 0);
lean_dec(x_398);
lean_ctor_set_tag(x_396, 1);
lean_ctor_set(x_396, 0, x_394);
return x_396;
}
else
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_dec(x_396);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_394);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SynthInstance_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_main___lambda__2), 9, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_8);
x_10 = l_Lean_Core_withCurrHeartbeats___at_Lean_Meta_SynthInstance_main___spec__2(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_SynthInstance_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_SynthInstance_main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_14 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_9, x_3, x_4, x_5, x_6, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Level_hasMVar(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_array_push(x_12, x_15);
lean_ctor_set(x_2, 0, x_18);
x_1 = x_10;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_13);
x_20 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_push(x_12, x_21);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_2, 1, x_25);
lean_ctor_set(x_2, 0, x_23);
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
x_29 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_9, x_3, x_4, x_5, x_6, x_7);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Level_hasMVar(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_array_push(x_27, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
x_1 = x_10;
x_2 = x_34;
x_7 = x_31;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_30);
lean_dec(x_28);
x_36 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_array_push(x_27, x_37);
x_40 = 1;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__8;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
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
x_13 = lean_array_to_list(lean_box(0), x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
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
x_19 = lean_array_to_list(lean_box(0), x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
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
x_1 = lean_mk_string("type class resolution failed, insufficient number of arguments");
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
x_29 = l_Lean_throwError___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_28, x_4, x_5, x_6, x_7, x_27);
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
x_2 = l_Lean_mkSort(x_1);
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
x_18 = l_Lean_Expr_getAppNumArgsAux(x_3, x_17);
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
x_49 = l_Lean_Expr_getAppNumArgsAux(x_3, x_48);
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_synthInstance_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static size_t _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2;
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
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_synthInstance_x3f___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_synthInstance_x3f___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2;
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
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2;
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
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_synthInstance_x3f___spec__7(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
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
x_92 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_synthInstance_x3f___spec__7(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
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
x_106 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_5, x_8, x_9, x_2, x_3);
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
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_13, x_16, x_17, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_4(x_3, x_4, x_5, x_6, x_7);
x_10 = l_Lean_profileitIOUnsafe___rarg(x_1, x_2, x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__8___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_main(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("preprocess: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ==> ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
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
lean_inc(x_1);
x_8 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocessOutParam(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_28 = lean_st_ref_get(x_6, x_10);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = 0;
x_12 = x_33;
x_13 = x_32;
goto block_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_11, x_3, x_4, x_5, x_6, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unbox(x_36);
lean_dec(x_36);
x_12 = x_38;
x_13 = x_37;
goto block_27;
}
block_27:
{
if (x_12 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = l_Lean_Meta_SynthInstance_main(x_9, x_2, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_Meta_synthInstance_x3f___lambda__2___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_synthInstance_x3f___lambda__2___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_9);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_9);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_11, x_23, x_3, x_4, x_5, x_6, x_13);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Meta_SynthInstance_main(x_9, x_2, x_3, x_4, x_5, x_6, x_25);
return x_26;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
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
x_20 = l_Std_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__4(x_19, x_1, x_3);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
x_28 = lean_ctor_get(x_14, 3);
x_29 = lean_ctor_get(x_14, 4);
x_30 = lean_ctor_get(x_14, 5);
x_31 = lean_ctor_get(x_14, 6);
x_32 = lean_ctor_get(x_14, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_32);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
lean_inc(x_3);
x_33 = l_Std_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__4(x_32, x_1, x_3);
x_34 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_28);
lean_ctor_set(x_34, 4, x_29);
lean_ctor_set(x_34, 5, x_30);
lean_ctor_set(x_34, 6, x_31);
lean_ctor_set(x_13, 1, x_34);
x_35 = lean_st_ref_set(x_5, x_13, x_15);
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
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 2);
x_41 = lean_ctor_get(x_13, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_42 = lean_ctor_get(x_14, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_14, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_14, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_14, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_14, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_14, 2);
lean_inc(x_48);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 lean_ctor_release(x_14, 6);
 x_49 = x_14;
} else {
 lean_dec_ref(x_14);
 x_49 = lean_box(0);
}
lean_inc(x_3);
x_50 = l_Std_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__4(x_48, x_1, x_3);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 7, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_44);
lean_ctor_set(x_51, 4, x_45);
lean_ctor_set(x_51, 5, x_46);
lean_ctor_set(x_51, 6, x_47);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_39);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_40);
lean_ctor_set(x_52, 3, x_41);
x_53 = lean_st_ref_set(x_5, x_52, x_15);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_3);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; 
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_8);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec(x_1);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_3);
lean_ctor_set(x_58, 1, x_8);
return x_58;
}
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result type");
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
lean_object* x_1; 
x_1 = lean_mk_string("\nis not definitionally equal to");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___lambda__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = lean_infer_type(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 5);
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_18);
lean_ctor_set(x_20, 5, x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_13);
lean_inc(x_3);
x_21 = l_Lean_Meta_isExprDefEq(x_3, x_13, x_20, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_43 = lean_st_ref_get(x_10, x_24);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = 0;
x_25 = x_48;
x_26 = x_47;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
lean_inc(x_5);
x_50 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_5, x_7, x_8, x_9, x_10, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
x_25 = x_53;
x_26 = x_52;
goto block_42;
}
block_42:
{
if (x_25 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_27 = lean_box(0);
x_28 = lean_apply_6(x_4, x_27, x_7, x_8, x_9, x_10, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = l_Lean_indentExpr(x_13);
x_30 = l_Lean_Meta_synthInstance_x3f___lambda__4___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Meta_synthInstance_x3f___lambda__4___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_indentExpr(x_3);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_5, x_37, x_7, x_8, x_9, x_10, x_26);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = lean_apply_6(x_4, x_40, x_7, x_8, x_9, x_10, x_39);
return x_41;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_dec(x_21);
lean_inc(x_8);
x_55 = l_Lean_Meta_instantiateMVars(x_1, x_7, x_8, x_9, x_10, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_56);
x_58 = l_Lean_Meta_check(x_56, x_7, x_8, x_9, x_10, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_56);
x_61 = lean_apply_6(x_4, x_60, x_7, x_8, x_9, x_10, x_59);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_21);
if (x_66 == 0)
{
return x_21;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_21, 0);
x_68 = lean_ctor_get(x_21, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_21);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_12);
if (x_70 == 0)
{
return x_12;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_12, 0);
x_72 = lean_ctor_get(x_12, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_12);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result ");
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
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_synthInstance_maxSize;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_394 = lean_ctor_get(x_5, 0);
lean_inc(x_394);
x_395 = l_Lean_Meta_synthInstance_x3f___lambda__5___closed__3;
x_396 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_394, x_395);
lean_dec(x_394);
x_397 = l_Lean_Meta_getConfig(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_8 = x_396;
x_9 = x_398;
x_10 = x_399;
goto block_393;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_396);
x_400 = lean_ctor_get(x_2, 0);
lean_inc(x_400);
lean_dec(x_2);
x_401 = lean_ctor_get(x_397, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_397, 1);
lean_inc(x_402);
lean_dec(x_397);
x_8 = x_400;
x_9 = x_401;
x_10 = x_402;
goto block_393;
}
block_393:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = 1;
x_15 = 0;
x_16 = 3;
lean_ctor_set_uint8(x_12, 0, x_14);
lean_ctor_set_uint8(x_12, 1, x_14);
lean_ctor_set_uint8(x_12, 3, x_15);
lean_ctor_set_uint8(x_12, 4, x_14);
lean_ctor_set_uint8(x_12, 5, x_16);
lean_ctor_set_uint8(x_12, 11, x_14);
lean_inc(x_4);
x_17 = l_Lean_Meta_instantiateMVars(x_1, x_3, x_4, x_5, x_6, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_18, x_20, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_6, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_4, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_22);
x_32 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__1(x_31, x_22);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_free_object(x_26);
lean_inc(x_22);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__2), 7, 2);
lean_closure_set(x_33, 0, x_22);
lean_closure_set(x_33, 1, x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_34 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_33, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
x_37 = x_15;
goto block_93;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_35, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Array_isEmpty___rarg(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
x_37 = x_14;
goto block_93;
}
else
{
x_37 = x_15;
goto block_93;
}
}
block_93:
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_9);
x_38 = lean_box(0);
x_39 = l_Lean_Meta_synthInstance_x3f___lambda__3(x_22, x_37, x_38, x_3, x_4, x_5, x_6, x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_box(x_37);
lean_inc(x_22);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__3___boxed), 8, 2);
lean_closure_set(x_46, 0, x_22);
lean_closure_set(x_46, 1, x_45);
lean_inc(x_3);
x_47 = l_Lean_Meta_openAbstractMVarsResult(x_44, x_3, x_4, x_5, x_6, x_36);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_83 = lean_st_ref_get(x_6, x_50);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 3);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_ctor_get_uint8(x_85, sizeof(void*)*1);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_53 = x_15;
x_54 = x_87;
goto block_82;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_dec(x_83);
x_89 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_52, x_3, x_4, x_5, x_6, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_unbox(x_90);
lean_dec(x_90);
x_53 = x_92;
x_54 = x_91;
goto block_82;
}
block_82:
{
if (x_53 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_box(0);
x_56 = l_Lean_Meta_synthInstance_x3f___lambda__4(x_51, x_9, x_22, x_46, x_52, x_55, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_inc(x_51);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_51);
x_66 = l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_52, x_69, x_3, x_4, x_5, x_6, x_54);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Meta_synthInstance_x3f___lambda__4(x_51, x_9, x_22, x_46, x_52, x_71, x_3, x_4, x_5, x_6, x_72);
lean_dec(x_71);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
return x_73;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_73);
if (x_78 == 0)
{
return x_73;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_73, 0);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_73);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_97 = !lean_is_exclusive(x_34);
if (x_97 == 0)
{
return x_34;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_34, 0);
x_99 = lean_ctor_get(x_34, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_34);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_101 = lean_ctor_get(x_32, 0);
lean_inc(x_101);
lean_dec(x_32);
lean_ctor_set(x_26, 0, x_101);
return x_26;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_26, 0);
x_103 = lean_ctor_get(x_26, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_26);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_104, 2);
lean_inc(x_105);
lean_dec(x_104);
lean_inc(x_22);
x_106 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__1(x_105, x_22);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_inc(x_22);
x_107 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__2), 7, 2);
lean_closure_set(x_107, 0, x_22);
lean_closure_set(x_107, 1, x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_108 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_107, x_3, x_4, x_5, x_6, x_103);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
x_111 = x_15;
goto block_167;
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_109, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec(x_168);
x_170 = l_Array_isEmpty___rarg(x_169);
lean_dec(x_169);
if (x_170 == 0)
{
x_111 = x_14;
goto block_167;
}
else
{
x_111 = x_15;
goto block_167;
}
}
block_167:
{
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_9);
x_112 = lean_box(0);
x_113 = l_Lean_Meta_synthInstance_x3f___lambda__3(x_22, x_111, x_112, x_3, x_4, x_5, x_6, x_110);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_118 = lean_ctor_get(x_109, 0);
lean_inc(x_118);
lean_dec(x_109);
x_119 = lean_box(x_111);
lean_inc(x_22);
x_120 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__3___boxed), 8, 2);
lean_closure_set(x_120, 0, x_22);
lean_closure_set(x_120, 1, x_119);
lean_inc(x_3);
x_121 = l_Lean_Meta_openAbstractMVarsResult(x_118, x_3, x_4, x_5, x_6, x_110);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_157 = lean_st_ref_get(x_6, x_124);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_158, 3);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_ctor_get_uint8(x_159, sizeof(void*)*1);
lean_dec(x_159);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
x_127 = x_15;
x_128 = x_161;
goto block_156;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_dec(x_157);
x_163 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_126, x_3, x_4, x_5, x_6, x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_unbox(x_164);
lean_dec(x_164);
x_127 = x_166;
x_128 = x_165;
goto block_156;
}
block_156:
{
if (x_127 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_box(0);
x_130 = l_Lean_Meta_synthInstance_x3f___lambda__4(x_125, x_9, x_22, x_120, x_126, x_129, x_3, x_4, x_5, x_6, x_128);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
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
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_137 = x_130;
} else {
 lean_dec_ref(x_130);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_inc(x_125);
x_139 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_139, 0, x_125);
x_140 = l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2;
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_126, x_143, x_3, x_4, x_5, x_6, x_128);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Meta_synthInstance_x3f___lambda__4(x_125, x_9, x_22, x_120, x_126, x_145, x_3, x_4, x_5, x_6, x_146);
lean_dec(x_145);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_147, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_147, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_154 = x_147;
} else {
 lean_dec_ref(x_147);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_171 = lean_ctor_get(x_108, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_108, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_173 = x_108;
} else {
 lean_dec_ref(x_108);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_175 = lean_ctor_get(x_106, 0);
lean_inc(x_175);
lean_dec(x_106);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_103);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_3);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_177 = !lean_is_exclusive(x_21);
if (x_177 == 0)
{
return x_21;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_21, 0);
x_179 = lean_ctor_get(x_21, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_21);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_181 = lean_ctor_get_uint8(x_12, 2);
x_182 = lean_ctor_get_uint8(x_12, 6);
x_183 = lean_ctor_get_uint8(x_12, 7);
x_184 = lean_ctor_get_uint8(x_12, 8);
x_185 = lean_ctor_get_uint8(x_12, 9);
x_186 = lean_ctor_get_uint8(x_12, 10);
x_187 = lean_ctor_get_uint8(x_12, 12);
x_188 = lean_ctor_get_uint8(x_12, 13);
lean_dec(x_12);
x_189 = 1;
x_190 = 0;
x_191 = 3;
x_192 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_192, 0, x_189);
lean_ctor_set_uint8(x_192, 1, x_189);
lean_ctor_set_uint8(x_192, 2, x_181);
lean_ctor_set_uint8(x_192, 3, x_190);
lean_ctor_set_uint8(x_192, 4, x_189);
lean_ctor_set_uint8(x_192, 5, x_191);
lean_ctor_set_uint8(x_192, 6, x_182);
lean_ctor_set_uint8(x_192, 7, x_183);
lean_ctor_set_uint8(x_192, 8, x_184);
lean_ctor_set_uint8(x_192, 9, x_185);
lean_ctor_set_uint8(x_192, 10, x_186);
lean_ctor_set_uint8(x_192, 11, x_189);
lean_ctor_set_uint8(x_192, 12, x_187);
lean_ctor_set_uint8(x_192, 13, x_188);
lean_ctor_set(x_3, 0, x_192);
lean_inc(x_4);
x_193 = l_Lean_Meta_instantiateMVars(x_1, x_3, x_4, x_5, x_6, x_10);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_197 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_194, x_196, x_3, x_4, x_5, x_6, x_195);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_st_ref_get(x_6, x_199);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_st_ref_get(x_4, x_201);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_dec(x_203);
x_207 = lean_ctor_get(x_206, 2);
lean_inc(x_207);
lean_dec(x_206);
lean_inc(x_198);
x_208 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__1(x_207, x_198);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_205);
lean_inc(x_198);
x_209 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__2), 7, 2);
lean_closure_set(x_209, 0, x_198);
lean_closure_set(x_209, 1, x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_210 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_209, x_3, x_4, x_5, x_6, x_204);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
if (lean_obj_tag(x_211) == 0)
{
x_213 = x_190;
goto block_269;
}
else
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_270 = lean_ctor_get(x_211, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
lean_dec(x_270);
x_272 = l_Array_isEmpty___rarg(x_271);
lean_dec(x_271);
if (x_272 == 0)
{
x_213 = x_189;
goto block_269;
}
else
{
x_213 = x_190;
goto block_269;
}
}
block_269:
{
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_9);
x_214 = lean_box(0);
x_215 = l_Lean_Meta_synthInstance_x3f___lambda__3(x_198, x_213, x_214, x_3, x_4, x_5, x_6, x_212);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_218 = x_215;
} else {
 lean_dec_ref(x_215);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_220 = lean_ctor_get(x_211, 0);
lean_inc(x_220);
lean_dec(x_211);
x_221 = lean_box(x_213);
lean_inc(x_198);
x_222 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__3___boxed), 8, 2);
lean_closure_set(x_222, 0, x_198);
lean_closure_set(x_222, 1, x_221);
lean_inc(x_3);
x_223 = l_Lean_Meta_openAbstractMVarsResult(x_220, x_3, x_4, x_5, x_6, x_212);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
lean_dec(x_223);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_259 = lean_st_ref_get(x_6, x_226);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_260, 3);
lean_inc(x_261);
lean_dec(x_260);
x_262 = lean_ctor_get_uint8(x_261, sizeof(void*)*1);
lean_dec(x_261);
if (x_262 == 0)
{
lean_object* x_263; 
x_263 = lean_ctor_get(x_259, 1);
lean_inc(x_263);
lean_dec(x_259);
x_229 = x_190;
x_230 = x_263;
goto block_258;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_264 = lean_ctor_get(x_259, 1);
lean_inc(x_264);
lean_dec(x_259);
x_265 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_228, x_3, x_4, x_5, x_6, x_264);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_unbox(x_266);
lean_dec(x_266);
x_229 = x_268;
x_230 = x_267;
goto block_258;
}
block_258:
{
if (x_229 == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_box(0);
x_232 = l_Lean_Meta_synthInstance_x3f___lambda__4(x_227, x_9, x_198, x_222, x_228, x_231, x_3, x_4, x_5, x_6, x_230);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_232, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_232, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_239 = x_232;
} else {
 lean_dec_ref(x_232);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_inc(x_227);
x_241 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_241, 0, x_227);
x_242 = l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2;
x_243 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
x_244 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_245 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_228, x_245, x_3, x_4, x_5, x_6, x_230);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = l_Lean_Meta_synthInstance_x3f___lambda__4(x_227, x_9, x_198, x_222, x_228, x_247, x_3, x_4, x_5, x_6, x_248);
lean_dec(x_247);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_252 = x_249;
} else {
 lean_dec_ref(x_249);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_249, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_249, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_256 = x_249;
} else {
 lean_dec_ref(x_249);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
}
}
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_198);
lean_dec(x_3);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_273 = lean_ctor_get(x_210, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_210, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_275 = x_210;
} else {
 lean_dec_ref(x_210);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_198);
lean_dec(x_3);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_277 = lean_ctor_get(x_208, 0);
lean_inc(x_277);
lean_dec(x_208);
if (lean_is_scalar(x_205)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_205;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_204);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_3);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_279 = lean_ctor_get(x_197, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_197, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_281 = x_197;
} else {
 lean_dec_ref(x_197);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; uint8_t x_291; uint8_t x_292; uint8_t x_293; uint8_t x_294; uint8_t x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; uint8_t x_299; uint8_t x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_283 = lean_ctor_get(x_3, 0);
x_284 = lean_ctor_get(x_3, 1);
x_285 = lean_ctor_get(x_3, 2);
x_286 = lean_ctor_get(x_3, 3);
x_287 = lean_ctor_get(x_3, 4);
x_288 = lean_ctor_get(x_3, 5);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_3);
x_289 = lean_ctor_get_uint8(x_283, 2);
x_290 = lean_ctor_get_uint8(x_283, 6);
x_291 = lean_ctor_get_uint8(x_283, 7);
x_292 = lean_ctor_get_uint8(x_283, 8);
x_293 = lean_ctor_get_uint8(x_283, 9);
x_294 = lean_ctor_get_uint8(x_283, 10);
x_295 = lean_ctor_get_uint8(x_283, 12);
x_296 = lean_ctor_get_uint8(x_283, 13);
if (lean_is_exclusive(x_283)) {
 x_297 = x_283;
} else {
 lean_dec_ref(x_283);
 x_297 = lean_box(0);
}
x_298 = 1;
x_299 = 0;
x_300 = 3;
if (lean_is_scalar(x_297)) {
 x_301 = lean_alloc_ctor(0, 0, 14);
} else {
 x_301 = x_297;
}
lean_ctor_set_uint8(x_301, 0, x_298);
lean_ctor_set_uint8(x_301, 1, x_298);
lean_ctor_set_uint8(x_301, 2, x_289);
lean_ctor_set_uint8(x_301, 3, x_299);
lean_ctor_set_uint8(x_301, 4, x_298);
lean_ctor_set_uint8(x_301, 5, x_300);
lean_ctor_set_uint8(x_301, 6, x_290);
lean_ctor_set_uint8(x_301, 7, x_291);
lean_ctor_set_uint8(x_301, 8, x_292);
lean_ctor_set_uint8(x_301, 9, x_293);
lean_ctor_set_uint8(x_301, 10, x_294);
lean_ctor_set_uint8(x_301, 11, x_298);
lean_ctor_set_uint8(x_301, 12, x_295);
lean_ctor_set_uint8(x_301, 13, x_296);
x_302 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_284);
lean_ctor_set(x_302, 2, x_285);
lean_ctor_set(x_302, 3, x_286);
lean_ctor_set(x_302, 4, x_287);
lean_ctor_set(x_302, 5, x_288);
lean_inc(x_4);
x_303 = l_Lean_Meta_instantiateMVars(x_1, x_302, x_4, x_5, x_6, x_10);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_302);
x_307 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_304, x_306, x_302, x_4, x_5, x_6, x_305);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_st_ref_get(x_6, x_309);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
x_312 = lean_st_ref_get(x_4, x_311);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_315 = x_312;
} else {
 lean_dec_ref(x_312);
 x_315 = lean_box(0);
}
x_316 = lean_ctor_get(x_313, 1);
lean_inc(x_316);
lean_dec(x_313);
x_317 = lean_ctor_get(x_316, 2);
lean_inc(x_317);
lean_dec(x_316);
lean_inc(x_308);
x_318 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__1(x_317, x_308);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_315);
lean_inc(x_308);
x_319 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__2), 7, 2);
lean_closure_set(x_319, 0, x_308);
lean_closure_set(x_319, 1, x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_302);
x_320 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_319, x_302, x_4, x_5, x_6, x_314);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
if (lean_obj_tag(x_321) == 0)
{
x_323 = x_299;
goto block_379;
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; 
x_380 = lean_ctor_get(x_321, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
lean_dec(x_380);
x_382 = l_Array_isEmpty___rarg(x_381);
lean_dec(x_381);
if (x_382 == 0)
{
x_323 = x_298;
goto block_379;
}
else
{
x_323 = x_299;
goto block_379;
}
}
block_379:
{
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_9);
x_324 = lean_box(0);
x_325 = l_Lean_Meta_synthInstance_x3f___lambda__3(x_308, x_323, x_324, x_302, x_4, x_5, x_6, x_322);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_302);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_328 = x_325;
} else {
 lean_dec_ref(x_325);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
return x_329;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; 
x_330 = lean_ctor_get(x_321, 0);
lean_inc(x_330);
lean_dec(x_321);
x_331 = lean_box(x_323);
lean_inc(x_308);
x_332 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__3___boxed), 8, 2);
lean_closure_set(x_332, 0, x_308);
lean_closure_set(x_332, 1, x_331);
lean_inc(x_302);
x_333 = l_Lean_Meta_openAbstractMVarsResult(x_330, x_302, x_4, x_5, x_6, x_322);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_334, 1);
lean_inc(x_335);
lean_dec(x_334);
x_336 = lean_ctor_get(x_333, 1);
lean_inc(x_336);
lean_dec(x_333);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_369 = lean_st_ref_get(x_6, x_336);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_370, 3);
lean_inc(x_371);
lean_dec(x_370);
x_372 = lean_ctor_get_uint8(x_371, sizeof(void*)*1);
lean_dec(x_371);
if (x_372 == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_369, 1);
lean_inc(x_373);
lean_dec(x_369);
x_339 = x_299;
x_340 = x_373;
goto block_368;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; 
x_374 = lean_ctor_get(x_369, 1);
lean_inc(x_374);
lean_dec(x_369);
x_375 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_338, x_302, x_4, x_5, x_6, x_374);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
x_378 = lean_unbox(x_376);
lean_dec(x_376);
x_339 = x_378;
x_340 = x_377;
goto block_368;
}
block_368:
{
if (x_339 == 0)
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_box(0);
x_342 = l_Lean_Meta_synthInstance_x3f___lambda__4(x_337, x_9, x_308, x_332, x_338, x_341, x_302, x_4, x_5, x_6, x_340);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_345 = x_342;
} else {
 lean_dec_ref(x_342);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_347 = lean_ctor_get(x_342, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_342, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_349 = x_342;
} else {
 lean_dec_ref(x_342);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_inc(x_337);
x_351 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_351, 0, x_337);
x_352 = l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2;
x_353 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
x_354 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_355 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
x_356 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_338, x_355, x_302, x_4, x_5, x_6, x_340);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = l_Lean_Meta_synthInstance_x3f___lambda__4(x_337, x_9, x_308, x_332, x_338, x_357, x_302, x_4, x_5, x_6, x_358);
lean_dec(x_357);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_362 = x_359;
} else {
 lean_dec_ref(x_359);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = lean_ctor_get(x_359, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_359, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_366 = x_359;
} else {
 lean_dec_ref(x_359);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 2, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_365);
return x_367;
}
}
}
}
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_308);
lean_dec(x_302);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_383 = lean_ctor_get(x_320, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_320, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_385 = x_320;
} else {
 lean_dec_ref(x_320);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 2, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_384);
return x_386;
}
}
else
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_308);
lean_dec(x_302);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_387 = lean_ctor_get(x_318, 0);
lean_inc(x_387);
lean_dec(x_318);
if (lean_is_scalar(x_315)) {
 x_388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_388 = x_315;
}
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_314);
return x_388;
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_302);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_389 = lean_ctor_get(x_307, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_307, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_391 = x_307;
} else {
 lean_dec_ref(x_307);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(1, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_390);
return x_392;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeclass inference");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___lambda__5), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_Meta_synthInstance_x3f___closed__1;
x_11 = l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__8___rarg(x_10, x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_synthInstance_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_synthInstance_x3f___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_synthInstance_x3f___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_profileitM___at_Lean_Meta_synthInstance_x3f___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_synthInstance_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_synthInstance_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
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
x_30 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_29, x_3, x_4, x_5, x_6, x_24);
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
x_20 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_19, x_3, x_4, x_5, x_6, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___closed__2;
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
x_16 = l_Lean_Meta_isExprMVarAssigned(x_1, x_4, x_5, x_6, x_7, x_11);
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
x_20 = l_Lean_Meta_assignExprMVar(x_1, x_15, x_4, x_5, x_6, x_7, x_19);
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
x_1 = lean_mk_string("synthPending");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_2 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("synthPending ");
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
x_1 = lean_mk_string("too many nested synthPending invocations");
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
x_7 = l_Lean_Meta_getMVarDecl(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*7);
switch (x_9) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_12 = l_Lean_Meta_isClass_x3f(x_11, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = 0;
x_17 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_13);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 4);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 5);
lean_inc(x_28);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_dec_lt(x_29, x_27);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_32 = lean_ctor_get(x_2, 5);
lean_dec(x_32);
x_33 = lean_ctor_get(x_2, 4);
lean_dec(x_33);
x_34 = lean_ctor_get(x_2, 3);
lean_dec(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_2, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_2, 0);
lean_dec(x_37);
x_38 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
x_39 = lean_nat_add(x_27, x_29);
lean_dec(x_27);
lean_ctor_set(x_2, 4, x_39);
x_55 = lean_st_ref_get(x_5, x_22);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get_uint8(x_57, sizeof(void*)*1);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = 0;
x_40 = x_60;
x_41 = x_59;
goto block_54;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
x_62 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_38, x_2, x_3, x_4, x_5, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unbox(x_63);
lean_dec(x_63);
x_40 = x_65;
x_41 = x_64;
goto block_54;
}
block_54:
{
if (x_40 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_11, x_42, x_2, x_3, x_4, x_5, x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_inc(x_1);
x_44 = l_Lean_mkMVar(x_1);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__4;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_38, x_49, x_2, x_3, x_4, x_5, x_41);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_11, x_51, x_2, x_3, x_4, x_5, x_52);
lean_dec(x_51);
return x_53;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_2);
x_66 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
x_67 = lean_nat_add(x_27, x_29);
lean_dec(x_27);
x_68 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_68, 0, x_23);
lean_ctor_set(x_68, 1, x_24);
lean_ctor_set(x_68, 2, x_25);
lean_ctor_set(x_68, 3, x_26);
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 5, x_28);
x_84 = lean_st_ref_get(x_5, x_22);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 3);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_ctor_get_uint8(x_86, sizeof(void*)*1);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = 0;
x_69 = x_89;
x_70 = x_88;
goto block_83;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_dec(x_84);
x_91 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_66, x_68, x_3, x_4, x_5, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_unbox(x_92);
lean_dec(x_92);
x_69 = x_94;
x_70 = x_93;
goto block_83;
}
block_83:
{
if (x_69 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_box(0);
x_72 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_11, x_71, x_68, x_3, x_4, x_5, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_inc(x_1);
x_73 = l_Lean_mkMVar(x_1);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__4;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_66, x_78, x_68, x_3, x_4, x_5, x_70);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_11, x_80, x_68, x_3, x_4, x_5, x_81);
lean_dec(x_80);
return x_82;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_1);
x_95 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
x_96 = lean_st_ref_get(x_5, x_22);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 3);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_ctor_get_uint8(x_98, sizeof(void*)*1);
lean_dec(x_98);
if (x_99 == 0)
{
uint8_t x_100; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_96);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_96, 0);
lean_dec(x_101);
x_102 = 0;
x_103 = lean_box(x_102);
lean_ctor_set(x_96, 0, x_103);
return x_96;
}
else
{
lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_96, 1);
lean_inc(x_104);
lean_dec(x_96);
x_105 = 0;
x_106 = lean_box(x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_96, 1);
lean_inc(x_108);
lean_dec(x_96);
x_109 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_95, x_2, x_3, x_4, x_5, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
uint8_t x_112; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_109, 0);
lean_dec(x_113);
x_114 = 0;
x_115 = lean_box(x_114);
lean_ctor_set(x_109, 0, x_115);
return x_109;
}
else
{
lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
lean_dec(x_109);
x_117 = 0;
x_118 = lean_box(x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_109, 1);
lean_inc(x_120);
lean_dec(x_109);
x_121 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__6;
x_122 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_95, x_121, x_2, x_3, x_4, x_5, x_120);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_122, 0);
lean_dec(x_124);
x_125 = 0;
x_126 = lean_box(x_125);
lean_ctor_set(x_122, 0, x_126);
return x_122;
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_dec(x_122);
x_128 = 0;
x_129 = lean_box(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_127);
return x_130;
}
}
}
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_12);
if (x_131 == 0)
{
return x_12;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_12, 0);
x_133 = lean_ctor_get(x_12, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_12);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
case 1:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_7, 1);
lean_inc(x_135);
lean_dec(x_7);
x_136 = lean_ctor_get(x_8, 2);
lean_inc(x_136);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_136);
x_137 = l_Lean_Meta_isClass_x3f(x_136, x_2, x_3, x_4, x_5, x_135);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
lean_dec(x_136);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_137);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_137, 0);
lean_dec(x_140);
x_141 = 0;
x_142 = lean_box(x_141);
lean_ctor_set(x_137, 0, x_142);
return x_137;
}
else
{
lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_137, 1);
lean_inc(x_143);
lean_dec(x_137);
x_144 = 0;
x_145 = lean_box(x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_dec(x_138);
x_147 = lean_ctor_get(x_137, 1);
lean_inc(x_147);
lean_dec(x_137);
x_148 = lean_ctor_get(x_2, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_2, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_2, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_2, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_2, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_2, 5);
lean_inc(x_153);
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_nat_dec_lt(x_154, x_152);
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_2);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_157 = lean_ctor_get(x_2, 5);
lean_dec(x_157);
x_158 = lean_ctor_get(x_2, 4);
lean_dec(x_158);
x_159 = lean_ctor_get(x_2, 3);
lean_dec(x_159);
x_160 = lean_ctor_get(x_2, 2);
lean_dec(x_160);
x_161 = lean_ctor_get(x_2, 1);
lean_dec(x_161);
x_162 = lean_ctor_get(x_2, 0);
lean_dec(x_162);
x_163 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
x_164 = lean_nat_add(x_152, x_154);
lean_dec(x_152);
lean_ctor_set(x_2, 4, x_164);
x_180 = lean_st_ref_get(x_5, x_147);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_181, 3);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_ctor_get_uint8(x_182, sizeof(void*)*1);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
lean_dec(x_180);
x_185 = 0;
x_165 = x_185;
x_166 = x_184;
goto block_179;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_186 = lean_ctor_get(x_180, 1);
lean_inc(x_186);
lean_dec(x_180);
x_187 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_163, x_2, x_3, x_4, x_5, x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_unbox(x_188);
lean_dec(x_188);
x_165 = x_190;
x_166 = x_189;
goto block_179;
}
block_179:
{
if (x_165 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_box(0);
x_168 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_136, x_167, x_2, x_3, x_4, x_5, x_166);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_inc(x_1);
x_169 = l_Lean_mkMVar(x_1);
x_170 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_171 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__4;
x_172 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_174 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_163, x_174, x_2, x_3, x_4, x_5, x_166);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_136, x_176, x_2, x_3, x_4, x_5, x_177);
lean_dec(x_176);
return x_178;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_dec(x_2);
x_191 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
x_192 = lean_nat_add(x_152, x_154);
lean_dec(x_152);
x_193 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_193, 0, x_148);
lean_ctor_set(x_193, 1, x_149);
lean_ctor_set(x_193, 2, x_150);
lean_ctor_set(x_193, 3, x_151);
lean_ctor_set(x_193, 4, x_192);
lean_ctor_set(x_193, 5, x_153);
x_209 = lean_st_ref_get(x_5, x_147);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_210, 3);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_ctor_get_uint8(x_211, sizeof(void*)*1);
lean_dec(x_211);
if (x_212 == 0)
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_209, 1);
lean_inc(x_213);
lean_dec(x_209);
x_214 = 0;
x_194 = x_214;
x_195 = x_213;
goto block_208;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_215 = lean_ctor_get(x_209, 1);
lean_inc(x_215);
lean_dec(x_209);
x_216 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_191, x_193, x_3, x_4, x_5, x_215);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_unbox(x_217);
lean_dec(x_217);
x_194 = x_219;
x_195 = x_218;
goto block_208;
}
block_208:
{
if (x_194 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_box(0);
x_197 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_136, x_196, x_193, x_3, x_4, x_5, x_195);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_inc(x_1);
x_198 = l_Lean_mkMVar(x_1);
x_199 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_200 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__4;
x_201 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_202 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_203 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_191, x_203, x_193, x_3, x_4, x_5, x_195);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__1(x_1, x_136, x_205, x_193, x_3, x_4, x_5, x_206);
lean_dec(x_205);
return x_207;
}
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_136);
lean_dec(x_1);
x_220 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
x_221 = lean_st_ref_get(x_5, x_147);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_222, 3);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_ctor_get_uint8(x_223, sizeof(void*)*1);
lean_dec(x_223);
if (x_224 == 0)
{
uint8_t x_225; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_225 = !lean_is_exclusive(x_221);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_221, 0);
lean_dec(x_226);
x_227 = 0;
x_228 = lean_box(x_227);
lean_ctor_set(x_221, 0, x_228);
return x_221;
}
else
{
lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_221, 1);
lean_inc(x_229);
lean_dec(x_221);
x_230 = 0;
x_231 = lean_box(x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_229);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_233 = lean_ctor_get(x_221, 1);
lean_inc(x_233);
lean_dec(x_221);
x_234 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_220, x_2, x_3, x_4, x_5, x_233);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_unbox(x_235);
lean_dec(x_235);
if (x_236 == 0)
{
uint8_t x_237; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_237 = !lean_is_exclusive(x_234);
if (x_237 == 0)
{
lean_object* x_238; uint8_t x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_234, 0);
lean_dec(x_238);
x_239 = 0;
x_240 = lean_box(x_239);
lean_ctor_set(x_234, 0, x_240);
return x_234;
}
else
{
lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_234, 1);
lean_inc(x_241);
lean_dec(x_234);
x_242 = 0;
x_243 = lean_box(x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_241);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_245 = lean_ctor_get(x_234, 1);
lean_inc(x_245);
lean_dec(x_234);
x_246 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__6;
x_247 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_220, x_246, x_2, x_3, x_4, x_5, x_245);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
lean_object* x_249; uint8_t x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_247, 0);
lean_dec(x_249);
x_250 = 0;
x_251 = lean_box(x_250);
lean_ctor_set(x_247, 0, x_251);
return x_247;
}
else
{
lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_247, 1);
lean_inc(x_252);
lean_dec(x_247);
x_253 = 0;
x_254 = lean_box(x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_252);
return x_255;
}
}
}
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_136);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_137);
if (x_256 == 0)
{
return x_137;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_137, 0);
x_258 = lean_ctor_get(x_137, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_137);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
default: 
{
uint8_t x_260; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_260 = !lean_is_exclusive(x_7);
if (x_260 == 0)
{
lean_object* x_261; uint8_t x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_7, 0);
lean_dec(x_261);
x_262 = 0;
x_263 = lean_box(x_262);
lean_ctor_set(x_7, 0, x_263);
return x_7;
}
else
{
lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_7, 1);
lean_inc(x_264);
lean_dec(x_7);
x_265 = 0;
x_266 = lean_box(x_265);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_264);
return x_267;
}
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_268 = !lean_is_exclusive(x_7);
if (x_268 == 0)
{
return x_7;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_7, 0);
x_270 = lean_ctor_get(x_7, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_7);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
}
LEAN_EXPORT lean_object* lean_synth_pending(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
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
x_17 = lean_nat_dec_eq(x_9, x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_4, 8);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 7);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 6);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 5);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 4);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 3);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_4, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_4, 0);
lean_dec(x_27);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_9, x_28);
lean_dec(x_9);
lean_ctor_set(x_4, 1, x_29);
x_30 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_9, x_31);
lean_dec(x_9);
x_33 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_10);
lean_ctor_set(x_33, 3, x_11);
lean_ctor_set(x_33, 4, x_12);
lean_ctor_set(x_33, 5, x_13);
lean_ctor_set(x_33, 6, x_14);
lean_ctor_set(x_33, 7, x_15);
lean_ctor_set(x_33, 8, x_16);
x_34 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_7, x_2, x_3, x_33, x_5, x_6);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_35 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2(x_11, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_7767_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___lambda__2___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__8;
x_9 = l_Lean_registerTraceClass(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_12 = l_Lean_registerTraceClass(x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__2;
x_15 = l_Lean_registerTraceClass(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Meta_SynthInstance_resume___closed__5;
x_18 = l_Lean_registerTraceClass(x_17, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_21 = l_Lean_registerTraceClass(x_20, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___lambda__2___closed__2;
x_24 = l_Lean_registerTraceClass(x_23, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__2;
x_27 = l_Lean_registerTraceClass(x_26, x_25);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
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
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
return x_15;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_12);
if (x_44 == 0)
{
return x_12;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_12);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_9);
if (x_48 == 0)
{
return x_9;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_9, 0);
x_50 = lean_ctor_get(x_9, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_9);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_6);
if (x_52 == 0)
{
return x_6;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_6, 0);
x_54 = lean_ctor_get(x_6, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_6);
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
x_56 = !lean_is_exclusive(x_3);
if (x_56 == 0)
{
return x_3;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_3, 0);
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_3);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
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
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_synthInstance_maxHeartbeats = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_synthInstance_maxHeartbeats);
lean_dec_ref(res);
}l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33____closed__4);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_33_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_synthInstance_maxSize = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_synthInstance_maxSize);
lean_dec_ref(res);
}l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__1 = _init_l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getMaxHeartbeats___closed__1);
l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__1 = _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__1);
l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__2 = _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__2);
l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__3 = _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__3);
l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__4 = _init_l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__4);
if (builtin) {res = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_SynthInstance_inferTCGoalsRLAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_SynthInstance_inferTCGoalsRLAttr);
lean_dec_ref(res);
}l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1 = _init_l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_hasInferTCGoalsRLAttribute___closed__1);
l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1 = _init_l_Lean_Meta_SynthInstance_instInhabitedGeneratorNode___closed__1();
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
l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1 = _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__1);
l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2 = _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_normLevel___closed__2);
l_Lean_Meta_SynthInstance_mkTableKey___closed__1 = _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKey___closed__1);
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
l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__3);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__4 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_SynthInstance_getInstances___spec__6___closed__4);
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
l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__9 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__9);
l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__10 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__10);
l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__1 = _init_l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__1);
l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__2 = _init_l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__2);
l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__3 = _init_l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__3);
l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__4 = _init_l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__4);
l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__5 = _init_l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__5);
l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__6 = _init_l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__9___closed__6);
l_Lean_Meta_SynthInstance_newSubgoal___lambda__3___closed__1 = _init_l_Lean_Meta_SynthInstance_newSubgoal___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___lambda__3___closed__1);
l_Lean_Meta_SynthInstance_newSubgoal___closed__1 = _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___closed__1);
l_Lean_Meta_SynthInstance_newSubgoal___closed__2 = _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___closed__2);
l_Lean_Meta_SynthInstance_newSubgoal___closed__3 = _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___closed__3);
l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1___closed__1 = _init_l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_SynthInstance_getEntry___spec__1___closed__1);
l_Lean_Meta_SynthInstance_getEntry___closed__1 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__1);
l_Lean_Meta_SynthInstance_getEntry___closed__2 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__2);
l_Lean_Meta_SynthInstance_getEntry___closed__3 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__3);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__2 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__2);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__3 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__3);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__4 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__4);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__5 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__5);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__6 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__6);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__7 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__7);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__1 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__1);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__2 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__2);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__3 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__3);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__4 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___closed__4);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__2);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__3 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg___closed__3);
l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__1);
l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___closed__2);
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
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__1 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__1);
l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__2 = _init_l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__2);
l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_addAnswer___closed__1 = _init_l_Lean_Meta_SynthInstance_addAnswer___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___closed__1);
l_Lean_Meta_SynthInstance_addAnswer___closed__2 = _init_l_Lean_Meta_SynthInstance_addAnswer___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___closed__2);
l_Lean_Meta_SynthInstance_addAnswer___closed__3 = _init_l_Lean_Meta_SynthInstance_addAnswer___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___closed__3);
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
l_Lean_Meta_SynthInstance_generate___closed__1 = _init_l_Lean_Meta_SynthInstance_generate___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__1);
l_Lean_Meta_SynthInstance_generate___closed__2 = _init_l_Lean_Meta_SynthInstance_generate___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__2);
l_Lean_Meta_SynthInstance_generate___closed__3 = _init_l_Lean_Meta_SynthInstance_generate___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__3);
l_Lean_Meta_SynthInstance_generate___closed__4 = _init_l_Lean_Meta_SynthInstance_generate___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__4);
l_Lean_Meta_SynthInstance_getNextToResume___rarg___closed__1 = _init_l_Lean_Meta_SynthInstance_getNextToResume___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getNextToResume___rarg___closed__1);
l_Lean_Meta_SynthInstance_resume___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_resume___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_resume___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_resume___closed__1 = _init_l_Lean_Meta_SynthInstance_resume___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__1);
l_Lean_Meta_SynthInstance_resume___closed__2 = _init_l_Lean_Meta_SynthInstance_resume___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__2);
l_Lean_Meta_SynthInstance_resume___closed__3 = _init_l_Lean_Meta_SynthInstance_resume___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__3);
l_Lean_Meta_SynthInstance_resume___closed__4 = _init_l_Lean_Meta_SynthInstance_resume___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__4);
l_Lean_Meta_SynthInstance_resume___closed__5 = _init_l_Lean_Meta_SynthInstance_resume___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__5);
l_Lean_Meta_SynthInstance_resume___closed__6 = _init_l_Lean_Meta_SynthInstance_resume___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__6);
l_Lean_Meta_SynthInstance_resume___closed__7 = _init_l_Lean_Meta_SynthInstance_resume___closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__7);
l_Lean_Meta_SynthInstance_synth___closed__1 = _init_l_Lean_Meta_SynthInstance_synth___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___closed__1);
l_Lean_Meta_SynthInstance_synth___closed__2 = _init_l_Lean_Meta_SynthInstance_synth___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___closed__2);
l_Lean_Meta_SynthInstance_synth___closed__3 = _init_l_Lean_Meta_SynthInstance_synth___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___closed__3);
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
l_Lean_Meta_SynthInstance_main___lambda__2___closed__1 = _init_l_Lean_Meta_SynthInstance_main___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lambda__2___closed__1);
l_Lean_Meta_SynthInstance_main___lambda__2___closed__2 = _init_l_Lean_Meta_SynthInstance_main___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lambda__2___closed__2);
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
l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__1 = _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__1();
l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2 = _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_synthInstance_x3f___spec__2___closed__2();
l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Meta_synthInstance_x3f___spec__5___closed__1);
l_Lean_Meta_synthInstance_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_synthInstance_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__2___closed__1);
l_Lean_Meta_synthInstance_x3f___lambda__2___closed__2 = _init_l_Lean_Meta_synthInstance_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__2___closed__2);
l_Lean_Meta_synthInstance_x3f___lambda__2___closed__3 = _init_l_Lean_Meta_synthInstance_x3f___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__2___closed__3);
l_Lean_Meta_synthInstance_x3f___lambda__2___closed__4 = _init_l_Lean_Meta_synthInstance_x3f___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__2___closed__4);
l_Lean_Meta_synthInstance_x3f___lambda__4___closed__1 = _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__4___closed__1);
l_Lean_Meta_synthInstance_x3f___lambda__4___closed__2 = _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__4___closed__2);
l_Lean_Meta_synthInstance_x3f___lambda__4___closed__3 = _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__4___closed__3);
l_Lean_Meta_synthInstance_x3f___lambda__4___closed__4 = _init_l_Lean_Meta_synthInstance_x3f___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__4___closed__4);
l_Lean_Meta_synthInstance_x3f___lambda__5___closed__1 = _init_l_Lean_Meta_synthInstance_x3f___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__5___closed__1);
l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2 = _init_l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__5___closed__2);
l_Lean_Meta_synthInstance_x3f___lambda__5___closed__3 = _init_l_Lean_Meta_synthInstance_x3f___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___lambda__5___closed__3);
l_Lean_Meta_synthInstance_x3f___closed__1 = _init_l_Lean_Meta_synthInstance_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__1);
l_Lean_Meta_trySynthInstance___closed__1 = _init_l_Lean_Meta_trySynthInstance___closed__1();
lean_mark_persistent(l_Lean_Meta_trySynthInstance___closed__1);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___closed__1);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___closed__2);
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
res = l_Lean_Meta_initFn____x40_Lean_Meta_SynthInstance___hyg_7767_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

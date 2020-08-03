// Lean compiler output
// Module: Lean.Meta.SynthInstance
// Imports: Init Lean.Meta.Basic Lean.Meta.Instances Lean.Meta.LevelDefEq Lean.Meta.AbstractMVars Lean.Meta.WHNF
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
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessOutParam___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__51;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__3;
lean_object* l___private_Lean_Meta_SynthInstance_2__preprocess(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1(lean_object*, lean_object*);
uint8_t lean_is_out_param(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_addAnswer(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getTop(lean_object*);
lean_object* l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_toLOption___rarg(lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___closed__5;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_addAnswer___closed__1;
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__7;
lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__3;
lean_object* l___private_Lean_Meta_SynthInstance_7__regTraceClasses(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_addAnswer___closed__2;
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocessLevels___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getResult(lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_maxStepsOption___closed__5;
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
lean_object* l_Lean_Meta_synthPendingImp(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessOutParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___closed__3;
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getTraceState___boxed(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__1;
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_maxStepsOption(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_11__regTraceClasses___closed__2;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Answer_inhabited;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_withMCtx(lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__6(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5;
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__2;
lean_object* l_Lean_Meta_SynthInstance_main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2;
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_maxStepsOption___closed__3;
lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3;
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_synthInstance_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__5;
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__73;
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVarsResult_inhabited___closed__1;
lean_object* l_Lean_Meta_setSynthPendingRef___closed__1;
uint8_t l_Lean_Meta_SynthInstance_Waiter_isRoot(lean_object*);
extern lean_object* l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_meta2Synth(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getTop___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__6;
lean_object* l_Lean_Meta_SynthInstance_getTraceState(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5___boxed(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l_Lean_Meta_SynthInstance_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___closed__3;
lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_main___spec__1(lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__5;
lean_object* l_Lean_Meta_SynthInstance_meta2Synth___closed__1;
lean_object* l_Lean_Meta_SynthInstance_addContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tracer___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__7;
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_modifyTop(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__6___rarg(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__2;
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_GeneratorNode_inhabited;
lean_object* l_Lean_Meta_SynthInstance_getTraceState___rarg(lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___boxed(lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__2(lean_object*);
lean_object* l_Lean_Meta_getGlobalInstances___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getOptions___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__4;
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__4;
extern size_t l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1;
lean_object* l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__1(lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l_Lean_Meta_SynthInstance_step(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setSynthPendingRef(lean_object*);
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__9;
size_t lean_usize_modn(size_t, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__5;
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__3;
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getNextToResume___boxed(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__7;
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_2__preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___closed__4;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1___boxed(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Meta_SynthInstance_getResult___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__4;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4;
lean_object* l_Lean_Meta_SynthInstance_getEntry(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___closed__6;
lean_object* l_Lean_Meta_SynthInstance_synth(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__2;
uint8_t l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__1;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__2;
lean_object* l_Lean_Meta_synthInstance_x3f___closed__3;
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocessLevels(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__5;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2;
lean_object* l_Lean_Meta_SynthInstance_wakeUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_withMCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1;
lean_object* l_Lean_Meta_SynthInstance_getTop___rarg(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__6;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__3;
uint8_t l_Lean_Meta_SynthInstance_isNewAnswer(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__6;
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__1;
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__6(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__8;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
lean_object* l_Std_PersistentArray_toArray___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_addContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Waiter_isRoot___boxed(lean_object*);
extern lean_object* l_Lean_Meta_synthPendingRef;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_incDepth(lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getResult___boxed(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__2;
lean_object* l_Lean_Meta_SynthInstance_tracer;
lean_object* l_Lean_Meta_SynthInstance_mkTableKey(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_6__getMaxSteps(lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__72;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__4;
lean_object* l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getNextToResume(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_isNewAnswer___boxed(lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isLevelAssignable(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__9;
lean_object* l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__3;
lean_object* l_Lean_Meta_SynthInstance_Consumernode_inhabited;
extern lean_object* l_Lean_Meta_isLevelDefEq___closed__9;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2;
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_modifyTop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_6__getMaxSteps___boxed(lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___closed__2;
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Meta_SynthInstance_generate___closed__1;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__1;
lean_object* l_Lean_Meta_maxStepsOption___closed__1;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1;
lean_object* l_Lean_Meta_maxStepsOption___closed__2;
lean_object* l_Lean_Meta_SynthInstance_getInstances___closed__1;
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___boxed(lean_object*);
extern lean_object* l_Lean_Meta_Exception_Inhabited___closed__2;
uint8_t l_Lean_MetavarContext_isExprAssignable(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1;
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_SynthInstance_liftMeta___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TagAttribute_Inhabited___closed__3;
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
lean_object* l_Lean_Meta_SynthInstance_consume(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__4;
lean_object* l_Lean_Meta_synthInstance_x3f___closed__2;
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2;
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3;
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__1;
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__2;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryAnswer___closed__1;
lean_object* l_Lean_Meta_SynthInstance_main___closed__2;
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tracer___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_has_out_params(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__2;
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__8;
lean_object* l_Lean_Meta_SynthInstance_generate___closed__4;
lean_object* l_Lean_Meta_SynthInstance_main___closed__1;
lean_object* l_Lean_Meta_SynthInstance_resume___closed__1;
lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__3;
lean_object* l_Lean_Meta_maxStepsOption___closed__4;
lean_object* l_Lean_Meta_SynthInstance_liftMeta(lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inferTCGoalsLR");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instruct type class resolution procedure to solve goals from left to right for this instance");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2;
x_3 = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3;
x_4 = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Expr_Inhabited___closed__1;
x_2 = l_Lean_MetavarContext_Inhabited___closed__1;
x_3 = l_Array_empty___closed__1;
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
lean_object* _init_l_Lean_Meta_SynthInstance_GeneratorNode_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_Inhabited___closed__1;
x_3 = l_Lean_MetavarContext_Inhabited___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_Consumernode_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1;
return x_1;
}
}
uint8_t l_Lean_Meta_SynthInstance_Waiter_isRoot(lean_object* x_1) {
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
lean_object* l_Lean_Meta_SynthInstance_Waiter_isRoot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SynthInstance_Waiter_isRoot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_4, x_1);
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_name_eq(x_4, x_1);
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
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
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
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__7(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
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
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(x_1, x_2, x_7);
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
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(x_1, x_2, x_12);
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
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(x_13, x_15);
return x_17;
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
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_tc");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_6, x_2, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_level_update_succ(x_1, x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_level_update_succ(x_1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_2);
x_17 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_15, x_2, x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_16, x_2, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_level_update_max(x_1, x_18, x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_level_update_max(x_1, x_18, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
case 3:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_2);
x_30 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_28, x_2, x_3);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_29, x_2, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_level_update_imax(x_1, x_31, x_35);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_level_update_imax(x_1, x_31, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
case 5:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = l_Lean_MetavarContext_isLevelAssignable(x_2, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_3);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
x_47 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(x_45, x_41);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_3, 2);
lean_dec(x_49);
x_50 = lean_ctor_get(x_3, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_3, 0);
lean_dec(x_51);
x_52 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2;
lean_inc(x_44);
x_53 = lean_name_mk_numeral(x_52, x_44);
x_54 = l_Lean_mkLevelParam(x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_44, x_55);
lean_dec(x_44);
lean_inc(x_54);
x_57 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(x_45, x_41, x_54);
lean_ctor_set(x_3, 1, x_57);
lean_ctor_set(x_3, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_3);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
x_59 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2;
lean_inc(x_44);
x_60 = lean_name_mk_numeral(x_59, x_44);
x_61 = l_Lean_mkLevelParam(x_60);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_44, x_62);
lean_dec(x_44);
lean_inc(x_61);
x_64 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(x_45, x_41, x_61);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_46);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_41);
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_3);
return x_68;
}
}
}
default: 
{
lean_object* x_69; 
lean_dec(x_2);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_3);
return x_69;
}
}
}
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_4, x_1);
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_name_eq(x_4, x_1);
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
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
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
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__7(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
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
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(x_1, x_2, x_7);
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
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(x_1, x_2, x_12);
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
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(x_13, x_15);
return x_17;
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
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_7, x_2, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(x_8, x_2, x_11);
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
x_20 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_18, x_2, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(x_19, x_2, x_22);
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
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(x_11, x_6);
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
x_17 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2;
lean_inc(x_9);
x_18 = lean_name_mk_numeral(x_17, x_9);
x_19 = l_Lean_mkFVar(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_9, x_20);
lean_dec(x_9);
lean_inc(x_19);
x_22 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(x_11, x_6, x_19);
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
x_24 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2;
lean_inc(x_9);
x_25 = lean_name_mk_numeral(x_24, x_9);
x_26 = l_Lean_mkFVar(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_9, x_27);
lean_dec(x_9);
lean_inc(x_26);
x_29 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(x_11, x_6, x_26);
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
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_34, x_2, x_3);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_expr_update_sort(x_1, x_37);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_expr_update_sort(x_1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
case 4:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(x_43, x_2, x_3);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_expr_update_const(x_1, x_46);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_expr_update_const(x_1, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
case 5:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_inc(x_2);
x_54 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_52, x_2, x_3);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_53, x_2, x_56);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_expr_update_app(x_1, x_55, x_59);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_57, 0);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_57);
x_63 = lean_expr_update_app(x_1, x_55, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
case 6:
{
lean_object* x_65; lean_object* x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 2);
lean_inc(x_66);
x_67 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_2);
x_68 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_65, x_2, x_3);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_66, x_2, x_70);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = (uint8_t)((x_67 << 24) >> 61);
x_75 = lean_expr_update_lambda(x_1, x_74, x_69, x_73);
lean_ctor_set(x_71, 0, x_75);
return x_71;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_71, 0);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_71);
x_78 = (uint8_t)((x_67 << 24) >> 61);
x_79 = lean_expr_update_lambda(x_1, x_78, x_69, x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
case 7:
{
lean_object* x_81; lean_object* x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_1, 2);
lean_inc(x_82);
x_83 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_2);
x_84 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_81, x_2, x_3);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_82, x_2, x_86);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = (uint8_t)((x_83 << 24) >> 61);
x_91 = lean_expr_update_forall(x_1, x_90, x_85, x_89);
lean_ctor_set(x_87, 0, x_91);
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_87, 0);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_87);
x_94 = (uint8_t)((x_83 << 24) >> 61);
x_95 = lean_expr_update_forall(x_1, x_94, x_85, x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
}
case 8:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_97 = lean_ctor_get(x_1, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_1, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 3);
lean_inc(x_99);
lean_inc(x_2);
x_100 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_97, x_2, x_3);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_2);
x_103 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_98, x_2, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_99, x_2, x_105);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_expr_update_let(x_1, x_101, x_104, x_108);
lean_ctor_set(x_106, 0, x_109);
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
x_112 = lean_expr_update_let(x_1, x_101, x_104, x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
case 10:
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_1, 1);
lean_inc(x_114);
x_115 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_114, x_2, x_3);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_expr_update_mdata(x_1, x_117);
lean_ctor_set(x_115, 0, x_118);
return x_115;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_115, 0);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_115);
x_121 = lean_expr_update_mdata(x_1, x_119);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
case 11:
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_1, 2);
lean_inc(x_123);
x_124 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_123, x_2, x_3);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_expr_update_proj(x_1, x_126);
lean_ctor_set(x_124, 0, x_127);
return x_124;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_124, 0);
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_124);
x_130 = lean_expr_update_proj(x_1, x_128);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
default: 
{
lean_object* x_132; 
lean_dec(x_2);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_132, 1, x_3);
return x_132;
}
}
}
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_SynthInstance_mkTableKey___closed__1;
x_3 = l_Lean_Meta_SynthInstance_mkTableKey___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_mkTableKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_SynthInstance_mkTableKey___closed__3;
x_4 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_2, x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_AbstractMVarsResult_inhabited___closed__1;
x_2 = l_Lean_Expr_Inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_Answer_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_SynthM_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_Inhabited___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_SynthM_inhabited___closed__1;
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_getTraceState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_getTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getTraceState___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_getTraceState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_getTraceState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_Lean_Meta_SynthInstance_getOptions___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_getOptions(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_addContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_9);
x_11 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
lean_object* l_Lean_Meta_SynthInstance_addContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_addContext(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_tracer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_5, 4, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
x_16 = lean_ctor_get(x_5, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_17 = lean_apply_1(x_1, x_15);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_17);
lean_ctor_set(x_18, 5, x_16);
lean_ctor_set(x_3, 0, x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_21, 5);
lean_inc(x_31);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 x_32 = x_21;
} else {
 lean_dec_ref(x_21);
 x_32 = lean_box(0);
}
x_33 = lean_apply_1(x_1, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_31);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set(x_35, 2, x_23);
lean_ctor_set(x_35, 3, x_24);
lean_ctor_set(x_35, 4, x_25);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tracer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getOptions___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tracer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tracer___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tracer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getTraceState___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tracer___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_addContext___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tracer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_SynthInstance_tracer___closed__1;
x_2 = l_Lean_Meta_SynthInstance_tracer___closed__2;
x_3 = l_Lean_Meta_SynthInstance_tracer___closed__3;
x_4 = l_Lean_Meta_SynthInstance_tracer___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tracer() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_tracer___closed__5;
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_tracer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_tracer___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_liftMeta___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_apply_2(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_3, 0, x_8);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_3, 0, x_13);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get(x_3, 2);
x_20 = lean_ctor_get(x_3, 3);
x_21 = lean_ctor_get(x_3, 4);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_22 = lean_apply_2(x_1, x_2, x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_21);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_20);
lean_ctor_set(x_31, 4, x_21);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_liftMeta(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_liftMeta___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_meta2Synth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_liftMeta___rarg), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_meta2Synth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_meta2Synth___closed__1;
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_withMCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_66; 
x_8 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_6, 1, x_1);
x_66 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_67);
x_9 = x_69;
x_10 = x_68;
goto block_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_70);
x_9 = x_72;
x_10 = x_71;
goto block_65;
}
block_65:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 1);
lean_dec(x_16);
lean_ctor_set(x_11, 1, x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 2);
x_20 = lean_ctor_get(x_11, 3);
x_21 = lean_ctor_get(x_11, 4);
x_22 = lean_ctor_get(x_11, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_8);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
lean_ctor_set(x_10, 0, x_23);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_10, 1);
x_26 = lean_ctor_get(x_10, 2);
x_27 = lean_ctor_get(x_10, 3);
x_28 = lean_ctor_get(x_10, 4);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_11, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_11, 5);
lean_inc(x_33);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_34 = x_11;
} else {
 lean_dec_ref(x_11);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 6, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_8);
lean_ctor_set(x_35, 2, x_30);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_35, 5, x_33);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set(x_36, 3, x_27);
lean_ctor_set(x_36, 4, x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 0);
lean_inc(x_39);
lean_dec(x_9);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_10, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
lean_ctor_set(x_38, 1, x_8);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_10);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 2);
x_47 = lean_ctor_get(x_38, 3);
x_48 = lean_ctor_get(x_38, 4);
x_49 = lean_ctor_get(x_38, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_8);
lean_ctor_set(x_50, 2, x_46);
lean_ctor_set(x_50, 3, x_47);
lean_ctor_set(x_50, 4, x_48);
lean_ctor_set(x_50, 5, x_49);
lean_ctor_set(x_10, 0, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_10);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_10, 1);
x_53 = lean_ctor_get(x_10, 2);
x_54 = lean_ctor_get(x_10, 3);
x_55 = lean_ctor_get(x_10, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_10);
x_56 = lean_ctor_get(x_38, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_38, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_38, 3);
lean_inc(x_58);
x_59 = lean_ctor_get(x_38, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_38, 5);
lean_inc(x_60);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 x_61 = x_38;
} else {
 lean_dec_ref(x_38);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 6, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_8);
lean_ctor_set(x_62, 2, x_57);
lean_ctor_set(x_62, 3, x_58);
lean_ctor_set(x_62, 4, x_59);
lean_ctor_set(x_62, 5, x_60);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_52);
lean_ctor_set(x_63, 2, x_53);
lean_ctor_set(x_63, 3, x_54);
lean_ctor_set(x_63, 4, x_55);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_39);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_114; lean_object* x_115; 
x_73 = lean_ctor_get(x_6, 0);
x_74 = lean_ctor_get(x_6, 1);
x_75 = lean_ctor_get(x_6, 2);
x_76 = lean_ctor_get(x_6, 3);
x_77 = lean_ctor_get(x_6, 4);
x_78 = lean_ctor_get(x_6, 5);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_6);
x_114 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_114, 0, x_73);
lean_ctor_set(x_114, 1, x_1);
lean_ctor_set(x_114, 2, x_75);
lean_ctor_set(x_114, 3, x_76);
lean_ctor_set(x_114, 4, x_77);
lean_ctor_set(x_114, 5, x_78);
lean_ctor_set(x_4, 0, x_114);
x_115 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_116);
x_79 = x_118;
x_80 = x_117;
goto block_113;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_dec(x_115);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_119);
x_79 = x_121;
x_80 = x_120;
goto block_113;
}
block_113:
{
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_80, 4);
lean_inc(x_86);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 x_87 = x_80;
} else {
 lean_dec_ref(x_80);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_81, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_81, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_81, 4);
lean_inc(x_91);
x_92 = lean_ctor_get(x_81, 5);
lean_inc(x_92);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 lean_ctor_release(x_81, 5);
 x_93 = x_81;
} else {
 lean_dec_ref(x_81);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 6, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_74);
lean_ctor_set(x_94, 2, x_89);
lean_ctor_set(x_94, 3, x_90);
lean_ctor_set(x_94, 4, x_91);
lean_ctor_set(x_94, 5, x_92);
if (lean_is_scalar(x_87)) {
 x_95 = lean_alloc_ctor(0, 5, 0);
} else {
 x_95 = x_87;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_83);
lean_ctor_set(x_95, 2, x_84);
lean_ctor_set(x_95, 3, x_85);
lean_ctor_set(x_95, 4, x_86);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_82);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_97 = lean_ctor_get(x_80, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_79, 0);
lean_inc(x_98);
lean_dec(x_79);
x_99 = lean_ctor_get(x_80, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_80, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_80, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 4);
lean_inc(x_102);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 x_103 = x_80;
} else {
 lean_dec_ref(x_80);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_97, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_97, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_97, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_97, 4);
lean_inc(x_107);
x_108 = lean_ctor_get(x_97, 5);
lean_inc(x_108);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 lean_ctor_release(x_97, 2);
 lean_ctor_release(x_97, 3);
 lean_ctor_release(x_97, 4);
 lean_ctor_release(x_97, 5);
 x_109 = x_97;
} else {
 lean_dec_ref(x_97);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_74);
lean_ctor_set(x_110, 2, x_105);
lean_ctor_set(x_110, 3, x_106);
lean_ctor_set(x_110, 4, x_107);
lean_ctor_set(x_110, 5, x_108);
if (lean_is_scalar(x_103)) {
 x_111 = lean_alloc_ctor(0, 5, 0);
} else {
 x_111 = x_103;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_99);
lean_ctor_set(x_111, 2, x_100);
lean_ctor_set(x_111, 3, x_101);
lean_ctor_set(x_111, 4, x_102);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_98);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_122 = lean_ctor_get(x_4, 0);
x_123 = lean_ctor_get(x_4, 1);
x_124 = lean_ctor_get(x_4, 2);
x_125 = lean_ctor_get(x_4, 3);
x_126 = lean_ctor_get(x_4, 4);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_4);
x_127 = lean_ctor_get(x_122, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_122, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_122, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_122, 4);
lean_inc(x_131);
x_132 = lean_ctor_get(x_122, 5);
lean_inc(x_132);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 lean_ctor_release(x_122, 4);
 lean_ctor_release(x_122, 5);
 x_133 = x_122;
} else {
 lean_dec_ref(x_122);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_169 = lean_alloc_ctor(0, 6, 0);
} else {
 x_169 = x_133;
}
lean_ctor_set(x_169, 0, x_127);
lean_ctor_set(x_169, 1, x_1);
lean_ctor_set(x_169, 2, x_129);
lean_ctor_set(x_169, 3, x_130);
lean_ctor_set(x_169, 4, x_131);
lean_ctor_set(x_169, 5, x_132);
x_170 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_123);
lean_ctor_set(x_170, 2, x_124);
lean_ctor_set(x_170, 3, x_125);
lean_ctor_set(x_170, 4, x_126);
x_171 = lean_apply_2(x_2, x_3, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_172);
x_134 = x_174;
x_135 = x_173;
goto block_168;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_171, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_dec(x_171);
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_175);
x_134 = x_177;
x_135 = x_176;
goto block_168;
}
block_168:
{
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 4);
lean_inc(x_141);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 x_142 = x_135;
} else {
 lean_dec_ref(x_135);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_136, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_136, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_136, 3);
lean_inc(x_145);
x_146 = lean_ctor_get(x_136, 4);
lean_inc(x_146);
x_147 = lean_ctor_get(x_136, 5);
lean_inc(x_147);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 lean_ctor_release(x_136, 3);
 lean_ctor_release(x_136, 4);
 lean_ctor_release(x_136, 5);
 x_148 = x_136;
} else {
 lean_dec_ref(x_136);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 6, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_128);
lean_ctor_set(x_149, 2, x_144);
lean_ctor_set(x_149, 3, x_145);
lean_ctor_set(x_149, 4, x_146);
lean_ctor_set(x_149, 5, x_147);
if (lean_is_scalar(x_142)) {
 x_150 = lean_alloc_ctor(0, 5, 0);
} else {
 x_150 = x_142;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_138);
lean_ctor_set(x_150, 2, x_139);
lean_ctor_set(x_150, 3, x_140);
lean_ctor_set(x_150, 4, x_141);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_137);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_152 = lean_ctor_get(x_135, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_134, 0);
lean_inc(x_153);
lean_dec(x_134);
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_135, 2);
lean_inc(x_155);
x_156 = lean_ctor_get(x_135, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_135, 4);
lean_inc(x_157);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 x_158 = x_135;
} else {
 lean_dec_ref(x_135);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_152, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_152, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_152, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_152, 4);
lean_inc(x_162);
x_163 = lean_ctor_get(x_152, 5);
lean_inc(x_163);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 lean_ctor_release(x_152, 2);
 lean_ctor_release(x_152, 3);
 lean_ctor_release(x_152, 4);
 lean_ctor_release(x_152, 5);
 x_164 = x_152;
} else {
 lean_dec_ref(x_152);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(0, 6, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_128);
lean_ctor_set(x_165, 2, x_160);
lean_ctor_set(x_165, 3, x_161);
lean_ctor_set(x_165, 4, x_162);
lean_ctor_set(x_165, 5, x_163);
if (lean_is_scalar(x_158)) {
 x_166 = lean_alloc_ctor(0, 5, 0);
} else {
 x_166 = x_158;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_154);
lean_ctor_set(x_166, 2, x_155);
lean_ctor_set(x_166, 3, x_156);
lean_ctor_set(x_166, 4, x_157);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_153);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_withMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_withMCtx___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
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
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_7, x_2, x_11);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_18, x_2, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.SynthInstance");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("global instance is not a constant");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
x_2 = lean_unsigned_to_nat(193u);
x_3 = lean_unsigned_to_nat(13u);
x_4 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_25; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_25 = x_9;
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_26, x_3, x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_expr_update_const(x_25, x_29);
lean_ctor_set(x_27, 0, x_30);
x_12 = x_27;
goto block_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_expr_update_const(x_25, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_12 = x_34;
goto block_24;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_25);
x_35 = l_Lean_Meta_isClassQuick___main___closed__1;
x_36 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3;
x_37 = lean_panic_fn(x_35, x_36);
lean_inc(x_3);
x_38 = lean_apply_2(x_37, x_3, x_4);
x_12 = x_38;
goto block_24;
}
block_24:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_1, x_15);
x_17 = x_13;
x_18 = lean_array_fset(x_11, x_1, x_17);
lean_dec(x_1);
x_1 = x_16;
x_2 = x_18;
x_4 = x_14;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
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
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (x_10 == 0)
{
lean_dec(x_8);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_array_push(x_5, x_14);
x_4 = x_12;
x_5 = x_15;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (x_10 == 0)
{
lean_dec(x_8);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_array_push(x_5, x_14);
x_4 = x_12;
x_5 = x_15;
goto _start;
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_11__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__72;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("globalInstances");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Meta_isClass(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_14);
x_16 = lean_alloc_ctor(15, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = lean_alloc_ctor(15, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = l_Lean_Meta_getGlobalInstances___rarg(x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_3);
lean_inc(x_2);
x_31 = l_Lean_Meta_DiscrTree_getUnify___rarg(x_29, x_2, x_3, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = x_32;
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2), 4, 2);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_34);
x_37 = x_36;
lean_inc(x_3);
x_38 = lean_apply_2(x_37, x_3, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_64; uint8_t x_65; 
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
x_64 = lean_ctor_get(x_40, 4);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
lean_dec(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = 0;
x_42 = x_66;
x_43 = x_40;
goto block_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3;
x_68 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_67, x_3, x_40);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_42 = x_71;
x_43 = x_70;
goto block_63;
}
block_63:
{
if (x_42 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_44 = lean_ctor_get(x_3, 2);
lean_inc(x_44);
x_45 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(x_3, x_27, x_44, x_35, x_39);
lean_dec(x_44);
lean_dec(x_27);
lean_dec(x_3);
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_41);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_2);
x_48 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_51 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_39, x_35, x_50);
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3;
x_54 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_53, x_52, x_3, x_43);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_3, x_27, x_57, x_35, x_39);
lean_dec(x_57);
lean_dec(x_27);
lean_dec(x_3);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_ctor_get(x_3, 2);
lean_inc(x_60);
x_61 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_3, x_27, x_60, x_35, x_39);
lean_dec(x_60);
lean_dec(x_27);
lean_dec(x_3);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_38);
if (x_72 == 0)
{
return x_38;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_38, 0);
x_74 = lean_ctor_get(x_38, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_38);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_31);
if (x_76 == 0)
{
return x_31;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_31, 0);
x_78 = lean_ctor_get(x_31, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_31);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_5);
if (x_80 == 0)
{
return x_5;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_5, 0);
x_82 = lean_ctor_get(x_5, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_5);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_SynthInstance_getInstances___closed__1;
x_5 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SynthInstance_getInstances___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Expr_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
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
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
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
x_9 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_1, x_2, x_7);
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
x_14 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_1, x_2, x_12);
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
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_13, x_15);
return x_17;
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
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Expr_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_SynthInstance_getOptions(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_checkTraceOption(x_6, x_1);
lean_dec(x_6);
x_8 = lean_box(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = l_Lean_checkTraceOption(x_9, x_1);
lean_dec(x_9);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Lean_Meta_SynthInstance_addContext(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_7, 4);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_10);
x_19 = l_Std_PersistentArray_push___rarg(x_17, x_18);
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_box(0);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_10);
x_24 = l_Std_PersistentArray_push___rarg(x_22, x_23);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_21);
lean_ctor_set(x_7, 4, x_25);
x_26 = lean_box(0);
lean_ctor_set(x_5, 0, x_26);
return x_5;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
x_29 = lean_ctor_get(x_7, 2);
x_30 = lean_ctor_get(x_7, 3);
x_31 = lean_ctor_get(x_7, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_32 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_34 = x_8;
} else {
 lean_dec_ref(x_8);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_10);
x_36 = l_Std_PersistentArray_push___rarg(x_33, x_35);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 1, 1);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_32);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_29);
lean_ctor_set(x_38, 3, x_30);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_31);
lean_ctor_set(x_6, 0, x_38);
x_39 = lean_box(0);
lean_ctor_set(x_5, 0, x_39);
return x_5;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_40 = lean_ctor_get(x_6, 1);
x_41 = lean_ctor_get(x_6, 2);
x_42 = lean_ctor_get(x_6, 3);
x_43 = lean_ctor_get(x_6, 4);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_6);
x_44 = lean_ctor_get(x_7, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 5);
lean_inc(x_48);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_49 = x_7;
} else {
 lean_dec_ref(x_7);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_51 = lean_ctor_get(x_8, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_52 = x_8;
} else {
 lean_dec_ref(x_8);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_10);
x_54 = l_Std_PersistentArray_push___rarg(x_51, x_53);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 1, 1);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_50);
if (lean_is_scalar(x_49)) {
 x_56 = lean_alloc_ctor(0, 6, 0);
} else {
 x_56 = x_49;
}
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_45);
lean_ctor_set(x_56, 2, x_46);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set(x_56, 4, x_55);
lean_ctor_set(x_56, 5, x_48);
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_40);
lean_ctor_set(x_57, 2, x_41);
lean_ctor_set(x_57, 3, x_42);
lean_ctor_set(x_57, 4, x_43);
x_58 = lean_box(0);
lean_ctor_set(x_5, 1, x_57);
lean_ctor_set(x_5, 0, x_58);
return x_5;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_59 = lean_ctor_get(x_5, 0);
lean_inc(x_59);
lean_dec(x_5);
x_60 = lean_ctor_get(x_6, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_6, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_6, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_6, 4);
lean_inc(x_63);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_64 = x_6;
} else {
 lean_dec_ref(x_6);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_7, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_7, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_7, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_7, 5);
lean_inc(x_69);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_70 = x_7;
} else {
 lean_dec_ref(x_7);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_72 = lean_ctor_get(x_8, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_73 = x_8;
} else {
 lean_dec_ref(x_8);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_59);
x_75 = l_Std_PersistentArray_push___rarg(x_72, x_74);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 1, 1);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_71);
if (lean_is_scalar(x_70)) {
 x_77 = lean_alloc_ctor(0, 6, 0);
} else {
 x_77 = x_70;
}
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_66);
lean_ctor_set(x_77, 2, x_67);
lean_ctor_set(x_77, 3, x_68);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set(x_77, 5, x_69);
if (lean_is_scalar(x_64)) {
 x_78 = lean_alloc_ctor(0, 5, 0);
} else {
 x_78 = x_64;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_60);
lean_ctor_set(x_78, 2, x_61);
lean_ctor_set(x_78, 3, x_62);
lean_ctor_set(x_78, 4, x_63);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("newSubgoal");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 4);
lean_inc(x_11);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_12 = x_6;
} else {
 lean_dec_ref(x_6);
 x_12 = lean_box(0);
}
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_72; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_14 = lean_ctor_get(x_7, 1);
lean_ctor_set(x_7, 1, x_1);
x_146 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_146, 0, x_7);
lean_ctor_set(x_146, 1, x_8);
lean_ctor_set(x_146, 2, x_9);
lean_ctor_set(x_146, 3, x_10);
lean_ctor_set(x_146, 4, x_11);
x_147 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get_uint8(x_148, sizeof(void*)*1);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_72 = x_150;
goto block_145;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
lean_dec(x_147);
x_152 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_153 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_152, x_5, x_151);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_72 = x_156;
goto block_145;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_dec(x_153);
lean_inc(x_2);
x_158 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_158, 0, x_2);
x_159 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_152, x_158, x_5, x_157);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_72 = x_160;
goto block_145;
}
}
block_71:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 1);
lean_dec(x_22);
lean_ctor_set(x_17, 1, x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 2);
x_26 = lean_ctor_get(x_17, 3);
x_27 = lean_ctor_get(x_17, 4);
x_28 = lean_ctor_get(x_17, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_14);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set(x_16, 0, x_29);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_16);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_31 = lean_ctor_get(x_16, 1);
x_32 = lean_ctor_get(x_16, 2);
x_33 = lean_ctor_get(x_16, 3);
x_34 = lean_ctor_get(x_16, 4);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_35 = lean_ctor_get(x_17, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_17, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_17, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_17, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_17, 5);
lean_inc(x_39);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 x_40 = x_17;
} else {
 lean_dec_ref(x_17);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 6, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_14);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_41, 5, x_39);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_32);
lean_ctor_set(x_42, 3, x_33);
lean_ctor_set(x_42, 4, x_34);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_18);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_16, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_15, 0);
lean_inc(x_45);
lean_dec(x_15);
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_16, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_44, 1);
lean_dec(x_49);
lean_ctor_set(x_44, 1, x_14);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_16);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_44, 0);
x_52 = lean_ctor_get(x_44, 2);
x_53 = lean_ctor_get(x_44, 3);
x_54 = lean_ctor_get(x_44, 4);
x_55 = lean_ctor_get(x_44, 5);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_44);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_14);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set(x_56, 3, x_53);
lean_ctor_set(x_56, 4, x_54);
lean_ctor_set(x_56, 5, x_55);
lean_ctor_set(x_16, 0, x_56);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_16);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_58 = lean_ctor_get(x_16, 1);
x_59 = lean_ctor_get(x_16, 2);
x_60 = lean_ctor_get(x_16, 3);
x_61 = lean_ctor_get(x_16, 4);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_16);
x_62 = lean_ctor_get(x_44, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_44, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_44, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_44, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 5);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 lean_ctor_release(x_44, 4);
 lean_ctor_release(x_44, 5);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 6, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_14);
lean_ctor_set(x_68, 2, x_63);
lean_ctor_set(x_68, 3, x_64);
lean_ctor_set(x_68, 4, x_65);
lean_ctor_set(x_68, 5, x_66);
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_58);
lean_ctor_set(x_69, 2, x_59);
lean_ctor_set(x_69, 3, x_60);
lean_ctor_set(x_69, 4, x_61);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_45);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
block_145:
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
x_76 = lean_ctor_get(x_72, 2);
x_77 = lean_ctor_get(x_72, 3);
x_78 = lean_ctor_get(x_72, 4);
lean_inc(x_5);
lean_inc(x_3);
x_79 = l_Lean_Meta_inferType(x_3, x_5, x_74);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Meta_instantiateMVars(x_80, x_5, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_SynthInstance_getInstances___closed__1;
x_86 = l_Lean_Meta_forallTelescopeReducing___rarg(x_83, x_85, x_5, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_88);
lean_ctor_set(x_72, 0, x_88);
x_90 = l_Array_isEmpty___rarg(x_87);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_72);
x_91 = lean_array_get_size(x_87);
lean_inc(x_2);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_3);
lean_ctor_set(x_92, 1, x_2);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_87);
lean_ctor_set(x_92, 4, x_91);
x_93 = l_Lean_mkOptionalNode___closed__2;
x_94 = lean_array_push(x_93, x_4);
x_95 = l_Array_empty___closed__1;
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_push(x_76, x_92);
x_98 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_78, x_2, x_96);
if (lean_is_scalar(x_12)) {
 x_99 = lean_alloc_ctor(0, 5, 0);
} else {
 x_99 = x_12;
}
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_75);
lean_ctor_set(x_99, 2, x_97);
lean_ctor_set(x_99, 3, x_77);
lean_ctor_set(x_99, 4, x_98);
x_100 = l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
x_15 = x_100;
x_16 = x_99;
goto block_71;
}
else
{
lean_object* x_101; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_101 = l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
x_15 = x_101;
x_16 = x_72;
goto block_71;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = lean_ctor_get(x_86, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_86, 1);
lean_inc(x_103);
lean_dec(x_86);
lean_ctor_set(x_72, 0, x_103);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_102);
x_15 = x_104;
x_16 = x_72;
goto block_71;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_105 = lean_ctor_get(x_79, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
lean_dec(x_79);
lean_ctor_set(x_72, 0, x_106);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_105);
x_15 = x_107;
x_16 = x_72;
goto block_71;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_72, 0);
x_109 = lean_ctor_get(x_72, 1);
x_110 = lean_ctor_get(x_72, 2);
x_111 = lean_ctor_get(x_72, 3);
x_112 = lean_ctor_get(x_72, 4);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_72);
lean_inc(x_5);
lean_inc(x_3);
x_113 = l_Lean_Meta_inferType(x_3, x_5, x_108);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Meta_instantiateMVars(x_114, x_5, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Meta_SynthInstance_getInstances___closed__1;
x_120 = l_Lean_Meta_forallTelescopeReducing___rarg(x_117, x_119, x_5, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_122);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_109);
lean_ctor_set(x_124, 2, x_110);
lean_ctor_set(x_124, 3, x_111);
lean_ctor_set(x_124, 4, x_112);
x_125 = l_Array_isEmpty___rarg(x_121);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_124);
x_126 = lean_array_get_size(x_121);
lean_inc(x_2);
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_3);
lean_ctor_set(x_127, 1, x_2);
lean_ctor_set(x_127, 2, x_123);
lean_ctor_set(x_127, 3, x_121);
lean_ctor_set(x_127, 4, x_126);
x_128 = l_Lean_mkOptionalNode___closed__2;
x_129 = lean_array_push(x_128, x_4);
x_130 = l_Array_empty___closed__1;
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_push(x_110, x_127);
x_133 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_112, x_2, x_131);
if (lean_is_scalar(x_12)) {
 x_134 = lean_alloc_ctor(0, 5, 0);
} else {
 x_134 = x_12;
}
lean_ctor_set(x_134, 0, x_122);
lean_ctor_set(x_134, 1, x_109);
lean_ctor_set(x_134, 2, x_132);
lean_ctor_set(x_134, 3, x_111);
lean_ctor_set(x_134, 4, x_133);
x_135 = l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
x_15 = x_135;
x_16 = x_134;
goto block_71;
}
else
{
lean_object* x_136; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
x_15 = x_136;
x_16 = x_124;
goto block_71;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = lean_ctor_get(x_120, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_120, 1);
lean_inc(x_138);
lean_dec(x_120);
x_139 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_109);
lean_ctor_set(x_139, 2, x_110);
lean_ctor_set(x_139, 3, x_111);
lean_ctor_set(x_139, 4, x_112);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_137);
x_15 = x_140;
x_16 = x_139;
goto block_71;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_141 = lean_ctor_get(x_113, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_113, 1);
lean_inc(x_142);
lean_dec(x_113);
x_143 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_109);
lean_ctor_set(x_143, 2, x_110);
lean_ctor_set(x_143, 3, x_111);
lean_ctor_set(x_143, 4, x_112);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_141);
x_15 = x_144;
x_16 = x_143;
goto block_71;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_202; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_161 = lean_ctor_get(x_7, 0);
x_162 = lean_ctor_get(x_7, 1);
x_163 = lean_ctor_get(x_7, 2);
x_164 = lean_ctor_get(x_7, 3);
x_165 = lean_ctor_get(x_7, 4);
x_166 = lean_ctor_get(x_7, 5);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_7);
x_242 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_242, 0, x_161);
lean_ctor_set(x_242, 1, x_1);
lean_ctor_set(x_242, 2, x_163);
lean_ctor_set(x_242, 3, x_164);
lean_ctor_set(x_242, 4, x_165);
lean_ctor_set(x_242, 5, x_166);
x_243 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_8);
lean_ctor_set(x_243, 2, x_9);
lean_ctor_set(x_243, 3, x_10);
lean_ctor_set(x_243, 4, x_11);
x_244 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get_uint8(x_245, sizeof(void*)*1);
lean_dec(x_245);
if (x_246 == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
lean_dec(x_244);
x_202 = x_247;
goto block_241;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_248 = lean_ctor_get(x_244, 1);
lean_inc(x_248);
lean_dec(x_244);
x_249 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_250 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_249, x_5, x_248);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_unbox(x_251);
lean_dec(x_251);
if (x_252 == 0)
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_253);
lean_dec(x_250);
x_202 = x_253;
goto block_241;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_250, 1);
lean_inc(x_254);
lean_dec(x_250);
lean_inc(x_2);
x_255 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_255, 0, x_2);
x_256 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_249, x_255, x_5, x_254);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec(x_256);
x_202 = x_257;
goto block_241;
}
}
block_201:
{
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 0);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_168, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_168, 4);
lean_inc(x_174);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 x_175 = x_168;
} else {
 lean_dec_ref(x_168);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_169, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_169, 2);
lean_inc(x_177);
x_178 = lean_ctor_get(x_169, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_169, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_169, 5);
lean_inc(x_180);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 lean_ctor_release(x_169, 4);
 lean_ctor_release(x_169, 5);
 x_181 = x_169;
} else {
 lean_dec_ref(x_169);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 6, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_176);
lean_ctor_set(x_182, 1, x_162);
lean_ctor_set(x_182, 2, x_177);
lean_ctor_set(x_182, 3, x_178);
lean_ctor_set(x_182, 4, x_179);
lean_ctor_set(x_182, 5, x_180);
if (lean_is_scalar(x_175)) {
 x_183 = lean_alloc_ctor(0, 5, 0);
} else {
 x_183 = x_175;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_171);
lean_ctor_set(x_183, 2, x_172);
lean_ctor_set(x_183, 3, x_173);
lean_ctor_set(x_183, 4, x_174);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_170);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_185 = lean_ctor_get(x_168, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_167, 0);
lean_inc(x_186);
lean_dec(x_167);
x_187 = lean_ctor_get(x_168, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_168, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_168, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_168, 4);
lean_inc(x_190);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 x_191 = x_168;
} else {
 lean_dec_ref(x_168);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_185, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_185, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_185, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_185, 4);
lean_inc(x_195);
x_196 = lean_ctor_get(x_185, 5);
lean_inc(x_196);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 lean_ctor_release(x_185, 4);
 lean_ctor_release(x_185, 5);
 x_197 = x_185;
} else {
 lean_dec_ref(x_185);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(0, 6, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_192);
lean_ctor_set(x_198, 1, x_162);
lean_ctor_set(x_198, 2, x_193);
lean_ctor_set(x_198, 3, x_194);
lean_ctor_set(x_198, 4, x_195);
lean_ctor_set(x_198, 5, x_196);
if (lean_is_scalar(x_191)) {
 x_199 = lean_alloc_ctor(0, 5, 0);
} else {
 x_199 = x_191;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_187);
lean_ctor_set(x_199, 2, x_188);
lean_ctor_set(x_199, 3, x_189);
lean_ctor_set(x_199, 4, x_190);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_186);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
block_241:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_202, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_202, 4);
lean_inc(x_207);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 lean_ctor_release(x_202, 3);
 lean_ctor_release(x_202, 4);
 x_208 = x_202;
} else {
 lean_dec_ref(x_202);
 x_208 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_3);
x_209 = l_Lean_Meta_inferType(x_3, x_5, x_203);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_Lean_Meta_instantiateMVars(x_210, x_5, x_211);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = l_Lean_Meta_SynthInstance_getInstances___closed__1;
x_216 = l_Lean_Meta_forallTelescopeReducing___rarg(x_213, x_215, x_5, x_214);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_218);
if (lean_is_scalar(x_208)) {
 x_220 = lean_alloc_ctor(0, 5, 0);
} else {
 x_220 = x_208;
}
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_204);
lean_ctor_set(x_220, 2, x_205);
lean_ctor_set(x_220, 3, x_206);
lean_ctor_set(x_220, 4, x_207);
x_221 = l_Array_isEmpty___rarg(x_217);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_220);
x_222 = lean_array_get_size(x_217);
lean_inc(x_2);
x_223 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_223, 0, x_3);
lean_ctor_set(x_223, 1, x_2);
lean_ctor_set(x_223, 2, x_219);
lean_ctor_set(x_223, 3, x_217);
lean_ctor_set(x_223, 4, x_222);
x_224 = l_Lean_mkOptionalNode___closed__2;
x_225 = lean_array_push(x_224, x_4);
x_226 = l_Array_empty___closed__1;
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_array_push(x_205, x_223);
x_229 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_207, x_2, x_227);
if (lean_is_scalar(x_12)) {
 x_230 = lean_alloc_ctor(0, 5, 0);
} else {
 x_230 = x_12;
}
lean_ctor_set(x_230, 0, x_218);
lean_ctor_set(x_230, 1, x_204);
lean_ctor_set(x_230, 2, x_228);
lean_ctor_set(x_230, 3, x_206);
lean_ctor_set(x_230, 4, x_229);
x_231 = l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
x_167 = x_231;
x_168 = x_230;
goto block_201;
}
else
{
lean_object* x_232; 
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_232 = l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
x_167 = x_232;
x_168 = x_220;
goto block_201;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_233 = lean_ctor_get(x_216, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_216, 1);
lean_inc(x_234);
lean_dec(x_216);
if (lean_is_scalar(x_208)) {
 x_235 = lean_alloc_ctor(0, 5, 0);
} else {
 x_235 = x_208;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_204);
lean_ctor_set(x_235, 2, x_205);
lean_ctor_set(x_235, 3, x_206);
lean_ctor_set(x_235, 4, x_207);
x_236 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_236, 0, x_233);
x_167 = x_236;
x_168 = x_235;
goto block_201;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_237 = lean_ctor_get(x_209, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_209, 1);
lean_inc(x_238);
lean_dec(x_209);
if (lean_is_scalar(x_208)) {
 x_239 = lean_alloc_ctor(0, 5, 0);
} else {
 x_239 = x_208;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_204);
lean_ctor_set(x_239, 2, x_205);
lean_ctor_set(x_239, 3, x_206);
lean_ctor_set(x_239, 4, x_207);
x_240 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_240, 0, x_237);
x_167 = x_240;
x_168 = x_239;
goto block_201;
}
}
}
}
}
lean_object* l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 4);
lean_inc(x_4);
x_5 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(x_4, x_1);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_SynthM_inhabited(lean_box(0));
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid key at synthInstance");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
x_2 = lean_unsigned_to_nat(232u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Lean_Meta_SynthInstance_getEntry___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_SynthInstance_getEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Meta_SynthInstance_getEntry___closed__1;
x_8 = l_Lean_Meta_SynthInstance_getEntry___closed__3;
x_9 = lean_panic_fn(x_7, x_8);
x_10 = lean_apply_2(x_9, x_2, x_6);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_getEntry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_getEntry(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_66; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
lean_ctor_set(x_6, 1, x_1);
lean_inc(x_3);
x_66 = l_Lean_Meta_inferType(x_2, x_3, x_6);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Meta_instantiateMVars(x_67, x_3, x_68);
lean_dec(x_3);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_ctor_set(x_4, 0, x_71);
x_72 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_70);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_9 = x_73;
x_10 = x_4;
goto block_65;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_3);
lean_dec(x_1);
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_66, 1);
lean_inc(x_75);
lean_dec(x_66);
lean_ctor_set(x_4, 0, x_75);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_74);
x_9 = x_76;
x_10 = x_4;
goto block_65;
}
block_65:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 1);
lean_dec(x_16);
lean_ctor_set(x_11, 1, x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 2);
x_20 = lean_ctor_get(x_11, 3);
x_21 = lean_ctor_get(x_11, 4);
x_22 = lean_ctor_get(x_11, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_8);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
lean_ctor_set(x_10, 0, x_23);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_10, 1);
x_26 = lean_ctor_get(x_10, 2);
x_27 = lean_ctor_get(x_10, 3);
x_28 = lean_ctor_get(x_10, 4);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_11, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_11, 5);
lean_inc(x_33);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_34 = x_11;
} else {
 lean_dec_ref(x_11);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 6, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_8);
lean_ctor_set(x_35, 2, x_30);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_35, 5, x_33);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set(x_36, 3, x_27);
lean_ctor_set(x_36, 4, x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 0);
lean_inc(x_39);
lean_dec(x_9);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_10, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
lean_ctor_set(x_38, 1, x_8);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_10);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 2);
x_47 = lean_ctor_get(x_38, 3);
x_48 = lean_ctor_get(x_38, 4);
x_49 = lean_ctor_get(x_38, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_8);
lean_ctor_set(x_50, 2, x_46);
lean_ctor_set(x_50, 3, x_47);
lean_ctor_set(x_50, 4, x_48);
lean_ctor_set(x_50, 5, x_49);
lean_ctor_set(x_10, 0, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_10);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_10, 1);
x_53 = lean_ctor_get(x_10, 2);
x_54 = lean_ctor_get(x_10, 3);
x_55 = lean_ctor_get(x_10, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_10);
x_56 = lean_ctor_get(x_38, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_38, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_38, 3);
lean_inc(x_58);
x_59 = lean_ctor_get(x_38, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_38, 5);
lean_inc(x_60);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 x_61 = x_38;
} else {
 lean_dec_ref(x_38);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 6, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_8);
lean_ctor_set(x_62, 2, x_57);
lean_ctor_set(x_62, 3, x_58);
lean_ctor_set(x_62, 4, x_59);
lean_ctor_set(x_62, 5, x_60);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_52);
lean_ctor_set(x_63, 2, x_53);
lean_ctor_set(x_63, 3, x_54);
lean_ctor_set(x_63, 4, x_55);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_39);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_118; lean_object* x_119; 
x_77 = lean_ctor_get(x_6, 0);
x_78 = lean_ctor_get(x_6, 1);
x_79 = lean_ctor_get(x_6, 2);
x_80 = lean_ctor_get(x_6, 3);
x_81 = lean_ctor_get(x_6, 4);
x_82 = lean_ctor_get(x_6, 5);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_6);
lean_inc(x_1);
x_118 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_118, 0, x_77);
lean_ctor_set(x_118, 1, x_1);
lean_ctor_set(x_118, 2, x_79);
lean_ctor_set(x_118, 3, x_80);
lean_ctor_set(x_118, 4, x_81);
lean_ctor_set(x_118, 5, x_82);
lean_inc(x_3);
x_119 = l_Lean_Meta_inferType(x_2, x_3, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_Lean_Meta_instantiateMVars(x_120, x_3, x_121);
lean_dec(x_3);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_ctor_set(x_4, 0, x_124);
x_125 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_123);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_83 = x_126;
x_84 = x_4;
goto block_117;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_3);
lean_dec(x_1);
x_127 = lean_ctor_get(x_119, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_119, 1);
lean_inc(x_128);
lean_dec(x_119);
lean_ctor_set(x_4, 0, x_128);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_127);
x_83 = x_129;
x_84 = x_4;
goto block_117;
}
block_117:
{
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_84, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_84, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 4);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 lean_ctor_release(x_84, 4);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_85, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_85, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_85, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_85, 5);
lean_inc(x_96);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 lean_ctor_release(x_85, 3);
 lean_ctor_release(x_85, 4);
 lean_ctor_release(x_85, 5);
 x_97 = x_85;
} else {
 lean_dec_ref(x_85);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 6, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_92);
lean_ctor_set(x_98, 1, x_78);
lean_ctor_set(x_98, 2, x_93);
lean_ctor_set(x_98, 3, x_94);
lean_ctor_set(x_98, 4, x_95);
lean_ctor_set(x_98, 5, x_96);
if (lean_is_scalar(x_91)) {
 x_99 = lean_alloc_ctor(0, 5, 0);
} else {
 x_99 = x_91;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_87);
lean_ctor_set(x_99, 2, x_88);
lean_ctor_set(x_99, 3, x_89);
lean_ctor_set(x_99, 4, x_90);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_86);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_101 = lean_ctor_get(x_84, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_83, 0);
lean_inc(x_102);
lean_dec(x_83);
x_103 = lean_ctor_get(x_84, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_84, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_84, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_84, 4);
lean_inc(x_106);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 lean_ctor_release(x_84, 4);
 x_107 = x_84;
} else {
 lean_dec_ref(x_84);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_101, 2);
lean_inc(x_109);
x_110 = lean_ctor_get(x_101, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_101, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_101, 5);
lean_inc(x_112);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 lean_ctor_release(x_101, 4);
 lean_ctor_release(x_101, 5);
 x_113 = x_101;
} else {
 lean_dec_ref(x_101);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 6, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_78);
lean_ctor_set(x_114, 2, x_109);
lean_ctor_set(x_114, 3, x_110);
lean_ctor_set(x_114, 4, x_111);
lean_ctor_set(x_114, 5, x_112);
if (lean_is_scalar(x_107)) {
 x_115 = lean_alloc_ctor(0, 5, 0);
} else {
 x_115 = x_107;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_103);
lean_ctor_set(x_115, 2, x_104);
lean_ctor_set(x_115, 3, x_105);
lean_ctor_set(x_115, 4, x_106);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_102);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_177; lean_object* x_178; 
x_130 = lean_ctor_get(x_4, 0);
x_131 = lean_ctor_get(x_4, 1);
x_132 = lean_ctor_get(x_4, 2);
x_133 = lean_ctor_get(x_4, 3);
x_134 = lean_ctor_get(x_4, 4);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_4);
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_130, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_130, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_130, 4);
lean_inc(x_139);
x_140 = lean_ctor_get(x_130, 5);
lean_inc(x_140);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 lean_ctor_release(x_130, 5);
 x_141 = x_130;
} else {
 lean_dec_ref(x_130);
 x_141 = lean_box(0);
}
lean_inc(x_1);
if (lean_is_scalar(x_141)) {
 x_177 = lean_alloc_ctor(0, 6, 0);
} else {
 x_177 = x_141;
}
lean_ctor_set(x_177, 0, x_135);
lean_ctor_set(x_177, 1, x_1);
lean_ctor_set(x_177, 2, x_137);
lean_ctor_set(x_177, 3, x_138);
lean_ctor_set(x_177, 4, x_139);
lean_ctor_set(x_177, 5, x_140);
lean_inc(x_3);
x_178 = l_Lean_Meta_inferType(x_2, x_3, x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = l_Lean_Meta_instantiateMVars(x_179, x_3, x_180);
lean_dec(x_3);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_131);
lean_ctor_set(x_184, 2, x_132);
lean_ctor_set(x_184, 3, x_133);
lean_ctor_set(x_184, 4, x_134);
x_185 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_182);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
x_142 = x_186;
x_143 = x_184;
goto block_176;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_3);
lean_dec(x_1);
x_187 = lean_ctor_get(x_178, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_178, 1);
lean_inc(x_188);
lean_dec(x_178);
x_189 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_131);
lean_ctor_set(x_189, 2, x_132);
lean_ctor_set(x_189, 3, x_133);
lean_ctor_set(x_189, 4, x_134);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_187);
x_142 = x_190;
x_143 = x_189;
goto block_176;
}
block_176:
{
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_143, 4);
lean_inc(x_149);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 x_150 = x_143;
} else {
 lean_dec_ref(x_143);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_144, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_144, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_144, 3);
lean_inc(x_153);
x_154 = lean_ctor_get(x_144, 4);
lean_inc(x_154);
x_155 = lean_ctor_get(x_144, 5);
lean_inc(x_155);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 lean_ctor_release(x_144, 2);
 lean_ctor_release(x_144, 3);
 lean_ctor_release(x_144, 4);
 lean_ctor_release(x_144, 5);
 x_156 = x_144;
} else {
 lean_dec_ref(x_144);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 6, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set(x_157, 1, x_136);
lean_ctor_set(x_157, 2, x_152);
lean_ctor_set(x_157, 3, x_153);
lean_ctor_set(x_157, 4, x_154);
lean_ctor_set(x_157, 5, x_155);
if (lean_is_scalar(x_150)) {
 x_158 = lean_alloc_ctor(0, 5, 0);
} else {
 x_158 = x_150;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_146);
lean_ctor_set(x_158, 2, x_147);
lean_ctor_set(x_158, 3, x_148);
lean_ctor_set(x_158, 4, x_149);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_145);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_160 = lean_ctor_get(x_143, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_142, 0);
lean_inc(x_161);
lean_dec(x_142);
x_162 = lean_ctor_get(x_143, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_143, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_143, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_143, 4);
lean_inc(x_165);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 x_166 = x_143;
} else {
 lean_dec_ref(x_143);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_160, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_160, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_160, 3);
lean_inc(x_169);
x_170 = lean_ctor_get(x_160, 4);
lean_inc(x_170);
x_171 = lean_ctor_get(x_160, 5);
lean_inc(x_171);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 lean_ctor_release(x_160, 5);
 x_172 = x_160;
} else {
 lean_dec_ref(x_160);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 6, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_167);
lean_ctor_set(x_173, 1, x_136);
lean_ctor_set(x_173, 2, x_168);
lean_ctor_set(x_173, 3, x_169);
lean_ctor_set(x_173, 4, x_170);
lean_ctor_set(x_173, 5, x_171);
if (lean_is_scalar(x_166)) {
 x_174 = lean_alloc_ctor(0, 5, 0);
} else {
 x_174 = x_166;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_162);
lean_ctor_set(x_174, 2, x_163);
lean_ctor_set(x_174, 3, x_164);
lean_ctor_set(x_174, 4, x_165);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_161);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
if (lean_obj_tag(x_8) == 7)
{
lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 2);
lean_inc(x_33);
x_34 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_35 = lean_array_get_size(x_4);
x_36 = lean_expr_instantiate_rev_range(x_32, x_5, x_35, x_4);
lean_dec(x_35);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_3);
x_37 = l_Lean_Meta_mkForall(x_3, x_36, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_Lean_Meta_mkFreshExprMVarAt(x_1, x_2, x_38, x_40, x_41, x_9, x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unsigned_to_nat(0u);
lean_inc(x_43);
x_46 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_3, x_3, x_45, x_43);
lean_inc(x_46);
x_47 = l_Lean_mkApp(x_7, x_46);
x_48 = (uint8_t)((x_34 << 24) >> 61);
x_49 = l_Lean_BinderInfo_isInstImplicit(x_48);
x_50 = lean_array_push(x_4, x_46);
if (x_49 == 0)
{
lean_dec(x_43);
x_4 = x_50;
x_7 = x_47;
x_8 = x_33;
x_10 = x_44;
goto _start;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_6);
x_4 = x_50;
x_6 = x_52;
x_7 = x_47;
x_8 = x_33;
x_10 = x_44;
goto _start;
}
}
else
{
uint8_t x_54; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_37);
if (x_54 == 0)
{
return x_37;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_37, 0);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_37);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; 
x_58 = lean_box(0);
x_11 = x_58;
goto block_31;
}
block_31:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
x_12 = lean_array_get_size(x_4);
x_13 = lean_expr_instantiate_rev_range(x_8, x_5, x_12, x_4);
lean_dec(x_5);
lean_dec(x_8);
lean_inc(x_9);
x_14 = l_Lean_Meta_whnf(x_13, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Expr_isForall(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_free_object(x_14);
x_5 = x_12;
x_8 = x_16;
x_10 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = l_Lean_Expr_isForall(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_7);
lean_ctor_set(x_24, 2, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
else
{
x_5 = x_12;
x_8 = x_21;
x_10 = x_22;
goto _start;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_SynthInstance_getSubgoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Meta_inferType(x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = l_Array_empty___closed__1;
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_13 = l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(x_1, x_2, x_3, x_11, x_12, x_10, x_4, x_8, x_5, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Expr_getAppFn___main(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
x_21 = l_Lean_TagAttribute_hasTag(x_20, x_19, x_18);
lean_dec(x_18);
lean_dec(x_19);
if (x_21 == 0)
{
return x_13;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = l_List_reverse___rarg(x_23);
lean_ctor_set(x_15, 0, x_24);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
x_27 = lean_ctor_get(x_15, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_28 = l_List_reverse___rarg(x_25);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_13, 0, x_29);
return x_13;
}
}
}
else
{
lean_dec(x_17);
return x_13;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = l_Lean_Expr_getAppFn___main(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_32) == 4)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
x_36 = l_Lean_TagAttribute_hasTag(x_35, x_34, x_33);
lean_dec(x_33);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 2);
lean_inc(x_40);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_41 = x_30;
} else {
 lean_dec_ref(x_30);
 x_41 = lean_box(0);
}
x_42 = l_List_reverse___rarg(x_38);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 3, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec(x_32);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_31);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
return x_13;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_13, 0);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_13);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_7);
if (x_50 == 0)
{
return x_7;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_7, 0);
x_52 = lean_ctor_get(x_7, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_7);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tryResolve");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failure assigning");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_5);
x_9 = l_Lean_Meta_SynthInstance_getSubgoals(x_1, x_2, x_5, x_3, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_180; uint8_t x_181; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 2);
lean_inc(x_14);
lean_dec(x_10);
x_180 = lean_ctor_get(x_11, 4);
lean_inc(x_180);
x_181 = lean_ctor_get_uint8(x_180, sizeof(void*)*1);
lean_dec(x_180);
if (x_181 == 0)
{
x_15 = x_11;
goto block_179;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_182 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_183 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_182, x_7, x_11);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_15 = x_186;
goto block_179;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
lean_dec(x_183);
lean_inc(x_6);
x_188 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_188, 0, x_6);
x_189 = l_Lean_Meta_Exception_toTraceMessageData___closed__51;
x_190 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_inc(x_14);
x_191 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_191, 0, x_14);
x_192 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_182, x_192, x_7, x_187);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_15 = x_194;
goto block_179;
}
}
block_179:
{
lean_object* x_16; 
lean_inc(x_7);
x_16 = l_Lean_Meta_isExprDefEq(x_6, x_14, x_7, x_15);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_ctor_get(x_20, 4);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
lean_dec(x_23);
if (x_24 == 0)
{
lean_dec(x_7);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_free_object(x_16);
x_25 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_26 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_25, x_7, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
lean_ctor_set(x_26, 0, x_22);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l_Lean_Meta_isLevelDefEq___closed__6;
x_35 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_25, x_34, x_7, x_33);
lean_dec(x_7);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_22);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_dec(x_16);
x_41 = lean_box(0);
x_42 = lean_ctor_get(x_40, 4);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_7);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_46 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_45, x_7, x_40);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_7);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_50 = x_46;
} else {
 lean_dec_ref(x_46);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = l_Lean_Meta_isLevelDefEq___closed__6;
x_54 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_45, x_53, x_7, x_52);
lean_dec(x_7);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_41);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_16, 1);
lean_inc(x_58);
lean_dec(x_16);
lean_inc(x_7);
x_59 = l_Lean_Meta_mkLambda(x_5, x_13, x_7, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_7);
x_62 = l_Lean_Meta_isExprDefEq(x_4, x_60, x_7, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
lean_dec(x_12);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_62, 1);
x_67 = lean_ctor_get(x_62, 0);
lean_dec(x_67);
x_68 = lean_box(0);
x_69 = lean_ctor_get(x_66, 4);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_69, sizeof(void*)*1);
lean_dec(x_69);
if (x_70 == 0)
{
lean_dec(x_7);
lean_ctor_set(x_62, 0, x_68);
return x_62;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_free_object(x_62);
x_71 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_72 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_71, x_7, x_66);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_dec(x_7);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
lean_ctor_set(x_72, 0, x_68);
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_80 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5;
x_81 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_71, x_80, x_7, x_79);
lean_dec(x_7);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
lean_ctor_set(x_81, 0, x_68);
return x_81;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_68);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_62, 1);
lean_inc(x_86);
lean_dec(x_62);
x_87 = lean_box(0);
x_88 = lean_ctor_get(x_86, 4);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_88, sizeof(void*)*1);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_7);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_86);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_92 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_91, x_7, x_86);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_7);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_96 = x_92;
} else {
 lean_dec_ref(x_92);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
lean_dec(x_92);
x_99 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5;
x_100 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_91, x_99, x_7, x_98);
lean_dec(x_7);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_87);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_62);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_62, 1);
x_106 = lean_ctor_get(x_62, 0);
lean_dec(x_106);
x_107 = lean_ctor_get(x_105, 4);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_107, sizeof(void*)*1);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_7);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_12);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_62, 0, x_111);
return x_62;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_free_object(x_62);
x_112 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_113 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_112, x_7, x_105);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
uint8_t x_116; 
lean_dec(x_7);
x_116 = !lean_is_exclusive(x_113);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_113, 1);
x_118 = lean_ctor_get(x_113, 0);
lean_dec(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_12);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_113, 0, x_121);
return x_113;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_113, 1);
lean_inc(x_122);
lean_dec(x_113);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_12);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_122);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_127 = lean_ctor_get(x_113, 1);
lean_inc(x_127);
lean_dec(x_113);
x_128 = l_Lean_Meta_isLevelDefEq___closed__9;
x_129 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_112, x_128, x_7, x_127);
lean_dec(x_7);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_129, 1);
x_132 = lean_ctor_get(x_129, 0);
lean_dec(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_12);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_129, 0, x_135);
return x_129;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
lean_dec(x_129);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_12);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_136);
return x_140;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_62, 1);
lean_inc(x_141);
lean_dec(x_62);
x_142 = lean_ctor_get(x_141, 4);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_7);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_12);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_141);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_149 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_148, x_7, x_141);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_unbox(x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_7);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_12);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
if (lean_is_scalar(x_153)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_153;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_158 = lean_ctor_get(x_149, 1);
lean_inc(x_158);
lean_dec(x_149);
x_159 = l_Lean_Meta_isLevelDefEq___closed__9;
x_160 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_148, x_159, x_7, x_158);
lean_dec(x_7);
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
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_12);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
if (lean_is_scalar(x_162)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_162;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_161);
return x_166;
}
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_12);
lean_dec(x_7);
x_167 = !lean_is_exclusive(x_62);
if (x_167 == 0)
{
return x_62;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_62, 0);
x_169 = lean_ctor_get(x_62, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_62);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_4);
x_171 = !lean_is_exclusive(x_59);
if (x_171 == 0)
{
return x_59;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_59, 0);
x_173 = lean_ctor_get(x_59, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_59);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_175 = !lean_is_exclusive(x_16);
if (x_175 == 0)
{
return x_16;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_16, 0);
x_177 = lean_ctor_get(x_16, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_16);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_195 = !lean_is_exclusive(x_9);
if (x_195 == 0)
{
return x_9;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_9, 0);
x_197 = lean_ctor_get(x_9, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_9);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1), 8, 4);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_1);
x_11 = l_Lean_Meta_forallTelescopeReducing___rarg(x_6, x_10, x_3, x_7);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 4);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
x_16 = l_Std_PersistentArray_empty___closed__3;
lean_ctor_set(x_5, 0, x_16);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_dec(x_5);
x_18 = l_Std_PersistentArray_empty___closed__3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_17);
lean_ctor_set(x_4, 4, x_19);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 2);
x_23 = lean_ctor_get(x_4, 3);
x_24 = lean_ctor_get(x_4, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_26 = x_5;
} else {
 lean_dec_ref(x_5);
 x_26 = lean_box(0);
}
x_27 = l_Std_PersistentArray_empty___closed__3;
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 1, 1);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_25);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set(x_29, 5, x_24);
lean_ctor_set(x_3, 0, x_29);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_3, 1);
x_31 = lean_ctor_get(x_3, 2);
x_32 = lean_ctor_get(x_3, 3);
x_33 = lean_ctor_get(x_3, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 5);
lean_inc(x_38);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_39 = x_4;
} else {
 lean_dec_ref(x_4);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_41 = x_5;
} else {
 lean_dec_ref(x_5);
 x_41 = lean_box(0);
}
x_42 = l_Std_PersistentArray_empty___closed__3;
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 1, 1);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_40);
if (lean_is_scalar(x_39)) {
 x_44 = lean_alloc_ctor(0, 6, 0);
} else {
 x_44 = x_39;
}
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_35);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_37);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_38);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_30);
lean_ctor_set(x_45, 2, x_31);
lean_ctor_set(x_45, 3, x_32);
lean_ctor_set(x_45, 4, x_33);
lean_ctor_set(x_2, 1, x_45);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
lean_dec(x_2);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 4);
lean_inc(x_51);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_52 = x_3;
} else {
 lean_dec_ref(x_3);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_4, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_4, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_4, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_4, 5);
lean_inc(x_57);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_58 = x_4;
} else {
 lean_dec_ref(x_4);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_60 = x_5;
} else {
 lean_dec_ref(x_5);
 x_60 = lean_box(0);
}
x_61 = l_Std_PersistentArray_empty___closed__3;
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 1, 1);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_59);
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(0, 6, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_54);
lean_ctor_set(x_63, 2, x_55);
lean_ctor_set(x_63, 3, x_56);
lean_ctor_set(x_63, 4, x_62);
lean_ctor_set(x_63, 5, x_57);
if (lean_is_scalar(x_52)) {
 x_64 = lean_alloc_ctor(0, 5, 0);
} else {
 x_64 = x_52;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_48);
lean_ctor_set(x_64, 2, x_49);
lean_ctor_set(x_64, 3, x_50);
lean_ctor_set(x_64, 4, x_51);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_47);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 4);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = l_Std_PersistentArray_toArray___rarg(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_PersistentArray_push___rarg(x_1, x_15);
lean_ctor_set(x_6, 0, x_16);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
lean_dec(x_6);
x_21 = l_Std_PersistentArray_toArray___rarg(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_PersistentArray_push___rarg(x_1, x_23);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_19);
lean_ctor_set(x_5, 4, x_25);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_33 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_34 = lean_ctor_get(x_6, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_35 = x_6;
} else {
 lean_dec_ref(x_6);
 x_35 = lean_box(0);
}
x_36 = l_Std_PersistentArray_toArray___rarg(x_34);
lean_dec(x_34);
x_37 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Std_PersistentArray_push___rarg(x_1, x_38);
if (lean_is_scalar(x_35)) {
 x_40 = lean_alloc_ctor(0, 1, 1);
} else {
 x_40 = x_35;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_33);
x_41 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_41, 5, x_32);
lean_ctor_set(x_4, 0, x_41);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_4);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_44 = lean_ctor_get(x_4, 1);
x_45 = lean_ctor_get(x_4, 2);
x_46 = lean_ctor_get(x_4, 3);
x_47 = lean_ctor_get(x_4, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_4);
x_48 = lean_ctor_get(x_5, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_5, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_5, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_5, 5);
lean_inc(x_52);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 x_53 = x_5;
} else {
 lean_dec_ref(x_5);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_55 = lean_ctor_get(x_6, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_56 = x_6;
} else {
 lean_dec_ref(x_6);
 x_56 = lean_box(0);
}
x_57 = l_Std_PersistentArray_toArray___rarg(x_55);
lean_dec(x_55);
x_58 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_2);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Std_PersistentArray_push___rarg(x_1, x_59);
if (lean_is_scalar(x_56)) {
 x_61 = lean_alloc_ctor(0, 1, 1);
} else {
 x_61 = x_56;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_54);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(0, 6, 0);
} else {
 x_62 = x_53;
}
lean_ctor_set(x_62, 0, x_48);
lean_ctor_set(x_62, 1, x_49);
lean_ctor_set(x_62, 2, x_50);
lean_ctor_set(x_62, 3, x_51);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_52);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_44);
lean_ctor_set(x_63, 2, x_45);
lean_ctor_set(x_63, 3, x_46);
lean_ctor_set(x_63, 4, x_47);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_751; lean_object* x_752; uint8_t x_753; 
x_751 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_5);
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
x_753 = lean_ctor_get_uint8(x_752, sizeof(void*)*1);
lean_dec(x_752);
if (x_753 == 0)
{
lean_object* x_754; uint8_t x_755; 
x_754 = lean_ctor_get(x_751, 1);
lean_inc(x_754);
lean_dec(x_751);
x_755 = 0;
x_6 = x_755;
x_7 = x_754;
goto block_750;
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; uint8_t x_761; 
x_756 = lean_ctor_get(x_751, 1);
lean_inc(x_756);
lean_dec(x_751);
x_757 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_758 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_757, x_4, x_756);
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
x_761 = lean_unbox(x_759);
lean_dec(x_759);
x_6 = x_761;
x_7 = x_760;
goto block_750;
}
block_750:
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_8 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_11, 4);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_81; lean_object* x_82; lean_object* x_233; 
x_20 = 0;
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_20);
lean_ctor_set(x_11, 1, x_1);
x_233 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_11);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
lean_ctor_set(x_10, 0, x_235);
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_234);
x_81 = x_236;
x_82 = x_10;
goto block_232;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_233, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
lean_dec(x_233);
lean_ctor_set(x_10, 0, x_238);
x_239 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_239, 0, x_237);
x_81 = x_239;
x_82 = x_10;
goto block_232;
}
block_80:
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 4);
lean_inc(x_28);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_27, 4);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_13);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_13);
lean_ctor_set(x_27, 4, x_35);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
x_38 = lean_ctor_get(x_27, 2);
x_39 = lean_ctor_get(x_27, 3);
x_40 = lean_ctor_get(x_27, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_42 = x_28;
} else {
 lean_dec_ref(x_28);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 1, 1);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_13);
x_44 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set(x_44, 2, x_38);
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_40);
lean_ctor_set(x_25, 0, x_44);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_45 = lean_ctor_get(x_25, 1);
x_46 = lean_ctor_get(x_25, 2);
x_47 = lean_ctor_get(x_25, 3);
x_48 = lean_ctor_get(x_25, 4);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
x_49 = lean_ctor_get(x_27, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_27, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_27, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_27, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_27, 5);
lean_inc(x_53);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 x_54 = x_27;
} else {
 lean_dec_ref(x_27);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_28, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_56 = x_28;
} else {
 lean_dec_ref(x_28);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 1, 1);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 6, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_50);
lean_ctor_set(x_58, 2, x_51);
lean_ctor_set(x_58, 3, x_52);
lean_ctor_set(x_58, 4, x_57);
lean_ctor_set(x_58, 5, x_53);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_45);
lean_ctor_set(x_59, 2, x_46);
lean_ctor_set(x_59, 3, x_47);
lean_ctor_set(x_59, 4, x_48);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_59);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_60 = lean_ctor_get(x_23, 1);
lean_inc(x_60);
lean_dec(x_23);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_60, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 4);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 lean_ctor_release(x_60, 4);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_61, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_61, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_61, 5);
lean_inc(x_72);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 lean_ctor_release(x_61, 5);
 x_73 = x_61;
} else {
 lean_dec_ref(x_61);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_62, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_75 = x_62;
} else {
 lean_dec_ref(x_62);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 1, 1);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(0, 6, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_69);
lean_ctor_set(x_77, 2, x_70);
lean_ctor_set(x_77, 3, x_71);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set(x_77, 5, x_72);
if (lean_is_scalar(x_67)) {
 x_78 = lean_alloc_ctor(0, 5, 0);
} else {
 x_78 = x_67;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_63);
lean_ctor_set(x_78, 2, x_64);
lean_ctor_set(x_78, 3, x_65);
lean_ctor_set(x_78, 4, x_66);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_21);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
block_232:
{
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
lean_dec(x_81);
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_82, 0);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_83, 1);
lean_dec(x_88);
lean_ctor_set(x_83, 1, x_17);
x_21 = x_84;
x_22 = x_82;
goto block_80;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_83, 0);
x_90 = lean_ctor_get(x_83, 2);
x_91 = lean_ctor_get(x_83, 3);
x_92 = lean_ctor_get(x_83, 4);
x_93 = lean_ctor_get(x_83, 5);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_83);
x_94 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_17);
lean_ctor_set(x_94, 2, x_90);
lean_ctor_set(x_94, 3, x_91);
lean_ctor_set(x_94, 4, x_92);
lean_ctor_set(x_94, 5, x_93);
lean_ctor_set(x_82, 0, x_94);
x_21 = x_84;
x_22 = x_82;
goto block_80;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_95 = lean_ctor_get(x_82, 1);
x_96 = lean_ctor_get(x_82, 2);
x_97 = lean_ctor_get(x_82, 3);
x_98 = lean_ctor_get(x_82, 4);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_82);
x_99 = lean_ctor_get(x_83, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_83, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_83, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_83, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_83, 5);
lean_inc(x_103);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 lean_ctor_release(x_83, 3);
 lean_ctor_release(x_83, 4);
 lean_ctor_release(x_83, 5);
 x_104 = x_83;
} else {
 lean_dec_ref(x_83);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 6, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_17);
lean_ctor_set(x_105, 2, x_100);
lean_ctor_set(x_105, 3, x_101);
lean_ctor_set(x_105, 4, x_102);
lean_ctor_set(x_105, 5, x_103);
x_106 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_95);
lean_ctor_set(x_106, 2, x_96);
lean_ctor_set(x_106, 3, x_97);
lean_ctor_set(x_106, 4, x_98);
x_21 = x_84;
x_22 = x_106;
goto block_80;
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_81, 0);
lean_inc(x_108);
lean_dec(x_81);
x_109 = !lean_is_exclusive(x_82);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_82, 0);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_107);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_107, 1);
lean_dec(x_112);
lean_ctor_set(x_107, 1, x_17);
x_113 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_82);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_115 = lean_ctor_get(x_113, 1);
x_116 = lean_ctor_get(x_113, 0);
lean_dec(x_116);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 4);
lean_inc(x_118);
x_119 = !lean_is_exclusive(x_115);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_115, 0);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_117);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_117, 4);
lean_dec(x_122);
x_123 = !lean_is_exclusive(x_118);
if (x_123 == 0)
{
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_13);
lean_ctor_set(x_113, 0, x_108);
return x_113;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_118, 0);
lean_inc(x_124);
lean_dec(x_118);
x_125 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_13);
lean_ctor_set(x_117, 4, x_125);
lean_ctor_set(x_113, 0, x_108);
return x_113;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_126 = lean_ctor_get(x_117, 0);
x_127 = lean_ctor_get(x_117, 1);
x_128 = lean_ctor_get(x_117, 2);
x_129 = lean_ctor_get(x_117, 3);
x_130 = lean_ctor_get(x_117, 5);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_117);
x_131 = lean_ctor_get(x_118, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_132 = x_118;
} else {
 lean_dec_ref(x_118);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 1, 1);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_13);
x_134 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_134, 0, x_126);
lean_ctor_set(x_134, 1, x_127);
lean_ctor_set(x_134, 2, x_128);
lean_ctor_set(x_134, 3, x_129);
lean_ctor_set(x_134, 4, x_133);
lean_ctor_set(x_134, 5, x_130);
lean_ctor_set(x_115, 0, x_134);
lean_ctor_set(x_113, 0, x_108);
return x_113;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_135 = lean_ctor_get(x_115, 1);
x_136 = lean_ctor_get(x_115, 2);
x_137 = lean_ctor_get(x_115, 3);
x_138 = lean_ctor_get(x_115, 4);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_115);
x_139 = lean_ctor_get(x_117, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_117, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_117, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_117, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_117, 5);
lean_inc(x_143);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 lean_ctor_release(x_117, 4);
 lean_ctor_release(x_117, 5);
 x_144 = x_117;
} else {
 lean_dec_ref(x_117);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_118, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_146 = x_118;
} else {
 lean_dec_ref(x_118);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 1, 1);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_144)) {
 x_148 = lean_alloc_ctor(0, 6, 0);
} else {
 x_148 = x_144;
}
lean_ctor_set(x_148, 0, x_139);
lean_ctor_set(x_148, 1, x_140);
lean_ctor_set(x_148, 2, x_141);
lean_ctor_set(x_148, 3, x_142);
lean_ctor_set(x_148, 4, x_147);
lean_ctor_set(x_148, 5, x_143);
x_149 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_135);
lean_ctor_set(x_149, 2, x_136);
lean_ctor_set(x_149, 3, x_137);
lean_ctor_set(x_149, 4, x_138);
lean_ctor_set(x_113, 1, x_149);
lean_ctor_set(x_113, 0, x_108);
return x_113;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_150 = lean_ctor_get(x_113, 1);
lean_inc(x_150);
lean_dec(x_113);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_150, 2);
lean_inc(x_154);
x_155 = lean_ctor_get(x_150, 3);
lean_inc(x_155);
x_156 = lean_ctor_get(x_150, 4);
lean_inc(x_156);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 lean_ctor_release(x_150, 2);
 lean_ctor_release(x_150, 3);
 lean_ctor_release(x_150, 4);
 x_157 = x_150;
} else {
 lean_dec_ref(x_150);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_151, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_151, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_151, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_151, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_151, 5);
lean_inc(x_162);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 lean_ctor_release(x_151, 3);
 lean_ctor_release(x_151, 4);
 lean_ctor_release(x_151, 5);
 x_163 = x_151;
} else {
 lean_dec_ref(x_151);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_152, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_165 = x_152;
} else {
 lean_dec_ref(x_152);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 1, 1);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_163)) {
 x_167 = lean_alloc_ctor(0, 6, 0);
} else {
 x_167 = x_163;
}
lean_ctor_set(x_167, 0, x_158);
lean_ctor_set(x_167, 1, x_159);
lean_ctor_set(x_167, 2, x_160);
lean_ctor_set(x_167, 3, x_161);
lean_ctor_set(x_167, 4, x_166);
lean_ctor_set(x_167, 5, x_162);
if (lean_is_scalar(x_157)) {
 x_168 = lean_alloc_ctor(0, 5, 0);
} else {
 x_168 = x_157;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_153);
lean_ctor_set(x_168, 2, x_154);
lean_ctor_set(x_168, 3, x_155);
lean_ctor_set(x_168, 4, x_156);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_108);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_170 = lean_ctor_get(x_107, 0);
x_171 = lean_ctor_get(x_107, 2);
x_172 = lean_ctor_get(x_107, 3);
x_173 = lean_ctor_get(x_107, 4);
x_174 = lean_ctor_get(x_107, 5);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_107);
x_175 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_175, 0, x_170);
lean_ctor_set(x_175, 1, x_17);
lean_ctor_set(x_175, 2, x_171);
lean_ctor_set(x_175, 3, x_172);
lean_ctor_set(x_175, 4, x_173);
lean_ctor_set(x_175, 5, x_174);
lean_ctor_set(x_82, 0, x_175);
x_176 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_82);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_178 = x_176;
} else {
 lean_dec_ref(x_176);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_179, 4);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_177, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_177, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_177, 4);
lean_inc(x_184);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 lean_ctor_release(x_177, 4);
 x_185 = x_177;
} else {
 lean_dec_ref(x_177);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_179, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_179, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_179, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_179, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_179, 5);
lean_inc(x_190);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 lean_ctor_release(x_179, 5);
 x_191 = x_179;
} else {
 lean_dec_ref(x_179);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_180, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_193 = x_180;
} else {
 lean_dec_ref(x_180);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(0, 1, 1);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set_uint8(x_194, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_191)) {
 x_195 = lean_alloc_ctor(0, 6, 0);
} else {
 x_195 = x_191;
}
lean_ctor_set(x_195, 0, x_186);
lean_ctor_set(x_195, 1, x_187);
lean_ctor_set(x_195, 2, x_188);
lean_ctor_set(x_195, 3, x_189);
lean_ctor_set(x_195, 4, x_194);
lean_ctor_set(x_195, 5, x_190);
if (lean_is_scalar(x_185)) {
 x_196 = lean_alloc_ctor(0, 5, 0);
} else {
 x_196 = x_185;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_181);
lean_ctor_set(x_196, 2, x_182);
lean_ctor_set(x_196, 3, x_183);
lean_ctor_set(x_196, 4, x_184);
if (lean_is_scalar(x_178)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_178;
}
lean_ctor_set(x_197, 0, x_108);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_198 = lean_ctor_get(x_82, 1);
x_199 = lean_ctor_get(x_82, 2);
x_200 = lean_ctor_get(x_82, 3);
x_201 = lean_ctor_get(x_82, 4);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_82);
x_202 = lean_ctor_get(x_107, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_107, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_107, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_107, 4);
lean_inc(x_205);
x_206 = lean_ctor_get(x_107, 5);
lean_inc(x_206);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 lean_ctor_release(x_107, 4);
 lean_ctor_release(x_107, 5);
 x_207 = x_107;
} else {
 lean_dec_ref(x_107);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 6, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_202);
lean_ctor_set(x_208, 1, x_17);
lean_ctor_set(x_208, 2, x_203);
lean_ctor_set(x_208, 3, x_204);
lean_ctor_set(x_208, 4, x_205);
lean_ctor_set(x_208, 5, x_206);
x_209 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_198);
lean_ctor_set(x_209, 2, x_199);
lean_ctor_set(x_209, 3, x_200);
lean_ctor_set(x_209, 4, x_201);
x_210 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_209);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_212 = x_210;
} else {
 lean_dec_ref(x_210);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_213, 4);
lean_inc(x_214);
x_215 = lean_ctor_get(x_211, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_211, 2);
lean_inc(x_216);
x_217 = lean_ctor_get(x_211, 3);
lean_inc(x_217);
x_218 = lean_ctor_get(x_211, 4);
lean_inc(x_218);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 lean_ctor_release(x_211, 2);
 lean_ctor_release(x_211, 3);
 lean_ctor_release(x_211, 4);
 x_219 = x_211;
} else {
 lean_dec_ref(x_211);
 x_219 = lean_box(0);
}
x_220 = lean_ctor_get(x_213, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_213, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_213, 2);
lean_inc(x_222);
x_223 = lean_ctor_get(x_213, 3);
lean_inc(x_223);
x_224 = lean_ctor_get(x_213, 5);
lean_inc(x_224);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 lean_ctor_release(x_213, 4);
 lean_ctor_release(x_213, 5);
 x_225 = x_213;
} else {
 lean_dec_ref(x_213);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_214, 0);
lean_inc(x_226);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_227 = x_214;
} else {
 lean_dec_ref(x_214);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(0, 1, 1);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set_uint8(x_228, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_225)) {
 x_229 = lean_alloc_ctor(0, 6, 0);
} else {
 x_229 = x_225;
}
lean_ctor_set(x_229, 0, x_220);
lean_ctor_set(x_229, 1, x_221);
lean_ctor_set(x_229, 2, x_222);
lean_ctor_set(x_229, 3, x_223);
lean_ctor_set(x_229, 4, x_228);
lean_ctor_set(x_229, 5, x_224);
if (lean_is_scalar(x_219)) {
 x_230 = lean_alloc_ctor(0, 5, 0);
} else {
 x_230 = x_219;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_215);
lean_ctor_set(x_230, 2, x_216);
lean_ctor_set(x_230, 3, x_217);
lean_ctor_set(x_230, 4, x_218);
if (lean_is_scalar(x_212)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_212;
}
lean_ctor_set(x_231, 0, x_108);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
}
else
{
lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_268; lean_object* x_269; lean_object* x_323; 
x_240 = lean_ctor_get(x_12, 0);
lean_inc(x_240);
lean_dec(x_12);
x_241 = 0;
x_242 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set_uint8(x_242, sizeof(void*)*1, x_241);
lean_ctor_set(x_11, 4, x_242);
lean_ctor_set(x_11, 1, x_1);
x_323 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_11);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
lean_ctor_set(x_10, 0, x_325);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_324);
x_268 = x_326;
x_269 = x_10;
goto block_322;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_323, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_323, 1);
lean_inc(x_328);
lean_dec(x_323);
lean_ctor_set(x_10, 0, x_328);
x_329 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_329, 0, x_327);
x_268 = x_329;
x_269 = x_10;
goto block_322;
}
block_267:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_245 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_244);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_247 = x_245;
} else {
 lean_dec_ref(x_245);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_248, 4);
lean_inc(x_249);
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_246, 2);
lean_inc(x_251);
x_252 = lean_ctor_get(x_246, 3);
lean_inc(x_252);
x_253 = lean_ctor_get(x_246, 4);
lean_inc(x_253);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 lean_ctor_release(x_246, 3);
 lean_ctor_release(x_246, 4);
 x_254 = x_246;
} else {
 lean_dec_ref(x_246);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_248, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_248, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_248, 2);
lean_inc(x_257);
x_258 = lean_ctor_get(x_248, 3);
lean_inc(x_258);
x_259 = lean_ctor_get(x_248, 5);
lean_inc(x_259);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 lean_ctor_release(x_248, 2);
 lean_ctor_release(x_248, 3);
 lean_ctor_release(x_248, 4);
 lean_ctor_release(x_248, 5);
 x_260 = x_248;
} else {
 lean_dec_ref(x_248);
 x_260 = lean_box(0);
}
x_261 = lean_ctor_get(x_249, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 x_262 = x_249;
} else {
 lean_dec_ref(x_249);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(0, 1, 1);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set_uint8(x_263, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_260)) {
 x_264 = lean_alloc_ctor(0, 6, 0);
} else {
 x_264 = x_260;
}
lean_ctor_set(x_264, 0, x_255);
lean_ctor_set(x_264, 1, x_256);
lean_ctor_set(x_264, 2, x_257);
lean_ctor_set(x_264, 3, x_258);
lean_ctor_set(x_264, 4, x_263);
lean_ctor_set(x_264, 5, x_259);
if (lean_is_scalar(x_254)) {
 x_265 = lean_alloc_ctor(0, 5, 0);
} else {
 x_265 = x_254;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_250);
lean_ctor_set(x_265, 2, x_251);
lean_ctor_set(x_265, 3, x_252);
lean_ctor_set(x_265, 4, x_253);
if (lean_is_scalar(x_247)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_247;
 lean_ctor_set_tag(x_266, 1);
}
lean_ctor_set(x_266, 0, x_243);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
block_322:
{
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_268, 0);
lean_inc(x_271);
lean_dec(x_268);
x_272 = lean_ctor_get(x_269, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_269, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_269, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_269, 4);
lean_inc(x_275);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 lean_ctor_release(x_269, 2);
 lean_ctor_release(x_269, 3);
 lean_ctor_release(x_269, 4);
 x_276 = x_269;
} else {
 lean_dec_ref(x_269);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_270, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_270, 2);
lean_inc(x_278);
x_279 = lean_ctor_get(x_270, 3);
lean_inc(x_279);
x_280 = lean_ctor_get(x_270, 4);
lean_inc(x_280);
x_281 = lean_ctor_get(x_270, 5);
lean_inc(x_281);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 lean_ctor_release(x_270, 2);
 lean_ctor_release(x_270, 3);
 lean_ctor_release(x_270, 4);
 lean_ctor_release(x_270, 5);
 x_282 = x_270;
} else {
 lean_dec_ref(x_270);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 6, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_277);
lean_ctor_set(x_283, 1, x_17);
lean_ctor_set(x_283, 2, x_278);
lean_ctor_set(x_283, 3, x_279);
lean_ctor_set(x_283, 4, x_280);
lean_ctor_set(x_283, 5, x_281);
if (lean_is_scalar(x_276)) {
 x_284 = lean_alloc_ctor(0, 5, 0);
} else {
 x_284 = x_276;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_272);
lean_ctor_set(x_284, 2, x_273);
lean_ctor_set(x_284, 3, x_274);
lean_ctor_set(x_284, 4, x_275);
x_243 = x_271;
x_244 = x_284;
goto block_267;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_285 = lean_ctor_get(x_269, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_268, 0);
lean_inc(x_286);
lean_dec(x_268);
x_287 = lean_ctor_get(x_269, 1);
lean_inc(x_287);
x_288 = lean_ctor_get(x_269, 2);
lean_inc(x_288);
x_289 = lean_ctor_get(x_269, 3);
lean_inc(x_289);
x_290 = lean_ctor_get(x_269, 4);
lean_inc(x_290);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 lean_ctor_release(x_269, 2);
 lean_ctor_release(x_269, 3);
 lean_ctor_release(x_269, 4);
 x_291 = x_269;
} else {
 lean_dec_ref(x_269);
 x_291 = lean_box(0);
}
x_292 = lean_ctor_get(x_285, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_285, 2);
lean_inc(x_293);
x_294 = lean_ctor_get(x_285, 3);
lean_inc(x_294);
x_295 = lean_ctor_get(x_285, 4);
lean_inc(x_295);
x_296 = lean_ctor_get(x_285, 5);
lean_inc(x_296);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 lean_ctor_release(x_285, 3);
 lean_ctor_release(x_285, 4);
 lean_ctor_release(x_285, 5);
 x_297 = x_285;
} else {
 lean_dec_ref(x_285);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(0, 6, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_292);
lean_ctor_set(x_298, 1, x_17);
lean_ctor_set(x_298, 2, x_293);
lean_ctor_set(x_298, 3, x_294);
lean_ctor_set(x_298, 4, x_295);
lean_ctor_set(x_298, 5, x_296);
if (lean_is_scalar(x_291)) {
 x_299 = lean_alloc_ctor(0, 5, 0);
} else {
 x_299 = x_291;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_287);
lean_ctor_set(x_299, 2, x_288);
lean_ctor_set(x_299, 3, x_289);
lean_ctor_set(x_299, 4, x_290);
x_300 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_299);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_302 = x_300;
} else {
 lean_dec_ref(x_300);
 x_302 = lean_box(0);
}
x_303 = lean_ctor_get(x_301, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_303, 4);
lean_inc(x_304);
x_305 = lean_ctor_get(x_301, 1);
lean_inc(x_305);
x_306 = lean_ctor_get(x_301, 2);
lean_inc(x_306);
x_307 = lean_ctor_get(x_301, 3);
lean_inc(x_307);
x_308 = lean_ctor_get(x_301, 4);
lean_inc(x_308);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 lean_ctor_release(x_301, 2);
 lean_ctor_release(x_301, 3);
 lean_ctor_release(x_301, 4);
 x_309 = x_301;
} else {
 lean_dec_ref(x_301);
 x_309 = lean_box(0);
}
x_310 = lean_ctor_get(x_303, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_303, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_303, 2);
lean_inc(x_312);
x_313 = lean_ctor_get(x_303, 3);
lean_inc(x_313);
x_314 = lean_ctor_get(x_303, 5);
lean_inc(x_314);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 lean_ctor_release(x_303, 2);
 lean_ctor_release(x_303, 3);
 lean_ctor_release(x_303, 4);
 lean_ctor_release(x_303, 5);
 x_315 = x_303;
} else {
 lean_dec_ref(x_303);
 x_315 = lean_box(0);
}
x_316 = lean_ctor_get(x_304, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 x_317 = x_304;
} else {
 lean_dec_ref(x_304);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(0, 1, 1);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set_uint8(x_318, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_315)) {
 x_319 = lean_alloc_ctor(0, 6, 0);
} else {
 x_319 = x_315;
}
lean_ctor_set(x_319, 0, x_310);
lean_ctor_set(x_319, 1, x_311);
lean_ctor_set(x_319, 2, x_312);
lean_ctor_set(x_319, 3, x_313);
lean_ctor_set(x_319, 4, x_318);
lean_ctor_set(x_319, 5, x_314);
if (lean_is_scalar(x_309)) {
 x_320 = lean_alloc_ctor(0, 5, 0);
} else {
 x_320 = x_309;
}
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_305);
lean_ctor_set(x_320, 2, x_306);
lean_ctor_set(x_320, 3, x_307);
lean_ctor_set(x_320, 4, x_308);
if (lean_is_scalar(x_302)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_302;
}
lean_ctor_set(x_321, 0, x_286);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_364; lean_object* x_365; lean_object* x_419; lean_object* x_420; 
x_330 = lean_ctor_get(x_11, 0);
x_331 = lean_ctor_get(x_11, 1);
x_332 = lean_ctor_get(x_11, 2);
x_333 = lean_ctor_get(x_11, 3);
x_334 = lean_ctor_get(x_11, 5);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_11);
x_335 = lean_ctor_get(x_12, 0);
lean_inc(x_335);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_336 = x_12;
} else {
 lean_dec_ref(x_12);
 x_336 = lean_box(0);
}
x_337 = 0;
if (lean_is_scalar(x_336)) {
 x_338 = lean_alloc_ctor(0, 1, 1);
} else {
 x_338 = x_336;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set_uint8(x_338, sizeof(void*)*1, x_337);
x_419 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_419, 0, x_330);
lean_ctor_set(x_419, 1, x_1);
lean_ctor_set(x_419, 2, x_332);
lean_ctor_set(x_419, 3, x_333);
lean_ctor_set(x_419, 4, x_338);
lean_ctor_set(x_419, 5, x_334);
x_420 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_419);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
lean_ctor_set(x_10, 0, x_422);
x_423 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_423, 0, x_421);
x_364 = x_423;
x_365 = x_10;
goto block_418;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_420, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_420, 1);
lean_inc(x_425);
lean_dec(x_420);
lean_ctor_set(x_10, 0, x_425);
x_426 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_426, 0, x_424);
x_364 = x_426;
x_365 = x_10;
goto block_418;
}
block_363:
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_341 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_340);
x_342 = lean_ctor_get(x_341, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_343 = x_341;
} else {
 lean_dec_ref(x_341);
 x_343 = lean_box(0);
}
x_344 = lean_ctor_get(x_342, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_344, 4);
lean_inc(x_345);
x_346 = lean_ctor_get(x_342, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_342, 2);
lean_inc(x_347);
x_348 = lean_ctor_get(x_342, 3);
lean_inc(x_348);
x_349 = lean_ctor_get(x_342, 4);
lean_inc(x_349);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 lean_ctor_release(x_342, 3);
 lean_ctor_release(x_342, 4);
 x_350 = x_342;
} else {
 lean_dec_ref(x_342);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_344, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_344, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_344, 2);
lean_inc(x_353);
x_354 = lean_ctor_get(x_344, 3);
lean_inc(x_354);
x_355 = lean_ctor_get(x_344, 5);
lean_inc(x_355);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 lean_ctor_release(x_344, 2);
 lean_ctor_release(x_344, 3);
 lean_ctor_release(x_344, 4);
 lean_ctor_release(x_344, 5);
 x_356 = x_344;
} else {
 lean_dec_ref(x_344);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_345, 0);
lean_inc(x_357);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 x_358 = x_345;
} else {
 lean_dec_ref(x_345);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(0, 1, 1);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set_uint8(x_359, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_356)) {
 x_360 = lean_alloc_ctor(0, 6, 0);
} else {
 x_360 = x_356;
}
lean_ctor_set(x_360, 0, x_351);
lean_ctor_set(x_360, 1, x_352);
lean_ctor_set(x_360, 2, x_353);
lean_ctor_set(x_360, 3, x_354);
lean_ctor_set(x_360, 4, x_359);
lean_ctor_set(x_360, 5, x_355);
if (lean_is_scalar(x_350)) {
 x_361 = lean_alloc_ctor(0, 5, 0);
} else {
 x_361 = x_350;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_346);
lean_ctor_set(x_361, 2, x_347);
lean_ctor_set(x_361, 3, x_348);
lean_ctor_set(x_361, 4, x_349);
if (lean_is_scalar(x_343)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_343;
 lean_ctor_set_tag(x_362, 1);
}
lean_ctor_set(x_362, 0, x_339);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
block_418:
{
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_364, 0);
lean_inc(x_367);
lean_dec(x_364);
x_368 = lean_ctor_get(x_365, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_365, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_365, 3);
lean_inc(x_370);
x_371 = lean_ctor_get(x_365, 4);
lean_inc(x_371);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 lean_ctor_release(x_365, 2);
 lean_ctor_release(x_365, 3);
 lean_ctor_release(x_365, 4);
 x_372 = x_365;
} else {
 lean_dec_ref(x_365);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_366, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_366, 2);
lean_inc(x_374);
x_375 = lean_ctor_get(x_366, 3);
lean_inc(x_375);
x_376 = lean_ctor_get(x_366, 4);
lean_inc(x_376);
x_377 = lean_ctor_get(x_366, 5);
lean_inc(x_377);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 lean_ctor_release(x_366, 2);
 lean_ctor_release(x_366, 3);
 lean_ctor_release(x_366, 4);
 lean_ctor_release(x_366, 5);
 x_378 = x_366;
} else {
 lean_dec_ref(x_366);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 6, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_373);
lean_ctor_set(x_379, 1, x_331);
lean_ctor_set(x_379, 2, x_374);
lean_ctor_set(x_379, 3, x_375);
lean_ctor_set(x_379, 4, x_376);
lean_ctor_set(x_379, 5, x_377);
if (lean_is_scalar(x_372)) {
 x_380 = lean_alloc_ctor(0, 5, 0);
} else {
 x_380 = x_372;
}
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_368);
lean_ctor_set(x_380, 2, x_369);
lean_ctor_set(x_380, 3, x_370);
lean_ctor_set(x_380, 4, x_371);
x_339 = x_367;
x_340 = x_380;
goto block_363;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_381 = lean_ctor_get(x_365, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_364, 0);
lean_inc(x_382);
lean_dec(x_364);
x_383 = lean_ctor_get(x_365, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_365, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_365, 3);
lean_inc(x_385);
x_386 = lean_ctor_get(x_365, 4);
lean_inc(x_386);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 lean_ctor_release(x_365, 2);
 lean_ctor_release(x_365, 3);
 lean_ctor_release(x_365, 4);
 x_387 = x_365;
} else {
 lean_dec_ref(x_365);
 x_387 = lean_box(0);
}
x_388 = lean_ctor_get(x_381, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_381, 2);
lean_inc(x_389);
x_390 = lean_ctor_get(x_381, 3);
lean_inc(x_390);
x_391 = lean_ctor_get(x_381, 4);
lean_inc(x_391);
x_392 = lean_ctor_get(x_381, 5);
lean_inc(x_392);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 lean_ctor_release(x_381, 2);
 lean_ctor_release(x_381, 3);
 lean_ctor_release(x_381, 4);
 lean_ctor_release(x_381, 5);
 x_393 = x_381;
} else {
 lean_dec_ref(x_381);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(0, 6, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_388);
lean_ctor_set(x_394, 1, x_331);
lean_ctor_set(x_394, 2, x_389);
lean_ctor_set(x_394, 3, x_390);
lean_ctor_set(x_394, 4, x_391);
lean_ctor_set(x_394, 5, x_392);
if (lean_is_scalar(x_387)) {
 x_395 = lean_alloc_ctor(0, 5, 0);
} else {
 x_395 = x_387;
}
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_383);
lean_ctor_set(x_395, 2, x_384);
lean_ctor_set(x_395, 3, x_385);
lean_ctor_set(x_395, 4, x_386);
x_396 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_395);
x_397 = lean_ctor_get(x_396, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_398 = x_396;
} else {
 lean_dec_ref(x_396);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_397, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_399, 4);
lean_inc(x_400);
x_401 = lean_ctor_get(x_397, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_397, 2);
lean_inc(x_402);
x_403 = lean_ctor_get(x_397, 3);
lean_inc(x_403);
x_404 = lean_ctor_get(x_397, 4);
lean_inc(x_404);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 lean_ctor_release(x_397, 2);
 lean_ctor_release(x_397, 3);
 lean_ctor_release(x_397, 4);
 x_405 = x_397;
} else {
 lean_dec_ref(x_397);
 x_405 = lean_box(0);
}
x_406 = lean_ctor_get(x_399, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_399, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_399, 2);
lean_inc(x_408);
x_409 = lean_ctor_get(x_399, 3);
lean_inc(x_409);
x_410 = lean_ctor_get(x_399, 5);
lean_inc(x_410);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 lean_ctor_release(x_399, 2);
 lean_ctor_release(x_399, 3);
 lean_ctor_release(x_399, 4);
 lean_ctor_release(x_399, 5);
 x_411 = x_399;
} else {
 lean_dec_ref(x_399);
 x_411 = lean_box(0);
}
x_412 = lean_ctor_get(x_400, 0);
lean_inc(x_412);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 x_413 = x_400;
} else {
 lean_dec_ref(x_400);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(0, 1, 1);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set_uint8(x_414, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_411)) {
 x_415 = lean_alloc_ctor(0, 6, 0);
} else {
 x_415 = x_411;
}
lean_ctor_set(x_415, 0, x_406);
lean_ctor_set(x_415, 1, x_407);
lean_ctor_set(x_415, 2, x_408);
lean_ctor_set(x_415, 3, x_409);
lean_ctor_set(x_415, 4, x_414);
lean_ctor_set(x_415, 5, x_410);
if (lean_is_scalar(x_405)) {
 x_416 = lean_alloc_ctor(0, 5, 0);
} else {
 x_416 = x_405;
}
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_401);
lean_ctor_set(x_416, 2, x_402);
lean_ctor_set(x_416, 3, x_403);
lean_ctor_set(x_416, 4, x_404);
if (lean_is_scalar(x_398)) {
 x_417 = lean_alloc_ctor(0, 2, 0);
} else {
 x_417 = x_398;
}
lean_ctor_set(x_417, 0, x_382);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_466; lean_object* x_467; lean_object* x_521; lean_object* x_522; 
x_427 = lean_ctor_get(x_10, 1);
x_428 = lean_ctor_get(x_10, 2);
x_429 = lean_ctor_get(x_10, 3);
x_430 = lean_ctor_get(x_10, 4);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_10);
x_431 = lean_ctor_get(x_11, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_11, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_11, 2);
lean_inc(x_433);
x_434 = lean_ctor_get(x_11, 3);
lean_inc(x_434);
x_435 = lean_ctor_get(x_11, 5);
lean_inc(x_435);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_436 = x_11;
} else {
 lean_dec_ref(x_11);
 x_436 = lean_box(0);
}
x_437 = lean_ctor_get(x_12, 0);
lean_inc(x_437);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_438 = x_12;
} else {
 lean_dec_ref(x_12);
 x_438 = lean_box(0);
}
x_439 = 0;
if (lean_is_scalar(x_438)) {
 x_440 = lean_alloc_ctor(0, 1, 1);
} else {
 x_440 = x_438;
}
lean_ctor_set(x_440, 0, x_437);
lean_ctor_set_uint8(x_440, sizeof(void*)*1, x_439);
if (lean_is_scalar(x_436)) {
 x_521 = lean_alloc_ctor(0, 6, 0);
} else {
 x_521 = x_436;
}
lean_ctor_set(x_521, 0, x_431);
lean_ctor_set(x_521, 1, x_1);
lean_ctor_set(x_521, 2, x_433);
lean_ctor_set(x_521, 3, x_434);
lean_ctor_set(x_521, 4, x_440);
lean_ctor_set(x_521, 5, x_435);
x_522 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_521);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
x_525 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_427);
lean_ctor_set(x_525, 2, x_428);
lean_ctor_set(x_525, 3, x_429);
lean_ctor_set(x_525, 4, x_430);
x_526 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_526, 0, x_523);
x_466 = x_526;
x_467 = x_525;
goto block_520;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_527 = lean_ctor_get(x_522, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_522, 1);
lean_inc(x_528);
lean_dec(x_522);
x_529 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_427);
lean_ctor_set(x_529, 2, x_428);
lean_ctor_set(x_529, 3, x_429);
lean_ctor_set(x_529, 4, x_430);
x_530 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_530, 0, x_527);
x_466 = x_530;
x_467 = x_529;
goto block_520;
}
block_465:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_443 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_442);
x_444 = lean_ctor_get(x_443, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_445 = x_443;
} else {
 lean_dec_ref(x_443);
 x_445 = lean_box(0);
}
x_446 = lean_ctor_get(x_444, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_446, 4);
lean_inc(x_447);
x_448 = lean_ctor_get(x_444, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_444, 2);
lean_inc(x_449);
x_450 = lean_ctor_get(x_444, 3);
lean_inc(x_450);
x_451 = lean_ctor_get(x_444, 4);
lean_inc(x_451);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 lean_ctor_release(x_444, 2);
 lean_ctor_release(x_444, 3);
 lean_ctor_release(x_444, 4);
 x_452 = x_444;
} else {
 lean_dec_ref(x_444);
 x_452 = lean_box(0);
}
x_453 = lean_ctor_get(x_446, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_446, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_446, 2);
lean_inc(x_455);
x_456 = lean_ctor_get(x_446, 3);
lean_inc(x_456);
x_457 = lean_ctor_get(x_446, 5);
lean_inc(x_457);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 lean_ctor_release(x_446, 2);
 lean_ctor_release(x_446, 3);
 lean_ctor_release(x_446, 4);
 lean_ctor_release(x_446, 5);
 x_458 = x_446;
} else {
 lean_dec_ref(x_446);
 x_458 = lean_box(0);
}
x_459 = lean_ctor_get(x_447, 0);
lean_inc(x_459);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 x_460 = x_447;
} else {
 lean_dec_ref(x_447);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(0, 1, 1);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set_uint8(x_461, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_458)) {
 x_462 = lean_alloc_ctor(0, 6, 0);
} else {
 x_462 = x_458;
}
lean_ctor_set(x_462, 0, x_453);
lean_ctor_set(x_462, 1, x_454);
lean_ctor_set(x_462, 2, x_455);
lean_ctor_set(x_462, 3, x_456);
lean_ctor_set(x_462, 4, x_461);
lean_ctor_set(x_462, 5, x_457);
if (lean_is_scalar(x_452)) {
 x_463 = lean_alloc_ctor(0, 5, 0);
} else {
 x_463 = x_452;
}
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_448);
lean_ctor_set(x_463, 2, x_449);
lean_ctor_set(x_463, 3, x_450);
lean_ctor_set(x_463, 4, x_451);
if (lean_is_scalar(x_445)) {
 x_464 = lean_alloc_ctor(1, 2, 0);
} else {
 x_464 = x_445;
 lean_ctor_set_tag(x_464, 1);
}
lean_ctor_set(x_464, 0, x_441);
lean_ctor_set(x_464, 1, x_463);
return x_464;
}
block_520:
{
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_466, 0);
lean_inc(x_469);
lean_dec(x_466);
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_467, 2);
lean_inc(x_471);
x_472 = lean_ctor_get(x_467, 3);
lean_inc(x_472);
x_473 = lean_ctor_get(x_467, 4);
lean_inc(x_473);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 lean_ctor_release(x_467, 2);
 lean_ctor_release(x_467, 3);
 lean_ctor_release(x_467, 4);
 x_474 = x_467;
} else {
 lean_dec_ref(x_467);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_468, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_468, 2);
lean_inc(x_476);
x_477 = lean_ctor_get(x_468, 3);
lean_inc(x_477);
x_478 = lean_ctor_get(x_468, 4);
lean_inc(x_478);
x_479 = lean_ctor_get(x_468, 5);
lean_inc(x_479);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 lean_ctor_release(x_468, 2);
 lean_ctor_release(x_468, 3);
 lean_ctor_release(x_468, 4);
 lean_ctor_release(x_468, 5);
 x_480 = x_468;
} else {
 lean_dec_ref(x_468);
 x_480 = lean_box(0);
}
if (lean_is_scalar(x_480)) {
 x_481 = lean_alloc_ctor(0, 6, 0);
} else {
 x_481 = x_480;
}
lean_ctor_set(x_481, 0, x_475);
lean_ctor_set(x_481, 1, x_432);
lean_ctor_set(x_481, 2, x_476);
lean_ctor_set(x_481, 3, x_477);
lean_ctor_set(x_481, 4, x_478);
lean_ctor_set(x_481, 5, x_479);
if (lean_is_scalar(x_474)) {
 x_482 = lean_alloc_ctor(0, 5, 0);
} else {
 x_482 = x_474;
}
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_470);
lean_ctor_set(x_482, 2, x_471);
lean_ctor_set(x_482, 3, x_472);
lean_ctor_set(x_482, 4, x_473);
x_441 = x_469;
x_442 = x_482;
goto block_465;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_483 = lean_ctor_get(x_467, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_466, 0);
lean_inc(x_484);
lean_dec(x_466);
x_485 = lean_ctor_get(x_467, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_467, 2);
lean_inc(x_486);
x_487 = lean_ctor_get(x_467, 3);
lean_inc(x_487);
x_488 = lean_ctor_get(x_467, 4);
lean_inc(x_488);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 lean_ctor_release(x_467, 2);
 lean_ctor_release(x_467, 3);
 lean_ctor_release(x_467, 4);
 x_489 = x_467;
} else {
 lean_dec_ref(x_467);
 x_489 = lean_box(0);
}
x_490 = lean_ctor_get(x_483, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_483, 2);
lean_inc(x_491);
x_492 = lean_ctor_get(x_483, 3);
lean_inc(x_492);
x_493 = lean_ctor_get(x_483, 4);
lean_inc(x_493);
x_494 = lean_ctor_get(x_483, 5);
lean_inc(x_494);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 lean_ctor_release(x_483, 2);
 lean_ctor_release(x_483, 3);
 lean_ctor_release(x_483, 4);
 lean_ctor_release(x_483, 5);
 x_495 = x_483;
} else {
 lean_dec_ref(x_483);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(0, 6, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_490);
lean_ctor_set(x_496, 1, x_432);
lean_ctor_set(x_496, 2, x_491);
lean_ctor_set(x_496, 3, x_492);
lean_ctor_set(x_496, 4, x_493);
lean_ctor_set(x_496, 5, x_494);
if (lean_is_scalar(x_489)) {
 x_497 = lean_alloc_ctor(0, 5, 0);
} else {
 x_497 = x_489;
}
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_485);
lean_ctor_set(x_497, 2, x_486);
lean_ctor_set(x_497, 3, x_487);
lean_ctor_set(x_497, 4, x_488);
x_498 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_497);
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_500 = x_498;
} else {
 lean_dec_ref(x_498);
 x_500 = lean_box(0);
}
x_501 = lean_ctor_get(x_499, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_501, 4);
lean_inc(x_502);
x_503 = lean_ctor_get(x_499, 1);
lean_inc(x_503);
x_504 = lean_ctor_get(x_499, 2);
lean_inc(x_504);
x_505 = lean_ctor_get(x_499, 3);
lean_inc(x_505);
x_506 = lean_ctor_get(x_499, 4);
lean_inc(x_506);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 lean_ctor_release(x_499, 2);
 lean_ctor_release(x_499, 3);
 lean_ctor_release(x_499, 4);
 x_507 = x_499;
} else {
 lean_dec_ref(x_499);
 x_507 = lean_box(0);
}
x_508 = lean_ctor_get(x_501, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_501, 1);
lean_inc(x_509);
x_510 = lean_ctor_get(x_501, 2);
lean_inc(x_510);
x_511 = lean_ctor_get(x_501, 3);
lean_inc(x_511);
x_512 = lean_ctor_get(x_501, 5);
lean_inc(x_512);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 lean_ctor_release(x_501, 2);
 lean_ctor_release(x_501, 3);
 lean_ctor_release(x_501, 4);
 lean_ctor_release(x_501, 5);
 x_513 = x_501;
} else {
 lean_dec_ref(x_501);
 x_513 = lean_box(0);
}
x_514 = lean_ctor_get(x_502, 0);
lean_inc(x_514);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 x_515 = x_502;
} else {
 lean_dec_ref(x_502);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_515)) {
 x_516 = lean_alloc_ctor(0, 1, 1);
} else {
 x_516 = x_515;
}
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set_uint8(x_516, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_513)) {
 x_517 = lean_alloc_ctor(0, 6, 0);
} else {
 x_517 = x_513;
}
lean_ctor_set(x_517, 0, x_508);
lean_ctor_set(x_517, 1, x_509);
lean_ctor_set(x_517, 2, x_510);
lean_ctor_set(x_517, 3, x_511);
lean_ctor_set(x_517, 4, x_516);
lean_ctor_set(x_517, 5, x_512);
if (lean_is_scalar(x_507)) {
 x_518 = lean_alloc_ctor(0, 5, 0);
} else {
 x_518 = x_507;
}
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_503);
lean_ctor_set(x_518, 2, x_504);
lean_ctor_set(x_518, 3, x_505);
lean_ctor_set(x_518, 4, x_506);
if (lean_is_scalar(x_500)) {
 x_519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_519 = x_500;
}
lean_ctor_set(x_519, 0, x_484);
lean_ctor_set(x_519, 1, x_518);
return x_519;
}
}
}
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; 
x_531 = l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(x_7);
x_532 = lean_ctor_get(x_531, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_531, 0);
lean_inc(x_534);
lean_dec(x_531);
x_535 = !lean_is_exclusive(x_532);
if (x_535 == 0)
{
lean_object* x_536; uint8_t x_537; 
x_536 = lean_ctor_get(x_532, 0);
lean_dec(x_536);
x_537 = !lean_is_exclusive(x_533);
if (x_537 == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_622; 
x_538 = lean_ctor_get(x_533, 1);
lean_ctor_set(x_533, 1, x_1);
lean_inc(x_4);
x_622 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_533);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
lean_dec(x_622);
lean_ctor_set(x_532, 0, x_624);
x_625 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_625, 0, x_623);
x_539 = x_625;
x_540 = x_532;
goto block_621;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_626 = lean_ctor_get(x_622, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_622, 1);
lean_inc(x_627);
lean_dec(x_622);
lean_ctor_set(x_532, 0, x_627);
x_628 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_628, 0, x_626);
x_539 = x_628;
x_540 = x_532;
goto block_621;
}
block_621:
{
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_541; lean_object* x_542; uint8_t x_543; 
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_539, 0);
lean_inc(x_542);
lean_dec(x_539);
x_543 = !lean_is_exclusive(x_540);
if (x_543 == 0)
{
lean_object* x_544; uint8_t x_545; 
x_544 = lean_ctor_get(x_540, 0);
lean_dec(x_544);
x_545 = !lean_is_exclusive(x_541);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
x_546 = lean_ctor_get(x_541, 1);
lean_dec(x_546);
lean_ctor_set(x_541, 1, x_538);
x_547 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_548 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_534, x_547, x_4, x_540);
lean_dec(x_4);
x_549 = !lean_is_exclusive(x_548);
if (x_549 == 0)
{
lean_object* x_550; 
x_550 = lean_ctor_get(x_548, 0);
lean_dec(x_550);
lean_ctor_set_tag(x_548, 1);
lean_ctor_set(x_548, 0, x_542);
return x_548;
}
else
{
lean_object* x_551; lean_object* x_552; 
x_551 = lean_ctor_get(x_548, 1);
lean_inc(x_551);
lean_dec(x_548);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_542);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_553 = lean_ctor_get(x_541, 0);
x_554 = lean_ctor_get(x_541, 2);
x_555 = lean_ctor_get(x_541, 3);
x_556 = lean_ctor_get(x_541, 4);
x_557 = lean_ctor_get(x_541, 5);
lean_inc(x_557);
lean_inc(x_556);
lean_inc(x_555);
lean_inc(x_554);
lean_inc(x_553);
lean_dec(x_541);
x_558 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_558, 0, x_553);
lean_ctor_set(x_558, 1, x_538);
lean_ctor_set(x_558, 2, x_554);
lean_ctor_set(x_558, 3, x_555);
lean_ctor_set(x_558, 4, x_556);
lean_ctor_set(x_558, 5, x_557);
lean_ctor_set(x_540, 0, x_558);
x_559 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_560 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_534, x_559, x_4, x_540);
lean_dec(x_4);
x_561 = lean_ctor_get(x_560, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_562 = x_560;
} else {
 lean_dec_ref(x_560);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_563 = lean_alloc_ctor(1, 2, 0);
} else {
 x_563 = x_562;
 lean_ctor_set_tag(x_563, 1);
}
lean_ctor_set(x_563, 0, x_542);
lean_ctor_set(x_563, 1, x_561);
return x_563;
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_564 = lean_ctor_get(x_540, 1);
x_565 = lean_ctor_get(x_540, 2);
x_566 = lean_ctor_get(x_540, 3);
x_567 = lean_ctor_get(x_540, 4);
lean_inc(x_567);
lean_inc(x_566);
lean_inc(x_565);
lean_inc(x_564);
lean_dec(x_540);
x_568 = lean_ctor_get(x_541, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_541, 2);
lean_inc(x_569);
x_570 = lean_ctor_get(x_541, 3);
lean_inc(x_570);
x_571 = lean_ctor_get(x_541, 4);
lean_inc(x_571);
x_572 = lean_ctor_get(x_541, 5);
lean_inc(x_572);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 lean_ctor_release(x_541, 2);
 lean_ctor_release(x_541, 3);
 lean_ctor_release(x_541, 4);
 lean_ctor_release(x_541, 5);
 x_573 = x_541;
} else {
 lean_dec_ref(x_541);
 x_573 = lean_box(0);
}
if (lean_is_scalar(x_573)) {
 x_574 = lean_alloc_ctor(0, 6, 0);
} else {
 x_574 = x_573;
}
lean_ctor_set(x_574, 0, x_568);
lean_ctor_set(x_574, 1, x_538);
lean_ctor_set(x_574, 2, x_569);
lean_ctor_set(x_574, 3, x_570);
lean_ctor_set(x_574, 4, x_571);
lean_ctor_set(x_574, 5, x_572);
x_575 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_575, 0, x_574);
lean_ctor_set(x_575, 1, x_564);
lean_ctor_set(x_575, 2, x_565);
lean_ctor_set(x_575, 3, x_566);
lean_ctor_set(x_575, 4, x_567);
x_576 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_577 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_534, x_576, x_4, x_575);
lean_dec(x_4);
x_578 = lean_ctor_get(x_577, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_579 = x_577;
} else {
 lean_dec_ref(x_577);
 x_579 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_580 = lean_alloc_ctor(1, 2, 0);
} else {
 x_580 = x_579;
 lean_ctor_set_tag(x_580, 1);
}
lean_ctor_set(x_580, 0, x_542);
lean_ctor_set(x_580, 1, x_578);
return x_580;
}
}
else
{
lean_object* x_581; lean_object* x_582; uint8_t x_583; 
x_581 = lean_ctor_get(x_540, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_539, 0);
lean_inc(x_582);
lean_dec(x_539);
x_583 = !lean_is_exclusive(x_540);
if (x_583 == 0)
{
lean_object* x_584; uint8_t x_585; 
x_584 = lean_ctor_get(x_540, 0);
lean_dec(x_584);
x_585 = !lean_is_exclusive(x_581);
if (x_585 == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; uint8_t x_589; 
x_586 = lean_ctor_get(x_581, 1);
lean_dec(x_586);
lean_ctor_set(x_581, 1, x_538);
x_587 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_588 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_534, x_587, x_4, x_540);
lean_dec(x_4);
x_589 = !lean_is_exclusive(x_588);
if (x_589 == 0)
{
lean_object* x_590; 
x_590 = lean_ctor_get(x_588, 0);
lean_dec(x_590);
lean_ctor_set(x_588, 0, x_582);
return x_588;
}
else
{
lean_object* x_591; lean_object* x_592; 
x_591 = lean_ctor_get(x_588, 1);
lean_inc(x_591);
lean_dec(x_588);
x_592 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_592, 0, x_582);
lean_ctor_set(x_592, 1, x_591);
return x_592;
}
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_593 = lean_ctor_get(x_581, 0);
x_594 = lean_ctor_get(x_581, 2);
x_595 = lean_ctor_get(x_581, 3);
x_596 = lean_ctor_get(x_581, 4);
x_597 = lean_ctor_get(x_581, 5);
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_593);
lean_dec(x_581);
x_598 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_598, 0, x_593);
lean_ctor_set(x_598, 1, x_538);
lean_ctor_set(x_598, 2, x_594);
lean_ctor_set(x_598, 3, x_595);
lean_ctor_set(x_598, 4, x_596);
lean_ctor_set(x_598, 5, x_597);
lean_ctor_set(x_540, 0, x_598);
x_599 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_600 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_534, x_599, x_4, x_540);
lean_dec(x_4);
x_601 = lean_ctor_get(x_600, 1);
lean_inc(x_601);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 x_602 = x_600;
} else {
 lean_dec_ref(x_600);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_603 = x_602;
}
lean_ctor_set(x_603, 0, x_582);
lean_ctor_set(x_603, 1, x_601);
return x_603;
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_604 = lean_ctor_get(x_540, 1);
x_605 = lean_ctor_get(x_540, 2);
x_606 = lean_ctor_get(x_540, 3);
x_607 = lean_ctor_get(x_540, 4);
lean_inc(x_607);
lean_inc(x_606);
lean_inc(x_605);
lean_inc(x_604);
lean_dec(x_540);
x_608 = lean_ctor_get(x_581, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_581, 2);
lean_inc(x_609);
x_610 = lean_ctor_get(x_581, 3);
lean_inc(x_610);
x_611 = lean_ctor_get(x_581, 4);
lean_inc(x_611);
x_612 = lean_ctor_get(x_581, 5);
lean_inc(x_612);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 lean_ctor_release(x_581, 2);
 lean_ctor_release(x_581, 3);
 lean_ctor_release(x_581, 4);
 lean_ctor_release(x_581, 5);
 x_613 = x_581;
} else {
 lean_dec_ref(x_581);
 x_613 = lean_box(0);
}
if (lean_is_scalar(x_613)) {
 x_614 = lean_alloc_ctor(0, 6, 0);
} else {
 x_614 = x_613;
}
lean_ctor_set(x_614, 0, x_608);
lean_ctor_set(x_614, 1, x_538);
lean_ctor_set(x_614, 2, x_609);
lean_ctor_set(x_614, 3, x_610);
lean_ctor_set(x_614, 4, x_611);
lean_ctor_set(x_614, 5, x_612);
x_615 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_615, 0, x_614);
lean_ctor_set(x_615, 1, x_604);
lean_ctor_set(x_615, 2, x_605);
lean_ctor_set(x_615, 3, x_606);
lean_ctor_set(x_615, 4, x_607);
x_616 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_617 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_534, x_616, x_4, x_615);
lean_dec(x_4);
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_619 = x_617;
} else {
 lean_dec_ref(x_617);
 x_619 = lean_box(0);
}
if (lean_is_scalar(x_619)) {
 x_620 = lean_alloc_ctor(0, 2, 0);
} else {
 x_620 = x_619;
}
lean_ctor_set(x_620, 0, x_582);
lean_ctor_set(x_620, 1, x_618);
return x_620;
}
}
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_678; lean_object* x_679; 
x_629 = lean_ctor_get(x_533, 0);
x_630 = lean_ctor_get(x_533, 1);
x_631 = lean_ctor_get(x_533, 2);
x_632 = lean_ctor_get(x_533, 3);
x_633 = lean_ctor_get(x_533, 4);
x_634 = lean_ctor_get(x_533, 5);
lean_inc(x_634);
lean_inc(x_633);
lean_inc(x_632);
lean_inc(x_631);
lean_inc(x_630);
lean_inc(x_629);
lean_dec(x_533);
x_678 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_678, 0, x_629);
lean_ctor_set(x_678, 1, x_1);
lean_ctor_set(x_678, 2, x_631);
lean_ctor_set(x_678, 3, x_632);
lean_ctor_set(x_678, 4, x_633);
lean_ctor_set(x_678, 5, x_634);
lean_inc(x_4);
x_679 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_678);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
lean_dec(x_679);
lean_ctor_set(x_532, 0, x_681);
x_682 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_682, 0, x_680);
x_635 = x_682;
x_636 = x_532;
goto block_677;
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_683 = lean_ctor_get(x_679, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_679, 1);
lean_inc(x_684);
lean_dec(x_679);
lean_ctor_set(x_532, 0, x_684);
x_685 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_685, 0, x_683);
x_635 = x_685;
x_636 = x_532;
goto block_677;
}
block_677:
{
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_635, 0);
lean_inc(x_638);
lean_dec(x_635);
x_639 = lean_ctor_get(x_636, 1);
lean_inc(x_639);
x_640 = lean_ctor_get(x_636, 2);
lean_inc(x_640);
x_641 = lean_ctor_get(x_636, 3);
lean_inc(x_641);
x_642 = lean_ctor_get(x_636, 4);
lean_inc(x_642);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 lean_ctor_release(x_636, 2);
 lean_ctor_release(x_636, 3);
 lean_ctor_release(x_636, 4);
 x_643 = x_636;
} else {
 lean_dec_ref(x_636);
 x_643 = lean_box(0);
}
x_644 = lean_ctor_get(x_637, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_637, 2);
lean_inc(x_645);
x_646 = lean_ctor_get(x_637, 3);
lean_inc(x_646);
x_647 = lean_ctor_get(x_637, 4);
lean_inc(x_647);
x_648 = lean_ctor_get(x_637, 5);
lean_inc(x_648);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 lean_ctor_release(x_637, 2);
 lean_ctor_release(x_637, 3);
 lean_ctor_release(x_637, 4);
 lean_ctor_release(x_637, 5);
 x_649 = x_637;
} else {
 lean_dec_ref(x_637);
 x_649 = lean_box(0);
}
if (lean_is_scalar(x_649)) {
 x_650 = lean_alloc_ctor(0, 6, 0);
} else {
 x_650 = x_649;
}
lean_ctor_set(x_650, 0, x_644);
lean_ctor_set(x_650, 1, x_630);
lean_ctor_set(x_650, 2, x_645);
lean_ctor_set(x_650, 3, x_646);
lean_ctor_set(x_650, 4, x_647);
lean_ctor_set(x_650, 5, x_648);
if (lean_is_scalar(x_643)) {
 x_651 = lean_alloc_ctor(0, 5, 0);
} else {
 x_651 = x_643;
}
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_639);
lean_ctor_set(x_651, 2, x_640);
lean_ctor_set(x_651, 3, x_641);
lean_ctor_set(x_651, 4, x_642);
x_652 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_653 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_534, x_652, x_4, x_651);
lean_dec(x_4);
x_654 = lean_ctor_get(x_653, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_653)) {
 lean_ctor_release(x_653, 0);
 lean_ctor_release(x_653, 1);
 x_655 = x_653;
} else {
 lean_dec_ref(x_653);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_656 = x_655;
 lean_ctor_set_tag(x_656, 1);
}
lean_ctor_set(x_656, 0, x_638);
lean_ctor_set(x_656, 1, x_654);
return x_656;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
x_657 = lean_ctor_get(x_636, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_635, 0);
lean_inc(x_658);
lean_dec(x_635);
x_659 = lean_ctor_get(x_636, 1);
lean_inc(x_659);
x_660 = lean_ctor_get(x_636, 2);
lean_inc(x_660);
x_661 = lean_ctor_get(x_636, 3);
lean_inc(x_661);
x_662 = lean_ctor_get(x_636, 4);
lean_inc(x_662);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 lean_ctor_release(x_636, 2);
 lean_ctor_release(x_636, 3);
 lean_ctor_release(x_636, 4);
 x_663 = x_636;
} else {
 lean_dec_ref(x_636);
 x_663 = lean_box(0);
}
x_664 = lean_ctor_get(x_657, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_657, 2);
lean_inc(x_665);
x_666 = lean_ctor_get(x_657, 3);
lean_inc(x_666);
x_667 = lean_ctor_get(x_657, 4);
lean_inc(x_667);
x_668 = lean_ctor_get(x_657, 5);
lean_inc(x_668);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 lean_ctor_release(x_657, 2);
 lean_ctor_release(x_657, 3);
 lean_ctor_release(x_657, 4);
 lean_ctor_release(x_657, 5);
 x_669 = x_657;
} else {
 lean_dec_ref(x_657);
 x_669 = lean_box(0);
}
if (lean_is_scalar(x_669)) {
 x_670 = lean_alloc_ctor(0, 6, 0);
} else {
 x_670 = x_669;
}
lean_ctor_set(x_670, 0, x_664);
lean_ctor_set(x_670, 1, x_630);
lean_ctor_set(x_670, 2, x_665);
lean_ctor_set(x_670, 3, x_666);
lean_ctor_set(x_670, 4, x_667);
lean_ctor_set(x_670, 5, x_668);
if (lean_is_scalar(x_663)) {
 x_671 = lean_alloc_ctor(0, 5, 0);
} else {
 x_671 = x_663;
}
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_659);
lean_ctor_set(x_671, 2, x_660);
lean_ctor_set(x_671, 3, x_661);
lean_ctor_set(x_671, 4, x_662);
x_672 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_673 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_534, x_672, x_4, x_671);
lean_dec(x_4);
x_674 = lean_ctor_get(x_673, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 x_675 = x_673;
} else {
 lean_dec_ref(x_673);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(0, 2, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_658);
lean_ctor_set(x_676, 1, x_674);
return x_676;
}
}
}
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_740; lean_object* x_741; 
x_686 = lean_ctor_get(x_532, 1);
x_687 = lean_ctor_get(x_532, 2);
x_688 = lean_ctor_get(x_532, 3);
x_689 = lean_ctor_get(x_532, 4);
lean_inc(x_689);
lean_inc(x_688);
lean_inc(x_687);
lean_inc(x_686);
lean_dec(x_532);
x_690 = lean_ctor_get(x_533, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_533, 1);
lean_inc(x_691);
x_692 = lean_ctor_get(x_533, 2);
lean_inc(x_692);
x_693 = lean_ctor_get(x_533, 3);
lean_inc(x_693);
x_694 = lean_ctor_get(x_533, 4);
lean_inc(x_694);
x_695 = lean_ctor_get(x_533, 5);
lean_inc(x_695);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 lean_ctor_release(x_533, 2);
 lean_ctor_release(x_533, 3);
 lean_ctor_release(x_533, 4);
 lean_ctor_release(x_533, 5);
 x_696 = x_533;
} else {
 lean_dec_ref(x_533);
 x_696 = lean_box(0);
}
if (lean_is_scalar(x_696)) {
 x_740 = lean_alloc_ctor(0, 6, 0);
} else {
 x_740 = x_696;
}
lean_ctor_set(x_740, 0, x_690);
lean_ctor_set(x_740, 1, x_1);
lean_ctor_set(x_740, 2, x_692);
lean_ctor_set(x_740, 3, x_693);
lean_ctor_set(x_740, 4, x_694);
lean_ctor_set(x_740, 5, x_695);
lean_inc(x_4);
x_741 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_740);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
lean_dec(x_741);
x_744 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_744, 0, x_743);
lean_ctor_set(x_744, 1, x_686);
lean_ctor_set(x_744, 2, x_687);
lean_ctor_set(x_744, 3, x_688);
lean_ctor_set(x_744, 4, x_689);
x_745 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_745, 0, x_742);
x_697 = x_745;
x_698 = x_744;
goto block_739;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_746 = lean_ctor_get(x_741, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_741, 1);
lean_inc(x_747);
lean_dec(x_741);
x_748 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_686);
lean_ctor_set(x_748, 2, x_687);
lean_ctor_set(x_748, 3, x_688);
lean_ctor_set(x_748, 4, x_689);
x_749 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_749, 0, x_746);
x_697 = x_749;
x_698 = x_748;
goto block_739;
}
block_739:
{
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_699 = lean_ctor_get(x_698, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_697, 0);
lean_inc(x_700);
lean_dec(x_697);
x_701 = lean_ctor_get(x_698, 1);
lean_inc(x_701);
x_702 = lean_ctor_get(x_698, 2);
lean_inc(x_702);
x_703 = lean_ctor_get(x_698, 3);
lean_inc(x_703);
x_704 = lean_ctor_get(x_698, 4);
lean_inc(x_704);
if (lean_is_exclusive(x_698)) {
 lean_ctor_release(x_698, 0);
 lean_ctor_release(x_698, 1);
 lean_ctor_release(x_698, 2);
 lean_ctor_release(x_698, 3);
 lean_ctor_release(x_698, 4);
 x_705 = x_698;
} else {
 lean_dec_ref(x_698);
 x_705 = lean_box(0);
}
x_706 = lean_ctor_get(x_699, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_699, 2);
lean_inc(x_707);
x_708 = lean_ctor_get(x_699, 3);
lean_inc(x_708);
x_709 = lean_ctor_get(x_699, 4);
lean_inc(x_709);
x_710 = lean_ctor_get(x_699, 5);
lean_inc(x_710);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 lean_ctor_release(x_699, 2);
 lean_ctor_release(x_699, 3);
 lean_ctor_release(x_699, 4);
 lean_ctor_release(x_699, 5);
 x_711 = x_699;
} else {
 lean_dec_ref(x_699);
 x_711 = lean_box(0);
}
if (lean_is_scalar(x_711)) {
 x_712 = lean_alloc_ctor(0, 6, 0);
} else {
 x_712 = x_711;
}
lean_ctor_set(x_712, 0, x_706);
lean_ctor_set(x_712, 1, x_691);
lean_ctor_set(x_712, 2, x_707);
lean_ctor_set(x_712, 3, x_708);
lean_ctor_set(x_712, 4, x_709);
lean_ctor_set(x_712, 5, x_710);
if (lean_is_scalar(x_705)) {
 x_713 = lean_alloc_ctor(0, 5, 0);
} else {
 x_713 = x_705;
}
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_701);
lean_ctor_set(x_713, 2, x_702);
lean_ctor_set(x_713, 3, x_703);
lean_ctor_set(x_713, 4, x_704);
x_714 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_715 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_534, x_714, x_4, x_713);
lean_dec(x_4);
x_716 = lean_ctor_get(x_715, 1);
lean_inc(x_716);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_717 = x_715;
} else {
 lean_dec_ref(x_715);
 x_717 = lean_box(0);
}
if (lean_is_scalar(x_717)) {
 x_718 = lean_alloc_ctor(1, 2, 0);
} else {
 x_718 = x_717;
 lean_ctor_set_tag(x_718, 1);
}
lean_ctor_set(x_718, 0, x_700);
lean_ctor_set(x_718, 1, x_716);
return x_718;
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_719 = lean_ctor_get(x_698, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_697, 0);
lean_inc(x_720);
lean_dec(x_697);
x_721 = lean_ctor_get(x_698, 1);
lean_inc(x_721);
x_722 = lean_ctor_get(x_698, 2);
lean_inc(x_722);
x_723 = lean_ctor_get(x_698, 3);
lean_inc(x_723);
x_724 = lean_ctor_get(x_698, 4);
lean_inc(x_724);
if (lean_is_exclusive(x_698)) {
 lean_ctor_release(x_698, 0);
 lean_ctor_release(x_698, 1);
 lean_ctor_release(x_698, 2);
 lean_ctor_release(x_698, 3);
 lean_ctor_release(x_698, 4);
 x_725 = x_698;
} else {
 lean_dec_ref(x_698);
 x_725 = lean_box(0);
}
x_726 = lean_ctor_get(x_719, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_719, 2);
lean_inc(x_727);
x_728 = lean_ctor_get(x_719, 3);
lean_inc(x_728);
x_729 = lean_ctor_get(x_719, 4);
lean_inc(x_729);
x_730 = lean_ctor_get(x_719, 5);
lean_inc(x_730);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 lean_ctor_release(x_719, 2);
 lean_ctor_release(x_719, 3);
 lean_ctor_release(x_719, 4);
 lean_ctor_release(x_719, 5);
 x_731 = x_719;
} else {
 lean_dec_ref(x_719);
 x_731 = lean_box(0);
}
if (lean_is_scalar(x_731)) {
 x_732 = lean_alloc_ctor(0, 6, 0);
} else {
 x_732 = x_731;
}
lean_ctor_set(x_732, 0, x_726);
lean_ctor_set(x_732, 1, x_691);
lean_ctor_set(x_732, 2, x_727);
lean_ctor_set(x_732, 3, x_728);
lean_ctor_set(x_732, 4, x_729);
lean_ctor_set(x_732, 5, x_730);
if (lean_is_scalar(x_725)) {
 x_733 = lean_alloc_ctor(0, 5, 0);
} else {
 x_733 = x_725;
}
lean_ctor_set(x_733, 0, x_732);
lean_ctor_set(x_733, 1, x_721);
lean_ctor_set(x_733, 2, x_722);
lean_ctor_set(x_733, 3, x_723);
lean_ctor_set(x_733, 4, x_724);
x_734 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_735 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_534, x_734, x_4, x_733);
lean_dec(x_4);
x_736 = lean_ctor_get(x_735, 1);
lean_inc(x_736);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 lean_ctor_release(x_735, 1);
 x_737 = x_735;
} else {
 lean_dec_ref(x_735);
 x_737 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_738 = lean_alloc_ctor(0, 2, 0);
} else {
 x_738 = x_737;
}
lean_ctor_set(x_738, 0, x_720);
lean_ctor_set(x_738, 1, x_736);
return x_738;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tryAnswer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_69; 
x_11 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_6, 1, x_1);
lean_inc(x_4);
x_69 = l_Lean_Meta_openAbstractMVarsResult(x_7, x_4, x_6);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Meta_isExprDefEq(x_2, x_73, x_4, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
lean_ctor_set(x_5, 0, x_77);
x_78 = l_Lean_Meta_SynthInstance_tryAnswer___closed__1;
x_12 = x_78;
x_13 = x_5;
goto block_68;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_dec(x_74);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_ctor_set(x_5, 0, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_12 = x_82;
x_13 = x_5;
goto block_68;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_74, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_dec(x_74);
lean_ctor_set(x_5, 0, x_84);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_83);
x_12 = x_85;
x_13 = x_5;
goto block_68;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_4);
lean_dec(x_2);
x_86 = lean_ctor_get(x_69, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
lean_dec(x_69);
lean_ctor_set(x_5, 0, x_87);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_86);
x_12 = x_88;
x_13 = x_5;
goto block_68;
}
block_68:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_dec(x_19);
lean_ctor_set(x_14, 1, x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 2);
x_23 = lean_ctor_get(x_14, 3);
x_24 = lean_ctor_get(x_14, 4);
x_25 = lean_ctor_get(x_14, 5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_24);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_13, 0, x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_13);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_13, 1);
x_29 = lean_ctor_get(x_13, 2);
x_30 = lean_ctor_get(x_13, 3);
x_31 = lean_ctor_get(x_13, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_14, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_14, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_14, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_14, 5);
lean_inc(x_36);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 x_37 = x_14;
} else {
 lean_dec_ref(x_14);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 6, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_11);
lean_ctor_set(x_38, 2, x_33);
lean_ctor_set(x_38, 3, x_34);
lean_ctor_set(x_38, 4, x_35);
lean_ctor_set(x_38, 5, x_36);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set(x_39, 2, x_29);
lean_ctor_set(x_39, 3, x_30);
lean_ctor_set(x_39, 4, x_31);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_15);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_12, 0);
lean_inc(x_42);
lean_dec(x_12);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_13, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_dec(x_46);
lean_ctor_set(x_41, 1, x_11);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_13);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_41, 0);
x_49 = lean_ctor_get(x_41, 2);
x_50 = lean_ctor_get(x_41, 3);
x_51 = lean_ctor_get(x_41, 4);
x_52 = lean_ctor_get(x_41, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_41);
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_11);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_51);
lean_ctor_set(x_53, 5, x_52);
lean_ctor_set(x_13, 0, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set(x_54, 1, x_13);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_13, 1);
x_56 = lean_ctor_get(x_13, 2);
x_57 = lean_ctor_get(x_13, 3);
x_58 = lean_ctor_get(x_13, 4);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_59 = lean_ctor_get(x_41, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_41, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_41, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_41, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_41, 5);
lean_inc(x_63);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 x_64 = x_41;
} else {
 lean_dec_ref(x_41);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 6, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_11);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_61);
lean_ctor_set(x_65, 4, x_62);
lean_ctor_set(x_65, 5, x_63);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_55);
lean_ctor_set(x_66, 2, x_56);
lean_ctor_set(x_66, 3, x_57);
lean_ctor_set(x_66, 4, x_58);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_42);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_130; lean_object* x_131; 
x_89 = lean_ctor_get(x_6, 0);
x_90 = lean_ctor_get(x_6, 1);
x_91 = lean_ctor_get(x_6, 2);
x_92 = lean_ctor_get(x_6, 3);
x_93 = lean_ctor_get(x_6, 4);
x_94 = lean_ctor_get(x_6, 5);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_6);
x_130 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_130, 0, x_89);
lean_ctor_set(x_130, 1, x_1);
lean_ctor_set(x_130, 2, x_91);
lean_ctor_set(x_130, 3, x_92);
lean_ctor_set(x_130, 4, x_93);
lean_ctor_set(x_130, 5, x_94);
lean_inc(x_4);
x_131 = l_Lean_Meta_openAbstractMVarsResult(x_7, x_4, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Meta_isExprDefEq(x_2, x_135, x_4, x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
lean_ctor_set(x_5, 0, x_139);
x_140 = l_Lean_Meta_SynthInstance_tryAnswer___closed__1;
x_95 = x_140;
x_96 = x_5;
goto block_129;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_ctor_set(x_5, 0, x_141);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_95 = x_144;
x_96 = x_5;
goto block_129;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_136, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_136, 1);
lean_inc(x_146);
lean_dec(x_136);
lean_ctor_set(x_5, 0, x_146);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_145);
x_95 = x_147;
x_96 = x_5;
goto block_129;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_4);
lean_dec(x_2);
x_148 = lean_ctor_get(x_131, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_131, 1);
lean_inc(x_149);
lean_dec(x_131);
lean_ctor_set(x_5, 0, x_149);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_148);
x_95 = x_150;
x_96 = x_5;
goto block_129;
}
block_129:
{
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_96, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 4);
lean_inc(x_102);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 lean_ctor_release(x_96, 3);
 lean_ctor_release(x_96, 4);
 x_103 = x_96;
} else {
 lean_dec_ref(x_96);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_97, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_97, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_97, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_97, 4);
lean_inc(x_107);
x_108 = lean_ctor_get(x_97, 5);
lean_inc(x_108);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 lean_ctor_release(x_97, 2);
 lean_ctor_release(x_97, 3);
 lean_ctor_release(x_97, 4);
 lean_ctor_release(x_97, 5);
 x_109 = x_97;
} else {
 lean_dec_ref(x_97);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_90);
lean_ctor_set(x_110, 2, x_105);
lean_ctor_set(x_110, 3, x_106);
lean_ctor_set(x_110, 4, x_107);
lean_ctor_set(x_110, 5, x_108);
if (lean_is_scalar(x_103)) {
 x_111 = lean_alloc_ctor(0, 5, 0);
} else {
 x_111 = x_103;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_99);
lean_ctor_set(x_111, 2, x_100);
lean_ctor_set(x_111, 3, x_101);
lean_ctor_set(x_111, 4, x_102);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_98);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_113 = lean_ctor_get(x_96, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_95, 0);
lean_inc(x_114);
lean_dec(x_95);
x_115 = lean_ctor_get(x_96, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_96, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_96, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_96, 4);
lean_inc(x_118);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 lean_ctor_release(x_96, 3);
 lean_ctor_release(x_96, 4);
 x_119 = x_96;
} else {
 lean_dec_ref(x_96);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_113, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_113, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_113, 3);
lean_inc(x_122);
x_123 = lean_ctor_get(x_113, 4);
lean_inc(x_123);
x_124 = lean_ctor_get(x_113, 5);
lean_inc(x_124);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 lean_ctor_release(x_113, 5);
 x_125 = x_113;
} else {
 lean_dec_ref(x_113);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 6, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_120);
lean_ctor_set(x_126, 1, x_90);
lean_ctor_set(x_126, 2, x_121);
lean_ctor_set(x_126, 3, x_122);
lean_ctor_set(x_126, 4, x_123);
lean_ctor_set(x_126, 5, x_124);
if (lean_is_scalar(x_119)) {
 x_127 = lean_alloc_ctor(0, 5, 0);
} else {
 x_127 = x_119;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_115);
lean_ctor_set(x_127, 2, x_116);
lean_ctor_set(x_127, 3, x_117);
lean_ctor_set(x_127, 4, x_118);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_114);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_197; lean_object* x_198; 
x_151 = lean_ctor_get(x_5, 1);
x_152 = lean_ctor_get(x_5, 2);
x_153 = lean_ctor_get(x_5, 3);
x_154 = lean_ctor_get(x_5, 4);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_5);
x_155 = lean_ctor_get(x_6, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_6, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_6, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_6, 3);
lean_inc(x_158);
x_159 = lean_ctor_get(x_6, 4);
lean_inc(x_159);
x_160 = lean_ctor_get(x_6, 5);
lean_inc(x_160);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 x_161 = x_6;
} else {
 lean_dec_ref(x_6);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_197 = lean_alloc_ctor(0, 6, 0);
} else {
 x_197 = x_161;
}
lean_ctor_set(x_197, 0, x_155);
lean_ctor_set(x_197, 1, x_1);
lean_ctor_set(x_197, 2, x_157);
lean_ctor_set(x_197, 3, x_158);
lean_ctor_set(x_197, 4, x_159);
lean_ctor_set(x_197, 5, x_160);
lean_inc(x_4);
x_198 = l_Lean_Meta_openAbstractMVarsResult(x_7, x_4, x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec(x_198);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Meta_isExprDefEq(x_2, x_202, x_4, x_201);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_unbox(x_204);
lean_dec(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_dec(x_203);
x_207 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_151);
lean_ctor_set(x_207, 2, x_152);
lean_ctor_set(x_207, 3, x_153);
lean_ctor_set(x_207, 4, x_154);
x_208 = l_Lean_Meta_SynthInstance_tryAnswer___closed__1;
x_162 = x_208;
x_163 = x_207;
goto block_196;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_ctor_get(x_203, 1);
lean_inc(x_209);
lean_dec(x_203);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
x_211 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_151);
lean_ctor_set(x_211, 2, x_152);
lean_ctor_set(x_211, 3, x_153);
lean_ctor_set(x_211, 4, x_154);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_210);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_162 = x_213;
x_163 = x_211;
goto block_196;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_203, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_203, 1);
lean_inc(x_215);
lean_dec(x_203);
x_216 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_151);
lean_ctor_set(x_216, 2, x_152);
lean_ctor_set(x_216, 3, x_153);
lean_ctor_set(x_216, 4, x_154);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_214);
x_162 = x_217;
x_163 = x_216;
goto block_196;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_4);
lean_dec(x_2);
x_218 = lean_ctor_get(x_198, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_198, 1);
lean_inc(x_219);
lean_dec(x_198);
x_220 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_151);
lean_ctor_set(x_220, 2, x_152);
lean_ctor_set(x_220, 3, x_153);
lean_ctor_set(x_220, 4, x_154);
x_221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_221, 0, x_218);
x_162 = x_221;
x_163 = x_220;
goto block_196;
}
block_196:
{
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 3);
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
x_172 = lean_ctor_get(x_164, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_164, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_164, 4);
lean_inc(x_174);
x_175 = lean_ctor_get(x_164, 5);
lean_inc(x_175);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 lean_ctor_release(x_164, 3);
 lean_ctor_release(x_164, 4);
 lean_ctor_release(x_164, 5);
 x_176 = x_164;
} else {
 lean_dec_ref(x_164);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 6, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_171);
lean_ctor_set(x_177, 1, x_156);
lean_ctor_set(x_177, 2, x_172);
lean_ctor_set(x_177, 3, x_173);
lean_ctor_set(x_177, 4, x_174);
lean_ctor_set(x_177, 5, x_175);
if (lean_is_scalar(x_170)) {
 x_178 = lean_alloc_ctor(0, 5, 0);
} else {
 x_178 = x_170;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_166);
lean_ctor_set(x_178, 2, x_167);
lean_ctor_set(x_178, 3, x_168);
lean_ctor_set(x_178, 4, x_169);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_165);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_180 = lean_ctor_get(x_163, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_162, 0);
lean_inc(x_181);
lean_dec(x_162);
x_182 = lean_ctor_get(x_163, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_163, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_163, 3);
lean_inc(x_184);
x_185 = lean_ctor_get(x_163, 4);
lean_inc(x_185);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 lean_ctor_release(x_163, 3);
 lean_ctor_release(x_163, 4);
 x_186 = x_163;
} else {
 lean_dec_ref(x_163);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_180, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_180, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_180, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_180, 4);
lean_inc(x_190);
x_191 = lean_ctor_get(x_180, 5);
lean_inc(x_191);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 lean_ctor_release(x_180, 4);
 lean_ctor_release(x_180, 5);
 x_192 = x_180;
} else {
 lean_dec_ref(x_180);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 6, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_187);
lean_ctor_set(x_193, 1, x_156);
lean_ctor_set(x_193, 2, x_188);
lean_ctor_set(x_193, 3, x_189);
lean_ctor_set(x_193, 4, x_190);
lean_ctor_set(x_193, 5, x_191);
if (lean_is_scalar(x_186)) {
 x_194 = lean_alloc_ctor(0, 5, 0);
} else {
 x_194 = x_186;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_182);
lean_ctor_set(x_194, 2, x_183);
lean_ctor_set(x_194, 3, x_184);
lean_ctor_set(x_194, 4, x_185);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_181);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("skip answer containing metavariables ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_wakeUp___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_wakeUp___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_wakeUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_array_push(x_7, x_8);
lean_ctor_set(x_4, 3, x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
x_17 = lean_ctor_get(x_4, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
lean_inc(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_1);
x_19 = lean_array_push(x_16, x_18);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_20, 4, x_17);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_110; uint8_t x_111; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_110 = lean_ctor_get(x_23, 0);
lean_inc(x_110);
x_111 = l_Array_isEmpty___rarg(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_box(0);
x_24 = x_112;
goto block_109;
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_23, 1);
lean_inc(x_113);
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_nat_dec_eq(x_113, x_114);
lean_dec(x_113);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_box(0);
x_24 = x_116;
goto block_109;
}
else
{
uint8_t x_117; 
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_4);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_4, 1);
lean_dec(x_118);
x_119 = lean_ctor_get(x_23, 2);
lean_inc(x_119);
lean_dec(x_23);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_4, 1, x_120);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_4);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_123 = lean_ctor_get(x_4, 0);
x_124 = lean_ctor_get(x_4, 2);
x_125 = lean_ctor_get(x_4, 3);
x_126 = lean_ctor_get(x_4, 4);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_4);
x_127 = lean_ctor_get(x_23, 2);
lean_inc(x_127);
lean_dec(x_23);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_124);
lean_ctor_set(x_129, 3, x_125);
lean_ctor_set(x_129, 4, x_126);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
block_109:
{
uint8_t x_25; 
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_3);
x_27 = l_Lean_Meta_openAbstractMVarsResult(x_23, x_3, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set(x_4, 0, x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_4);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
lean_dec(x_31);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_43 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_42, x_3, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
uint8_t x_46; 
lean_dec(x_31);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_43, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_ctor_set(x_43, 0, x_48);
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_31);
x_54 = l_Lean_Meta_SynthInstance_wakeUp___closed__3;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_42, x_55, x_3, x_52);
lean_dec(x_3);
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
}
}
else
{
uint8_t x_63; 
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_27);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_27, 1);
lean_ctor_set(x_4, 0, x_64);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_27, 0);
x_66 = lean_ctor_get(x_27, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_27);
lean_ctor_set(x_4, 0, x_66);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_4);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_4, 0);
x_69 = lean_ctor_get(x_4, 1);
x_70 = lean_ctor_get(x_4, 2);
x_71 = lean_ctor_get(x_4, 3);
x_72 = lean_ctor_get(x_4, 4);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_4);
lean_inc(x_3);
x_73 = l_Lean_Meta_openAbstractMVarsResult(x_23, x_3, x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
lean_ctor_set(x_76, 2, x_70);
lean_ctor_set(x_76, 3, x_71);
lean_ctor_set(x_76, 4, x_72);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_76);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_80, sizeof(void*)*1);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
lean_dec(x_3);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_88 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_87, x_3, x_86);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_78);
lean_dec(x_3);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_92 = x_88;
} else {
 lean_dec_ref(x_88);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
lean_dec(x_88);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_78);
x_97 = l_Lean_Meta_SynthInstance_wakeUp___closed__3;
x_98 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_87, x_98, x_3, x_95);
lean_dec(x_3);
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
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_3);
x_104 = lean_ctor_get(x_73, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_73, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_106 = x_73;
} else {
 lean_dec_ref(x_73);
 x_106 = lean_box(0);
}
x_107 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_69);
lean_ctor_set(x_107, 2, x_70);
lean_ctor_set(x_107, 3, x_71);
lean_ctor_set(x_107, 4, x_72);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_wakeUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SynthInstance_wakeUp(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_expr_eqv(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = 1;
return x_15;
}
}
}
}
uint8_t l_Lean_Meta_SynthInstance_isNewAnswer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_SynthInstance_isNewAnswer___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Lean_Meta_SynthInstance_wakeUp(x_1, x_10, x_4, x_5);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("newAnswer");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_addAnswer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_addAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_185; uint8_t x_226; lean_object* x_227; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_10 = lean_ctor_get(x_4, 1);
lean_ctor_set(x_4, 1, x_5);
x_258 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_3);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get_uint8(x_259, sizeof(void*)*1);
lean_dec(x_259);
if (x_260 == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec(x_258);
x_262 = 0;
x_226 = x_262;
x_227 = x_261;
goto block_257;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_263 = lean_ctor_get(x_258, 1);
lean_inc(x_263);
lean_dec(x_258);
x_264 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_265 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_264, x_2, x_263);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_unbox(x_266);
lean_dec(x_266);
x_226 = x_268;
x_227 = x_267;
goto block_257;
}
block_184:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_dec(x_18);
lean_ctor_set(x_13, 1, x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 2);
x_22 = lean_ctor_get(x_13, 3);
x_23 = lean_ctor_get(x_13, 4);
x_24 = lean_ctor_get(x_13, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_10);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
lean_ctor_set(x_12, 0, x_25);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_12, 1);
x_28 = lean_ctor_get(x_12, 2);
x_29 = lean_ctor_get(x_12, 3);
x_30 = lean_ctor_get(x_12, 4);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_13, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_13, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 5);
lean_inc(x_35);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_36 = x_13;
} else {
 lean_dec_ref(x_13);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 6, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_10);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 4, x_34);
lean_ctor_set(x_37, 5, x_35);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_27);
lean_ctor_set(x_38, 2, x_28);
lean_ctor_set(x_38, 3, x_29);
lean_ctor_set(x_38, 4, x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_14);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_12, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_11, 0);
lean_inc(x_41);
lean_dec(x_11);
x_42 = !lean_is_exclusive(x_12);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_12, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 1);
lean_dec(x_45);
lean_ctor_set(x_40, 1, x_10);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_dec(x_1);
lean_inc(x_2);
x_47 = l_Lean_Meta_SynthInstance_getEntry(x_46, x_2, x_12);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_47, 1);
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
x_54 = l_Lean_Meta_SynthInstance_isNewAnswer(x_53, x_41);
if (x_54 == 0)
{
lean_object* x_55; 
lean_free_object(x_49);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_2);
x_55 = lean_box(0);
lean_ctor_set(x_47, 0, x_55);
return x_47;
}
else
{
lean_object* x_56; uint8_t x_57; 
lean_free_object(x_47);
lean_inc(x_41);
x_56 = lean_array_push(x_53, x_41);
lean_inc(x_52);
lean_ctor_set(x_49, 1, x_56);
x_57 = !lean_is_exclusive(x_51);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_51, 4);
x_59 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_58, x_46, x_49);
lean_ctor_set(x_51, 4, x_59);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_41, x_52, x_60, x_2, x_51);
lean_dec(x_52);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_ctor_get(x_51, 1);
x_64 = lean_ctor_get(x_51, 2);
x_65 = lean_ctor_get(x_51, 3);
x_66 = lean_ctor_get(x_51, 4);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_51);
x_67 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_66, x_46, x_49);
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_64);
lean_ctor_set(x_68, 3, x_65);
lean_ctor_set(x_68, 4, x_67);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_41, x_52, x_69, x_2, x_68);
lean_dec(x_52);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_47, 1);
x_72 = lean_ctor_get(x_49, 0);
x_73 = lean_ctor_get(x_49, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_49);
x_74 = l_Lean_Meta_SynthInstance_isNewAnswer(x_73, x_41);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_2);
x_75 = lean_box(0);
lean_ctor_set(x_47, 0, x_75);
return x_47;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_free_object(x_47);
lean_inc(x_41);
x_76 = lean_array_push(x_73, x_41);
lean_inc(x_72);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_71, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_71, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_71, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_71, 4);
lean_inc(x_82);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 x_83 = x_71;
} else {
 lean_dec_ref(x_71);
 x_83 = lean_box(0);
}
x_84 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_82, x_46, x_77);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_79);
lean_ctor_set(x_85, 2, x_80);
lean_ctor_set(x_85, 3, x_81);
lean_ctor_set(x_85, 4, x_84);
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_41, x_72, x_86, x_2, x_85);
lean_dec(x_72);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_47, 0);
x_89 = lean_ctor_get(x_47, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_47);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_92 = x_88;
} else {
 lean_dec_ref(x_88);
 x_92 = lean_box(0);
}
x_93 = l_Lean_Meta_SynthInstance_isNewAnswer(x_91, x_41);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_2);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_89);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_inc(x_41);
x_96 = lean_array_push(x_91, x_41);
lean_inc(x_90);
if (lean_is_scalar(x_92)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_92;
}
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_ctor_get(x_89, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_89, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_89, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_89, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_89, 4);
lean_inc(x_102);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 x_103 = x_89;
} else {
 lean_dec_ref(x_89);
 x_103 = lean_box(0);
}
x_104 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_102, x_46, x_97);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 5, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_99);
lean_ctor_set(x_105, 2, x_100);
lean_ctor_set(x_105, 3, x_101);
lean_ctor_set(x_105, 4, x_104);
x_106 = lean_unsigned_to_nat(0u);
x_107 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_41, x_90, x_106, x_2, x_105);
lean_dec(x_90);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_47);
if (x_108 == 0)
{
return x_47;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_47, 0);
x_110 = lean_ctor_get(x_47, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_47);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_40, 0);
x_113 = lean_ctor_get(x_40, 2);
x_114 = lean_ctor_get(x_40, 3);
x_115 = lean_ctor_get(x_40, 4);
x_116 = lean_ctor_get(x_40, 5);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_40);
x_117 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_10);
lean_ctor_set(x_117, 2, x_113);
lean_ctor_set(x_117, 3, x_114);
lean_ctor_set(x_117, 4, x_115);
lean_ctor_set(x_117, 5, x_116);
lean_ctor_set(x_12, 0, x_117);
x_118 = lean_ctor_get(x_1, 1);
lean_inc(x_118);
lean_dec(x_1);
lean_inc(x_2);
x_119 = l_Lean_Meta_SynthInstance_getEntry(x_118, x_2, x_12);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_125 = x_120;
} else {
 lean_dec_ref(x_120);
 x_125 = lean_box(0);
}
x_126 = l_Lean_Meta_SynthInstance_isNewAnswer(x_124, x_41);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_118);
lean_dec(x_41);
lean_dec(x_2);
x_127 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_122;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_121);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_122);
lean_inc(x_41);
x_129 = lean_array_push(x_124, x_41);
lean_inc(x_123);
if (lean_is_scalar(x_125)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_125;
}
lean_ctor_set(x_130, 0, x_123);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_ctor_get(x_121, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_121, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_121, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_121, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_121, 4);
lean_inc(x_135);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 lean_ctor_release(x_121, 4);
 x_136 = x_121;
} else {
 lean_dec_ref(x_121);
 x_136 = lean_box(0);
}
x_137 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_135, x_118, x_130);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 5, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_131);
lean_ctor_set(x_138, 1, x_132);
lean_ctor_set(x_138, 2, x_133);
lean_ctor_set(x_138, 3, x_134);
lean_ctor_set(x_138, 4, x_137);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_41, x_123, x_139, x_2, x_138);
lean_dec(x_123);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_118);
lean_dec(x_41);
lean_dec(x_2);
x_141 = lean_ctor_get(x_119, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_119, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_143 = x_119;
} else {
 lean_dec_ref(x_119);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_145 = lean_ctor_get(x_12, 1);
x_146 = lean_ctor_get(x_12, 2);
x_147 = lean_ctor_get(x_12, 3);
x_148 = lean_ctor_get(x_12, 4);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_12);
x_149 = lean_ctor_get(x_40, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_40, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_40, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_40, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_40, 5);
lean_inc(x_153);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 x_154 = x_40;
} else {
 lean_dec_ref(x_40);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(0, 6, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_149);
lean_ctor_set(x_155, 1, x_10);
lean_ctor_set(x_155, 2, x_150);
lean_ctor_set(x_155, 3, x_151);
lean_ctor_set(x_155, 4, x_152);
lean_ctor_set(x_155, 5, x_153);
x_156 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_145);
lean_ctor_set(x_156, 2, x_146);
lean_ctor_set(x_156, 3, x_147);
lean_ctor_set(x_156, 4, x_148);
x_157 = lean_ctor_get(x_1, 1);
lean_inc(x_157);
lean_dec(x_1);
lean_inc(x_2);
x_158 = l_Lean_Meta_SynthInstance_getEntry(x_157, x_2, x_156);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_159, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_164 = x_159;
} else {
 lean_dec_ref(x_159);
 x_164 = lean_box(0);
}
x_165 = l_Lean_Meta_SynthInstance_isNewAnswer(x_163, x_41);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_157);
lean_dec(x_41);
lean_dec(x_2);
x_166 = lean_box(0);
if (lean_is_scalar(x_161)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_161;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_160);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_161);
lean_inc(x_41);
x_168 = lean_array_push(x_163, x_41);
lean_inc(x_162);
if (lean_is_scalar(x_164)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_164;
}
lean_ctor_set(x_169, 0, x_162);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_ctor_get(x_160, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_160, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_160, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_160, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_160, 4);
lean_inc(x_174);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 x_175 = x_160;
} else {
 lean_dec_ref(x_160);
 x_175 = lean_box(0);
}
x_176 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_174, x_157, x_169);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(0, 5, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_170);
lean_ctor_set(x_177, 1, x_171);
lean_ctor_set(x_177, 2, x_172);
lean_ctor_set(x_177, 3, x_173);
lean_ctor_set(x_177, 4, x_176);
x_178 = lean_unsigned_to_nat(0u);
x_179 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_41, x_162, x_178, x_2, x_177);
lean_dec(x_162);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_157);
lean_dec(x_41);
lean_dec(x_2);
x_180 = lean_ctor_get(x_158, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_158, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_182 = x_158;
} else {
 lean_dec_ref(x_158);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
}
block_225:
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_187 = lean_ctor_get(x_185, 0);
x_188 = l_Lean_Meta_instantiateMVars(x_6, x_2, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Meta_abstractMVars(x_189, x_2, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_ctor_get(x_192, 2);
lean_inc(x_194);
lean_inc(x_2);
x_195 = l_Lean_Meta_inferType(x_194, x_2, x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
lean_ctor_set(x_185, 0, x_197);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_192);
lean_ctor_set(x_198, 1, x_196);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_11 = x_199;
x_12 = x_185;
goto block_184;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_192);
x_200 = lean_ctor_get(x_195, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_195, 1);
lean_inc(x_201);
lean_dec(x_195);
lean_ctor_set(x_185, 0, x_201);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_200);
x_11 = x_202;
x_12 = x_185;
goto block_184;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_203 = lean_ctor_get(x_185, 0);
x_204 = lean_ctor_get(x_185, 1);
x_205 = lean_ctor_get(x_185, 2);
x_206 = lean_ctor_get(x_185, 3);
x_207 = lean_ctor_get(x_185, 4);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_185);
x_208 = l_Lean_Meta_instantiateMVars(x_6, x_2, x_203);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = l_Lean_Meta_abstractMVars(x_209, x_2, x_210);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_ctor_get(x_212, 2);
lean_inc(x_214);
lean_inc(x_2);
x_215 = l_Lean_Meta_inferType(x_214, x_2, x_213);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_204);
lean_ctor_set(x_218, 2, x_205);
lean_ctor_set(x_218, 3, x_206);
lean_ctor_set(x_218, 4, x_207);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_212);
lean_ctor_set(x_219, 1, x_216);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_11 = x_220;
x_12 = x_218;
goto block_184;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_212);
x_221 = lean_ctor_get(x_215, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_215, 1);
lean_inc(x_222);
lean_dec(x_215);
x_223 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_204);
lean_ctor_set(x_223, 2, x_205);
lean_ctor_set(x_223, 3, x_206);
lean_ctor_set(x_223, 4, x_207);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_221);
x_11 = x_224;
x_12 = x_223;
goto block_184;
}
}
}
block_257:
{
if (x_226 == 0)
{
x_185 = x_227;
goto block_225;
}
else
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_227, 0);
lean_inc(x_2);
lean_inc(x_6);
x_230 = l_Lean_Meta_inferType(x_6, x_2, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
lean_ctor_set(x_227, 0, x_232);
x_233 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_233, 0, x_231);
x_234 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_235 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_234, x_233, x_2, x_227);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_185 = x_236;
goto block_225;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_6);
x_237 = lean_ctor_get(x_230, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_230, 1);
lean_inc(x_238);
lean_dec(x_230);
lean_ctor_set(x_227, 0, x_238);
x_239 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_239, 0, x_237);
x_11 = x_239;
x_12 = x_227;
goto block_184;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_240 = lean_ctor_get(x_227, 0);
x_241 = lean_ctor_get(x_227, 1);
x_242 = lean_ctor_get(x_227, 2);
x_243 = lean_ctor_get(x_227, 3);
x_244 = lean_ctor_get(x_227, 4);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_227);
lean_inc(x_2);
lean_inc(x_6);
x_245 = l_Lean_Meta_inferType(x_6, x_2, x_240);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_241);
lean_ctor_set(x_248, 2, x_242);
lean_ctor_set(x_248, 3, x_243);
lean_ctor_set(x_248, 4, x_244);
x_249 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_249, 0, x_246);
x_250 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_251 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_250, x_249, x_2, x_248);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec(x_251);
x_185 = x_252;
goto block_225;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_6);
x_253 = lean_ctor_get(x_245, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_245, 1);
lean_inc(x_254);
lean_dec(x_245);
x_255 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_241);
lean_ctor_set(x_255, 2, x_242);
lean_ctor_set(x_255, 3, x_243);
lean_ctor_set(x_255, 4, x_244);
x_256 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_256, 0, x_253);
x_11 = x_256;
x_12 = x_255;
goto block_184;
}
}
}
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_336; uint8_t x_361; lean_object* x_362; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_269 = lean_ctor_get(x_4, 0);
x_270 = lean_ctor_get(x_4, 1);
x_271 = lean_ctor_get(x_4, 2);
x_272 = lean_ctor_get(x_4, 3);
x_273 = lean_ctor_get(x_4, 4);
x_274 = lean_ctor_get(x_4, 5);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_4);
x_382 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_382, 0, x_269);
lean_ctor_set(x_382, 1, x_5);
lean_ctor_set(x_382, 2, x_271);
lean_ctor_set(x_382, 3, x_272);
lean_ctor_set(x_382, 4, x_273);
lean_ctor_set(x_382, 5, x_274);
lean_ctor_set(x_3, 0, x_382);
x_383 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_3);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get_uint8(x_384, sizeof(void*)*1);
lean_dec(x_384);
if (x_385 == 0)
{
lean_object* x_386; uint8_t x_387; 
x_386 = lean_ctor_get(x_383, 1);
lean_inc(x_386);
lean_dec(x_383);
x_387 = 0;
x_361 = x_387;
x_362 = x_386;
goto block_381;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_388 = lean_ctor_get(x_383, 1);
lean_inc(x_388);
lean_dec(x_383);
x_389 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_390 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_389, x_2, x_388);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_unbox(x_391);
lean_dec(x_391);
x_361 = x_393;
x_362 = x_392;
goto block_381;
}
block_335:
{
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_2);
lean_dec(x_1);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_275, 0);
lean_inc(x_278);
lean_dec(x_275);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_276, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_276, 3);
lean_inc(x_281);
x_282 = lean_ctor_get(x_276, 4);
lean_inc(x_282);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 lean_ctor_release(x_276, 2);
 lean_ctor_release(x_276, 3);
 lean_ctor_release(x_276, 4);
 x_283 = x_276;
} else {
 lean_dec_ref(x_276);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_277, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_277, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_277, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_277, 4);
lean_inc(x_287);
x_288 = lean_ctor_get(x_277, 5);
lean_inc(x_288);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 lean_ctor_release(x_277, 2);
 lean_ctor_release(x_277, 3);
 lean_ctor_release(x_277, 4);
 lean_ctor_release(x_277, 5);
 x_289 = x_277;
} else {
 lean_dec_ref(x_277);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(0, 6, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_284);
lean_ctor_set(x_290, 1, x_270);
lean_ctor_set(x_290, 2, x_285);
lean_ctor_set(x_290, 3, x_286);
lean_ctor_set(x_290, 4, x_287);
lean_ctor_set(x_290, 5, x_288);
if (lean_is_scalar(x_283)) {
 x_291 = lean_alloc_ctor(0, 5, 0);
} else {
 x_291 = x_283;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_279);
lean_ctor_set(x_291, 2, x_280);
lean_ctor_set(x_291, 3, x_281);
lean_ctor_set(x_291, 4, x_282);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_278);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_293 = lean_ctor_get(x_276, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_275, 0);
lean_inc(x_294);
lean_dec(x_275);
x_295 = lean_ctor_get(x_276, 1);
lean_inc(x_295);
x_296 = lean_ctor_get(x_276, 2);
lean_inc(x_296);
x_297 = lean_ctor_get(x_276, 3);
lean_inc(x_297);
x_298 = lean_ctor_get(x_276, 4);
lean_inc(x_298);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 lean_ctor_release(x_276, 2);
 lean_ctor_release(x_276, 3);
 lean_ctor_release(x_276, 4);
 x_299 = x_276;
} else {
 lean_dec_ref(x_276);
 x_299 = lean_box(0);
}
x_300 = lean_ctor_get(x_293, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_293, 2);
lean_inc(x_301);
x_302 = lean_ctor_get(x_293, 3);
lean_inc(x_302);
x_303 = lean_ctor_get(x_293, 4);
lean_inc(x_303);
x_304 = lean_ctor_get(x_293, 5);
lean_inc(x_304);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 lean_ctor_release(x_293, 2);
 lean_ctor_release(x_293, 3);
 lean_ctor_release(x_293, 4);
 lean_ctor_release(x_293, 5);
 x_305 = x_293;
} else {
 lean_dec_ref(x_293);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(0, 6, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_300);
lean_ctor_set(x_306, 1, x_270);
lean_ctor_set(x_306, 2, x_301);
lean_ctor_set(x_306, 3, x_302);
lean_ctor_set(x_306, 4, x_303);
lean_ctor_set(x_306, 5, x_304);
if (lean_is_scalar(x_299)) {
 x_307 = lean_alloc_ctor(0, 5, 0);
} else {
 x_307 = x_299;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_295);
lean_ctor_set(x_307, 2, x_296);
lean_ctor_set(x_307, 3, x_297);
lean_ctor_set(x_307, 4, x_298);
x_308 = lean_ctor_get(x_1, 1);
lean_inc(x_308);
lean_dec(x_1);
lean_inc(x_2);
x_309 = l_Lean_Meta_SynthInstance_getEntry(x_308, x_2, x_307);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_312 = x_309;
} else {
 lean_dec_ref(x_309);
 x_312 = lean_box(0);
}
x_313 = lean_ctor_get(x_310, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_310, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_315 = x_310;
} else {
 lean_dec_ref(x_310);
 x_315 = lean_box(0);
}
x_316 = l_Lean_Meta_SynthInstance_isNewAnswer(x_314, x_294);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; 
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_308);
lean_dec(x_294);
lean_dec(x_2);
x_317 = lean_box(0);
if (lean_is_scalar(x_312)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_312;
}
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_311);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_312);
lean_inc(x_294);
x_319 = lean_array_push(x_314, x_294);
lean_inc(x_313);
if (lean_is_scalar(x_315)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_315;
}
lean_ctor_set(x_320, 0, x_313);
lean_ctor_set(x_320, 1, x_319);
x_321 = lean_ctor_get(x_311, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_311, 1);
lean_inc(x_322);
x_323 = lean_ctor_get(x_311, 2);
lean_inc(x_323);
x_324 = lean_ctor_get(x_311, 3);
lean_inc(x_324);
x_325 = lean_ctor_get(x_311, 4);
lean_inc(x_325);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 lean_ctor_release(x_311, 2);
 lean_ctor_release(x_311, 3);
 lean_ctor_release(x_311, 4);
 x_326 = x_311;
} else {
 lean_dec_ref(x_311);
 x_326 = lean_box(0);
}
x_327 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_325, x_308, x_320);
if (lean_is_scalar(x_326)) {
 x_328 = lean_alloc_ctor(0, 5, 0);
} else {
 x_328 = x_326;
}
lean_ctor_set(x_328, 0, x_321);
lean_ctor_set(x_328, 1, x_322);
lean_ctor_set(x_328, 2, x_323);
lean_ctor_set(x_328, 3, x_324);
lean_ctor_set(x_328, 4, x_327);
x_329 = lean_unsigned_to_nat(0u);
x_330 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_294, x_313, x_329, x_2, x_328);
lean_dec(x_313);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_308);
lean_dec(x_294);
lean_dec(x_2);
x_331 = lean_ctor_get(x_309, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_309, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_333 = x_309;
} else {
 lean_dec_ref(x_309);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
}
block_360:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
x_339 = lean_ctor_get(x_336, 2);
lean_inc(x_339);
x_340 = lean_ctor_get(x_336, 3);
lean_inc(x_340);
x_341 = lean_ctor_get(x_336, 4);
lean_inc(x_341);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 lean_ctor_release(x_336, 4);
 x_342 = x_336;
} else {
 lean_dec_ref(x_336);
 x_342 = lean_box(0);
}
x_343 = l_Lean_Meta_instantiateMVars(x_6, x_2, x_337);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = l_Lean_Meta_abstractMVars(x_344, x_2, x_345);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
x_349 = lean_ctor_get(x_347, 2);
lean_inc(x_349);
lean_inc(x_2);
x_350 = l_Lean_Meta_inferType(x_349, x_2, x_348);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
if (lean_is_scalar(x_342)) {
 x_353 = lean_alloc_ctor(0, 5, 0);
} else {
 x_353 = x_342;
}
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_338);
lean_ctor_set(x_353, 2, x_339);
lean_ctor_set(x_353, 3, x_340);
lean_ctor_set(x_353, 4, x_341);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_347);
lean_ctor_set(x_354, 1, x_351);
x_355 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_355, 0, x_354);
x_275 = x_355;
x_276 = x_353;
goto block_335;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_347);
x_356 = lean_ctor_get(x_350, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_350, 1);
lean_inc(x_357);
lean_dec(x_350);
if (lean_is_scalar(x_342)) {
 x_358 = lean_alloc_ctor(0, 5, 0);
} else {
 x_358 = x_342;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_338);
lean_ctor_set(x_358, 2, x_339);
lean_ctor_set(x_358, 3, x_340);
lean_ctor_set(x_358, 4, x_341);
x_359 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_359, 0, x_356);
x_275 = x_359;
x_276 = x_358;
goto block_335;
}
}
block_381:
{
if (x_361 == 0)
{
x_336 = x_362;
goto block_360;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_362, 2);
lean_inc(x_365);
x_366 = lean_ctor_get(x_362, 3);
lean_inc(x_366);
x_367 = lean_ctor_get(x_362, 4);
lean_inc(x_367);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 lean_ctor_release(x_362, 2);
 lean_ctor_release(x_362, 3);
 lean_ctor_release(x_362, 4);
 x_368 = x_362;
} else {
 lean_dec_ref(x_362);
 x_368 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_6);
x_369 = l_Lean_Meta_inferType(x_6, x_2, x_363);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
if (lean_is_scalar(x_368)) {
 x_372 = lean_alloc_ctor(0, 5, 0);
} else {
 x_372 = x_368;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_364);
lean_ctor_set(x_372, 2, x_365);
lean_ctor_set(x_372, 3, x_366);
lean_ctor_set(x_372, 4, x_367);
x_373 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_373, 0, x_370);
x_374 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_375 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_374, x_373, x_2, x_372);
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
lean_dec(x_375);
x_336 = x_376;
goto block_360;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_6);
x_377 = lean_ctor_get(x_369, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_369, 1);
lean_inc(x_378);
lean_dec(x_369);
if (lean_is_scalar(x_368)) {
 x_379 = lean_alloc_ctor(0, 5, 0);
} else {
 x_379 = x_368;
}
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_364);
lean_ctor_set(x_379, 2, x_365);
lean_ctor_set(x_379, 3, x_366);
lean_ctor_set(x_379, 4, x_367);
x_380 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_380, 0, x_377);
x_275 = x_380;
x_276 = x_379;
goto block_335;
}
}
}
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_466; uint8_t x_491; lean_object* x_492; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
x_394 = lean_ctor_get(x_3, 1);
x_395 = lean_ctor_get(x_3, 2);
x_396 = lean_ctor_get(x_3, 3);
x_397 = lean_ctor_get(x_3, 4);
lean_inc(x_397);
lean_inc(x_396);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_3);
x_398 = lean_ctor_get(x_4, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_4, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_4, 2);
lean_inc(x_400);
x_401 = lean_ctor_get(x_4, 3);
lean_inc(x_401);
x_402 = lean_ctor_get(x_4, 4);
lean_inc(x_402);
x_403 = lean_ctor_get(x_4, 5);
lean_inc(x_403);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_404 = x_4;
} else {
 lean_dec_ref(x_4);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_512 = lean_alloc_ctor(0, 6, 0);
} else {
 x_512 = x_404;
}
lean_ctor_set(x_512, 0, x_398);
lean_ctor_set(x_512, 1, x_5);
lean_ctor_set(x_512, 2, x_400);
lean_ctor_set(x_512, 3, x_401);
lean_ctor_set(x_512, 4, x_402);
lean_ctor_set(x_512, 5, x_403);
x_513 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_394);
lean_ctor_set(x_513, 2, x_395);
lean_ctor_set(x_513, 3, x_396);
lean_ctor_set(x_513, 4, x_397);
x_514 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_513);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get_uint8(x_515, sizeof(void*)*1);
lean_dec(x_515);
if (x_516 == 0)
{
lean_object* x_517; uint8_t x_518; 
x_517 = lean_ctor_get(x_514, 1);
lean_inc(x_517);
lean_dec(x_514);
x_518 = 0;
x_491 = x_518;
x_492 = x_517;
goto block_511;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; uint8_t x_524; 
x_519 = lean_ctor_get(x_514, 1);
lean_inc(x_519);
lean_dec(x_514);
x_520 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_521 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_520, x_2, x_519);
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
lean_dec(x_521);
x_524 = lean_unbox(x_522);
lean_dec(x_522);
x_491 = x_524;
x_492 = x_523;
goto block_511;
}
block_465:
{
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_2);
lean_dec(x_1);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_405, 0);
lean_inc(x_408);
lean_dec(x_405);
x_409 = lean_ctor_get(x_406, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_406, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_406, 3);
lean_inc(x_411);
x_412 = lean_ctor_get(x_406, 4);
lean_inc(x_412);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 lean_ctor_release(x_406, 2);
 lean_ctor_release(x_406, 3);
 lean_ctor_release(x_406, 4);
 x_413 = x_406;
} else {
 lean_dec_ref(x_406);
 x_413 = lean_box(0);
}
x_414 = lean_ctor_get(x_407, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_407, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_407, 3);
lean_inc(x_416);
x_417 = lean_ctor_get(x_407, 4);
lean_inc(x_417);
x_418 = lean_ctor_get(x_407, 5);
lean_inc(x_418);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 lean_ctor_release(x_407, 2);
 lean_ctor_release(x_407, 3);
 lean_ctor_release(x_407, 4);
 lean_ctor_release(x_407, 5);
 x_419 = x_407;
} else {
 lean_dec_ref(x_407);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(0, 6, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_414);
lean_ctor_set(x_420, 1, x_399);
lean_ctor_set(x_420, 2, x_415);
lean_ctor_set(x_420, 3, x_416);
lean_ctor_set(x_420, 4, x_417);
lean_ctor_set(x_420, 5, x_418);
if (lean_is_scalar(x_413)) {
 x_421 = lean_alloc_ctor(0, 5, 0);
} else {
 x_421 = x_413;
}
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_409);
lean_ctor_set(x_421, 2, x_410);
lean_ctor_set(x_421, 3, x_411);
lean_ctor_set(x_421, 4, x_412);
x_422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_422, 0, x_408);
lean_ctor_set(x_422, 1, x_421);
return x_422;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_423 = lean_ctor_get(x_406, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_405, 0);
lean_inc(x_424);
lean_dec(x_405);
x_425 = lean_ctor_get(x_406, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_406, 2);
lean_inc(x_426);
x_427 = lean_ctor_get(x_406, 3);
lean_inc(x_427);
x_428 = lean_ctor_get(x_406, 4);
lean_inc(x_428);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 lean_ctor_release(x_406, 2);
 lean_ctor_release(x_406, 3);
 lean_ctor_release(x_406, 4);
 x_429 = x_406;
} else {
 lean_dec_ref(x_406);
 x_429 = lean_box(0);
}
x_430 = lean_ctor_get(x_423, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_423, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_423, 3);
lean_inc(x_432);
x_433 = lean_ctor_get(x_423, 4);
lean_inc(x_433);
x_434 = lean_ctor_get(x_423, 5);
lean_inc(x_434);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 lean_ctor_release(x_423, 2);
 lean_ctor_release(x_423, 3);
 lean_ctor_release(x_423, 4);
 lean_ctor_release(x_423, 5);
 x_435 = x_423;
} else {
 lean_dec_ref(x_423);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(0, 6, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_430);
lean_ctor_set(x_436, 1, x_399);
lean_ctor_set(x_436, 2, x_431);
lean_ctor_set(x_436, 3, x_432);
lean_ctor_set(x_436, 4, x_433);
lean_ctor_set(x_436, 5, x_434);
if (lean_is_scalar(x_429)) {
 x_437 = lean_alloc_ctor(0, 5, 0);
} else {
 x_437 = x_429;
}
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_425);
lean_ctor_set(x_437, 2, x_426);
lean_ctor_set(x_437, 3, x_427);
lean_ctor_set(x_437, 4, x_428);
x_438 = lean_ctor_get(x_1, 1);
lean_inc(x_438);
lean_dec(x_1);
lean_inc(x_2);
x_439 = l_Lean_Meta_SynthInstance_getEntry(x_438, x_2, x_437);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_442 = x_439;
} else {
 lean_dec_ref(x_439);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_440, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_440, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_445 = x_440;
} else {
 lean_dec_ref(x_440);
 x_445 = lean_box(0);
}
x_446 = l_Lean_Meta_SynthInstance_isNewAnswer(x_444, x_424);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_445);
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_438);
lean_dec(x_424);
lean_dec(x_2);
x_447 = lean_box(0);
if (lean_is_scalar(x_442)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_442;
}
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_441);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_442);
lean_inc(x_424);
x_449 = lean_array_push(x_444, x_424);
lean_inc(x_443);
if (lean_is_scalar(x_445)) {
 x_450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_450 = x_445;
}
lean_ctor_set(x_450, 0, x_443);
lean_ctor_set(x_450, 1, x_449);
x_451 = lean_ctor_get(x_441, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_441, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_441, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_441, 3);
lean_inc(x_454);
x_455 = lean_ctor_get(x_441, 4);
lean_inc(x_455);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 lean_ctor_release(x_441, 2);
 lean_ctor_release(x_441, 3);
 lean_ctor_release(x_441, 4);
 x_456 = x_441;
} else {
 lean_dec_ref(x_441);
 x_456 = lean_box(0);
}
x_457 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_455, x_438, x_450);
if (lean_is_scalar(x_456)) {
 x_458 = lean_alloc_ctor(0, 5, 0);
} else {
 x_458 = x_456;
}
lean_ctor_set(x_458, 0, x_451);
lean_ctor_set(x_458, 1, x_452);
lean_ctor_set(x_458, 2, x_453);
lean_ctor_set(x_458, 3, x_454);
lean_ctor_set(x_458, 4, x_457);
x_459 = lean_unsigned_to_nat(0u);
x_460 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_424, x_443, x_459, x_2, x_458);
lean_dec(x_443);
return x_460;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_438);
lean_dec(x_424);
lean_dec(x_2);
x_461 = lean_ctor_get(x_439, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_439, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_463 = x_439;
} else {
 lean_dec_ref(x_439);
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
}
block_490:
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
x_469 = lean_ctor_get(x_466, 2);
lean_inc(x_469);
x_470 = lean_ctor_get(x_466, 3);
lean_inc(x_470);
x_471 = lean_ctor_get(x_466, 4);
lean_inc(x_471);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 lean_ctor_release(x_466, 3);
 lean_ctor_release(x_466, 4);
 x_472 = x_466;
} else {
 lean_dec_ref(x_466);
 x_472 = lean_box(0);
}
x_473 = l_Lean_Meta_instantiateMVars(x_6, x_2, x_467);
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
lean_dec(x_473);
x_476 = l_Lean_Meta_abstractMVars(x_474, x_2, x_475);
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
x_479 = lean_ctor_get(x_477, 2);
lean_inc(x_479);
lean_inc(x_2);
x_480 = l_Lean_Meta_inferType(x_479, x_2, x_478);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec(x_480);
if (lean_is_scalar(x_472)) {
 x_483 = lean_alloc_ctor(0, 5, 0);
} else {
 x_483 = x_472;
}
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_468);
lean_ctor_set(x_483, 2, x_469);
lean_ctor_set(x_483, 3, x_470);
lean_ctor_set(x_483, 4, x_471);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_477);
lean_ctor_set(x_484, 1, x_481);
x_485 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_485, 0, x_484);
x_405 = x_485;
x_406 = x_483;
goto block_465;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_dec(x_477);
x_486 = lean_ctor_get(x_480, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_480, 1);
lean_inc(x_487);
lean_dec(x_480);
if (lean_is_scalar(x_472)) {
 x_488 = lean_alloc_ctor(0, 5, 0);
} else {
 x_488 = x_472;
}
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_468);
lean_ctor_set(x_488, 2, x_469);
lean_ctor_set(x_488, 3, x_470);
lean_ctor_set(x_488, 4, x_471);
x_489 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_489, 0, x_486);
x_405 = x_489;
x_406 = x_488;
goto block_465;
}
}
block_511:
{
if (x_491 == 0)
{
x_466 = x_492;
goto block_490;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
x_495 = lean_ctor_get(x_492, 2);
lean_inc(x_495);
x_496 = lean_ctor_get(x_492, 3);
lean_inc(x_496);
x_497 = lean_ctor_get(x_492, 4);
lean_inc(x_497);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 lean_ctor_release(x_492, 2);
 lean_ctor_release(x_492, 3);
 lean_ctor_release(x_492, 4);
 x_498 = x_492;
} else {
 lean_dec_ref(x_492);
 x_498 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_6);
x_499 = l_Lean_Meta_inferType(x_6, x_2, x_493);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec(x_499);
if (lean_is_scalar(x_498)) {
 x_502 = lean_alloc_ctor(0, 5, 0);
} else {
 x_502 = x_498;
}
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_494);
lean_ctor_set(x_502, 2, x_495);
lean_ctor_set(x_502, 3, x_496);
lean_ctor_set(x_502, 4, x_497);
x_503 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_503, 0, x_500);
x_504 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_505 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_504, x_503, x_2, x_502);
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
lean_dec(x_505);
x_466 = x_506;
goto block_490;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_6);
x_507 = lean_ctor_get(x_499, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_499, 1);
lean_inc(x_508);
lean_dec(x_499);
if (lean_is_scalar(x_498)) {
 x_509 = lean_alloc_ctor(0, 5, 0);
} else {
 x_509 = x_498;
}
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_494);
lean_ctor_set(x_509, 2, x_495);
lean_ctor_set(x_509, 3, x_496);
lean_ctor_set(x_509, 4, x_497);
x_510 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_510, 0, x_507);
x_405 = x_510;
x_406 = x_509;
goto block_465;
}
}
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_array_push(x_5, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
lean_object* l_Lean_Meta_SynthInstance_consume(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SynthInstance_addAnswer(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_8);
x_9 = l_Lean_Meta_SynthInstance_mkTableKeyFor(x_8, x_6, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_10, x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_SynthInstance_newSubgoal(x_8, x_10, x_6, x_7, x_2, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_17, 3);
x_22 = lean_ctor_get(x_17, 4);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(x_1, x_19, x_24, x_25, x_21);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_19, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_array_push(x_23, x_7);
lean_ctor_set(x_19, 0, x_30);
x_31 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_22, x_10, x_19);
lean_ctor_set(x_17, 4, x_31);
lean_ctor_set(x_17, 3, x_26);
x_32 = lean_box(0);
lean_ctor_set(x_12, 0, x_32);
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_19);
x_33 = lean_array_push(x_23, x_7);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
x_35 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_22, x_10, x_34);
lean_ctor_set(x_17, 4, x_35);
lean_ctor_set(x_17, 3, x_26);
x_36 = lean_box(0);
lean_ctor_set(x_12, 0, x_36);
return x_12;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
x_39 = lean_ctor_get(x_17, 2);
x_40 = lean_ctor_get(x_17, 3);
x_41 = lean_ctor_get(x_17, 4);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(x_1, x_19, x_43, x_44, x_40);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_46 = x_19;
} else {
 lean_dec_ref(x_19);
 x_46 = lean_box(0);
}
x_47 = lean_array_push(x_42, x_7);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
x_49 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_41, x_10, x_48);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_37);
lean_ctor_set(x_50, 1, x_38);
lean_ctor_set(x_50, 2, x_39);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_49);
x_51 = lean_box(0);
lean_ctor_set(x_12, 1, x_50);
lean_ctor_set(x_12, 0, x_51);
return x_12;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_ctor_get(x_13, 0);
lean_inc(x_53);
lean_dec(x_13);
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
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(x_1, x_53, x_61, x_62, x_57);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_64 = x_53;
} else {
 lean_dec_ref(x_53);
 x_64 = lean_box(0);
}
x_65 = lean_array_push(x_60, x_7);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
x_67 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_58, x_10, x_66);
if (lean_is_scalar(x_59)) {
 x_68 = lean_alloc_ctor(0, 5, 0);
} else {
 x_68 = x_59;
}
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_55);
lean_ctor_set(x_68, 2, x_56);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_67);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_9);
if (x_71 == 0)
{
return x_9;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_9, 0);
x_73 = lean_ctor_get(x_9, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_9);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_SynthInstance_getTop___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1(x_2);
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_getTop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getTop___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_getTop___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_getTop(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_modifyTop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
x_9 = lean_nat_dec_lt(x_8, x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_array_fget(x_5, x_8);
x_13 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_14 = lean_array_fset(x_5, x_8, x_13);
x_15 = lean_apply_1(x_1, x_12);
x_16 = lean_array_fset(x_14, x_8, x_15);
lean_dec(x_8);
lean_ctor_set(x_3, 2, x_16);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_ctor_get(x_3, 3);
x_23 = lean_ctor_get(x_3, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_24 = lean_array_get_size(x_21);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
x_27 = lean_nat_dec_lt(x_26, x_24);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set(x_28, 4, x_23);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_array_fget(x_21, x_26);
x_32 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_33 = lean_array_fset(x_21, x_26, x_32);
x_34 = lean_apply_1(x_1, x_31);
x_35 = lean_array_fset(x_33, x_26, x_34);
lean_dec(x_26);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_20);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_22);
lean_ctor_set(x_36, 4, x_23);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_modifyTop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_modifyTop(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("generate");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_generate___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instance ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_generate___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_generate___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_generate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_SynthInstance_getTop___rarg(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_free_object(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
x_16 = l_Lean_Expr_Inhabited;
x_17 = lean_array_get(x_16, x_10, x_15);
lean_dec(x_10);
x_141 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_6);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_18 = x_144;
goto block_140;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_dec(x_141);
x_146 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_147 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_146, x_1, x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_18 = x_150;
goto block_140;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
lean_dec(x_147);
lean_inc(x_17);
x_152 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_152, 0, x_17);
x_153 = l_Lean_Meta_SynthInstance_generate___closed__5;
x_154 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_146, x_154, x_1, x_151);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_18 = x_156;
goto block_140;
}
}
block_140:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 2);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_sub(x_21, x_14);
x_23 = lean_nat_dec_lt(x_22, x_21);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_15);
lean_inc(x_1);
lean_inc(x_7);
x_24 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_17, x_1, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_8);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = l_Lean_Meta_SynthInstance_consume(x_36, x_1, x_33);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
return x_24;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_24);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_array_fget(x_20, x_22);
x_43 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_44 = lean_array_fset(x_20, x_22, x_43);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 4);
lean_dec(x_46);
lean_ctor_set(x_42, 4, x_15);
x_47 = lean_array_fset(x_44, x_22, x_42);
lean_dec(x_22);
lean_ctor_set(x_18, 2, x_47);
lean_inc(x_1);
lean_inc(x_7);
x_48 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_17, x_1, x_18);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_48, 0, x_52);
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_dec(x_48);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_dec(x_48);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_7);
lean_ctor_set(x_60, 1, x_8);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set(x_60, 3, x_59);
x_61 = l_Lean_Meta_SynthInstance_consume(x_60, x_1, x_57);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_48);
if (x_62 == 0)
{
return x_48;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_48, 0);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_48);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_42, 0);
x_67 = lean_ctor_get(x_42, 1);
x_68 = lean_ctor_get(x_42, 2);
x_69 = lean_ctor_get(x_42, 3);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_42);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_69);
lean_ctor_set(x_70, 4, x_15);
x_71 = lean_array_fset(x_44, x_22, x_70);
lean_dec(x_22);
lean_ctor_set(x_18, 2, x_71);
lean_inc(x_1);
lean_inc(x_7);
x_72 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_17, x_1, x_18);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
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
x_76 = lean_box(0);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_82, 0, x_7);
lean_ctor_set(x_82, 1, x_8);
lean_ctor_set(x_82, 2, x_80);
lean_ctor_set(x_82, 3, x_81);
x_83 = l_Lean_Meta_SynthInstance_consume(x_82, x_1, x_79);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_84 = lean_ctor_get(x_72, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_72, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_86 = x_72;
} else {
 lean_dec_ref(x_72);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_88 = lean_ctor_get(x_18, 0);
x_89 = lean_ctor_get(x_18, 1);
x_90 = lean_ctor_get(x_18, 2);
x_91 = lean_ctor_get(x_18, 3);
x_92 = lean_ctor_get(x_18, 4);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_18);
x_93 = lean_array_get_size(x_90);
x_94 = lean_nat_sub(x_93, x_14);
x_95 = lean_nat_dec_lt(x_94, x_93);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_94);
lean_dec(x_15);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_88);
lean_ctor_set(x_96, 1, x_89);
lean_ctor_set(x_96, 2, x_90);
lean_ctor_set(x_96, 3, x_91);
lean_ctor_set(x_96, 4, x_92);
lean_inc(x_1);
lean_inc(x_7);
x_97 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_17, x_1, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
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
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_98, 0);
lean_inc(x_103);
lean_dec(x_98);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_dec(x_97);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_107, 0, x_7);
lean_ctor_set(x_107, 1, x_8);
lean_ctor_set(x_107, 2, x_105);
lean_ctor_set(x_107, 3, x_106);
x_108 = l_Lean_Meta_SynthInstance_consume(x_107, x_1, x_104);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_109 = lean_ctor_get(x_97, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_97, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_111 = x_97;
} else {
 lean_dec_ref(x_97);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_113 = lean_array_fget(x_90, x_94);
x_114 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_115 = lean_array_fset(x_90, x_94, x_114);
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 3);
lean_inc(x_119);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 x_120 = x_113;
} else {
 lean_dec_ref(x_113);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 5, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_117);
lean_ctor_set(x_121, 2, x_118);
lean_ctor_set(x_121, 3, x_119);
lean_ctor_set(x_121, 4, x_15);
x_122 = lean_array_fset(x_115, x_94, x_121);
lean_dec(x_94);
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_88);
lean_ctor_set(x_123, 1, x_89);
lean_ctor_set(x_123, 2, x_122);
lean_ctor_set(x_123, 3, x_91);
lean_ctor_set(x_123, 4, x_92);
lean_inc(x_1);
lean_inc(x_7);
x_124 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_17, x_1, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
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
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_7);
lean_ctor_set(x_134, 1, x_8);
lean_ctor_set(x_134, 2, x_132);
lean_ctor_set(x_134, 3, x_133);
x_135 = l_Lean_Meta_SynthInstance_consume(x_134, x_1, x_131);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_136 = lean_ctor_get(x_124, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_124, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_138 = x_124;
} else {
 lean_dec_ref(x_124);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_6);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_6, 2);
x_159 = lean_array_pop(x_158);
lean_ctor_set(x_6, 2, x_159);
x_160 = lean_box(0);
lean_ctor_set(x_3, 0, x_160);
return x_3;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_161 = lean_ctor_get(x_6, 0);
x_162 = lean_ctor_get(x_6, 1);
x_163 = lean_ctor_get(x_6, 2);
x_164 = lean_ctor_get(x_6, 3);
x_165 = lean_ctor_get(x_6, 4);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_6);
x_166 = lean_array_pop(x_163);
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_166);
lean_ctor_set(x_167, 3, x_164);
lean_ctor_set(x_167, 4, x_165);
x_168 = lean_box(0);
lean_ctor_set(x_3, 1, x_167);
lean_ctor_set(x_3, 0, x_168);
return x_3;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_169 = lean_ctor_get(x_3, 0);
x_170 = lean_ctor_get(x_3, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_3);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_169, 4);
lean_inc(x_175);
lean_dec(x_169);
x_176 = lean_unsigned_to_nat(0u);
x_177 = lean_nat_dec_eq(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_178 = lean_unsigned_to_nat(1u);
x_179 = lean_nat_sub(x_175, x_178);
lean_dec(x_175);
x_180 = l_Lean_Expr_Inhabited;
x_181 = lean_array_get(x_180, x_174, x_179);
lean_dec(x_174);
x_237 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_170);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get_uint8(x_238, sizeof(void*)*1);
lean_dec(x_238);
if (x_239 == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_182 = x_240;
goto block_236;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
lean_dec(x_237);
x_242 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_243 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_242, x_1, x_241);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_unbox(x_244);
lean_dec(x_244);
if (x_245 == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
lean_dec(x_243);
x_182 = x_246;
goto block_236;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_247 = lean_ctor_get(x_243, 1);
lean_inc(x_247);
lean_dec(x_243);
lean_inc(x_181);
x_248 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_248, 0, x_181);
x_249 = l_Lean_Meta_SynthInstance_generate___closed__5;
x_250 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_251 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_242, x_250, x_1, x_247);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec(x_251);
x_182 = x_252;
goto block_236;
}
}
block_236:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 3);
lean_inc(x_186);
x_187 = lean_ctor_get(x_182, 4);
lean_inc(x_187);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 lean_ctor_release(x_182, 3);
 lean_ctor_release(x_182, 4);
 x_188 = x_182;
} else {
 lean_dec_ref(x_182);
 x_188 = lean_box(0);
}
x_189 = lean_array_get_size(x_185);
x_190 = lean_nat_sub(x_189, x_178);
x_191 = lean_nat_dec_lt(x_190, x_189);
lean_dec(x_189);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_190);
lean_dec(x_179);
if (lean_is_scalar(x_188)) {
 x_192 = lean_alloc_ctor(0, 5, 0);
} else {
 x_192 = x_188;
}
lean_ctor_set(x_192, 0, x_183);
lean_ctor_set(x_192, 1, x_184);
lean_ctor_set(x_192, 2, x_185);
lean_ctor_set(x_192, 3, x_186);
lean_ctor_set(x_192, 4, x_187);
lean_inc(x_1);
lean_inc(x_171);
x_193 = l_Lean_Meta_SynthInstance_tryResolve(x_173, x_171, x_181, x_1, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_1);
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
x_197 = lean_box(0);
if (lean_is_scalar(x_196)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_196;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_195);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_199 = lean_ctor_get(x_194, 0);
lean_inc(x_199);
lean_dec(x_194);
x_200 = lean_ctor_get(x_193, 1);
lean_inc(x_200);
lean_dec(x_193);
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_dec(x_199);
x_203 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_203, 0, x_171);
lean_ctor_set(x_203, 1, x_172);
lean_ctor_set(x_203, 2, x_201);
lean_ctor_set(x_203, 3, x_202);
x_204 = l_Lean_Meta_SynthInstance_consume(x_203, x_1, x_200);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_1);
x_205 = lean_ctor_get(x_193, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_193, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_207 = x_193;
} else {
 lean_dec_ref(x_193);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_209 = lean_array_fget(x_185, x_190);
x_210 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_211 = lean_array_fset(x_185, x_190, x_210);
x_212 = lean_ctor_get(x_209, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_209, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_209, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_209, 3);
lean_inc(x_215);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 lean_ctor_release(x_209, 2);
 lean_ctor_release(x_209, 3);
 lean_ctor_release(x_209, 4);
 x_216 = x_209;
} else {
 lean_dec_ref(x_209);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 5, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_212);
lean_ctor_set(x_217, 1, x_213);
lean_ctor_set(x_217, 2, x_214);
lean_ctor_set(x_217, 3, x_215);
lean_ctor_set(x_217, 4, x_179);
x_218 = lean_array_fset(x_211, x_190, x_217);
lean_dec(x_190);
if (lean_is_scalar(x_188)) {
 x_219 = lean_alloc_ctor(0, 5, 0);
} else {
 x_219 = x_188;
}
lean_ctor_set(x_219, 0, x_183);
lean_ctor_set(x_219, 1, x_184);
lean_ctor_set(x_219, 2, x_218);
lean_ctor_set(x_219, 3, x_186);
lean_ctor_set(x_219, 4, x_187);
lean_inc(x_1);
lean_inc(x_171);
x_220 = l_Lean_Meta_SynthInstance_tryResolve(x_173, x_171, x_181, x_1, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_1);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_224 = lean_box(0);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_222);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = lean_ctor_get(x_221, 0);
lean_inc(x_226);
lean_dec(x_221);
x_227 = lean_ctor_get(x_220, 1);
lean_inc(x_227);
lean_dec(x_220);
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_229);
lean_dec(x_226);
x_230 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_230, 0, x_171);
lean_ctor_set(x_230, 1, x_172);
lean_ctor_set(x_230, 2, x_228);
lean_ctor_set(x_230, 3, x_229);
x_231 = l_Lean_Meta_SynthInstance_consume(x_230, x_1, x_227);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_1);
x_232 = lean_ctor_get(x_220, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_220, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_234 = x_220;
} else {
 lean_dec_ref(x_220);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_1);
x_253 = lean_ctor_get(x_170, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_170, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_170, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_170, 3);
lean_inc(x_256);
x_257 = lean_ctor_get(x_170, 4);
lean_inc(x_257);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 x_258 = x_170;
} else {
 lean_dec_ref(x_170);
 x_258 = lean_box(0);
}
x_259 = lean_array_pop(x_255);
if (lean_is_scalar(x_258)) {
 x_260 = lean_alloc_ctor(0, 5, 0);
} else {
 x_260 = x_258;
}
lean_ctor_set(x_260, 0, x_253);
lean_ctor_set(x_260, 1, x_254);
lean_ctor_set(x_260, 2, x_259);
lean_ctor_set(x_260, 3, x_256);
lean_ctor_set(x_260, 4, x_257);
x_261 = lean_box(0);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
}
}
lean_object* _init_l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_Consumernode_inhabited;
x_2 = l_Lean_Meta_SynthInstance_Answer_inhabited;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(x_3);
x_5 = lean_array_pop(x_3);
lean_ctor_set(x_1, 3, x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_12 = l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(x_10);
x_13 = lean_array_pop(x_10);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Meta_SynthInstance_getNextToResume(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getNextToResume___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_getNextToResume___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_getNextToResume(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resume found no remaining subgoals");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
x_2 = lean_unsigned_to_nat(427u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Lean_Meta_SynthInstance_resume___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resume");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_resume___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" <== ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_resume(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Meta_SynthInstance_getNextToResume___rarg(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_Meta_SynthInstance_getEntry___closed__1;
x_9 = l_Lean_Meta_SynthInstance_resume___closed__2;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_apply_2(x_10, x_1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
lean_inc(x_1);
lean_inc(x_19);
x_21 = l_Lean_Meta_SynthInstance_tryAnswer(x_17, x_19, x_13, x_1, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_20);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_30 = x_21;
} else {
 lean_dec_ref(x_21);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
lean_inc(x_31);
lean_inc(x_15);
lean_ctor_set(x_5, 3, x_20);
lean_ctor_set(x_5, 2, x_31);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_92; lean_object* x_93; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_35 = lean_ctor_get(x_33, 1);
lean_ctor_set(x_33, 1, x_31);
x_150 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_29);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get_uint8(x_151, sizeof(void*)*1);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = 0;
x_92 = x_154;
x_93 = x_153;
goto block_149;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_155 = lean_ctor_get(x_150, 1);
lean_inc(x_155);
lean_dec(x_150);
x_156 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_157 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_156, x_1, x_155);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_unbox(x_158);
lean_dec(x_158);
x_92 = x_160;
x_93 = x_159;
goto block_149;
}
block_91:
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_1);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
lean_ctor_set(x_38, 1, x_35);
if (lean_is_scalar(x_30)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_30;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 2);
x_47 = lean_ctor_get(x_38, 3);
x_48 = lean_ctor_get(x_38, 4);
x_49 = lean_ctor_get(x_38, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_35);
lean_ctor_set(x_50, 2, x_46);
lean_ctor_set(x_50, 3, x_47);
lean_ctor_set(x_50, 4, x_48);
lean_ctor_set(x_50, 5, x_49);
lean_ctor_set(x_37, 0, x_50);
if (lean_is_scalar(x_30)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_30;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_37);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_37, 1);
x_53 = lean_ctor_get(x_37, 2);
x_54 = lean_ctor_get(x_37, 3);
x_55 = lean_ctor_get(x_37, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_37);
x_56 = lean_ctor_get(x_38, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_38, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_38, 3);
lean_inc(x_58);
x_59 = lean_ctor_get(x_38, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_38, 5);
lean_inc(x_60);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 x_61 = x_38;
} else {
 lean_dec_ref(x_38);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 6, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_35);
lean_ctor_set(x_62, 2, x_57);
lean_ctor_set(x_62, 3, x_58);
lean_ctor_set(x_62, 4, x_59);
lean_ctor_set(x_62, 5, x_60);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_52);
lean_ctor_set(x_63, 2, x_53);
lean_ctor_set(x_63, 3, x_54);
lean_ctor_set(x_63, 4, x_55);
if (lean_is_scalar(x_30)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_30;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_39);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_36);
lean_dec(x_30);
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_37, 0);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 1);
lean_dec(x_68);
lean_ctor_set(x_66, 1, x_35);
x_69 = l_Lean_Meta_SynthInstance_consume(x_5, x_1, x_37);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_ctor_get(x_66, 2);
x_72 = lean_ctor_get(x_66, 3);
x_73 = lean_ctor_get(x_66, 4);
x_74 = lean_ctor_get(x_66, 5);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_66);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_35);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_72);
lean_ctor_set(x_75, 4, x_73);
lean_ctor_set(x_75, 5, x_74);
lean_ctor_set(x_37, 0, x_75);
x_76 = l_Lean_Meta_SynthInstance_consume(x_5, x_1, x_37);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_77 = lean_ctor_get(x_37, 0);
x_78 = lean_ctor_get(x_37, 1);
x_79 = lean_ctor_get(x_37, 2);
x_80 = lean_ctor_get(x_37, 3);
x_81 = lean_ctor_get(x_37, 4);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_37);
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 4);
lean_inc(x_85);
x_86 = lean_ctor_get(x_77, 5);
lean_inc(x_86);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 x_87 = x_77;
} else {
 lean_dec_ref(x_77);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 6, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_35);
lean_ctor_set(x_88, 2, x_83);
lean_ctor_set(x_88, 3, x_84);
lean_ctor_set(x_88, 4, x_85);
lean_ctor_set(x_88, 5, x_86);
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_78);
lean_ctor_set(x_89, 2, x_79);
lean_ctor_set(x_89, 3, x_80);
lean_ctor_set(x_89, 4, x_81);
x_90 = l_Lean_Meta_SynthInstance_consume(x_5, x_1, x_89);
return x_90;
}
}
}
block_149:
{
if (x_92 == 0)
{
lean_object* x_94; 
lean_dec(x_19);
lean_dec(x_15);
x_94 = l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
x_36 = x_94;
x_37 = x_93;
goto block_91;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_1);
x_97 = l_Lean_Meta_inferType(x_15, x_1, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_1);
x_100 = l_Lean_Meta_inferType(x_19, x_1, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_ctor_set(x_93, 0, x_102);
x_103 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_104 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_105 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_107 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_109 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_108, x_107, x_1, x_93);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_110);
x_36 = x_112;
x_37 = x_111;
goto block_91;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_98);
x_113 = lean_ctor_get(x_100, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_100, 1);
lean_inc(x_114);
lean_dec(x_100);
lean_ctor_set(x_93, 0, x_114);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_113);
x_36 = x_115;
x_37 = x_93;
goto block_91;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_19);
x_116 = lean_ctor_get(x_97, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_97, 1);
lean_inc(x_117);
lean_dec(x_97);
lean_ctor_set(x_93, 0, x_117);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_116);
x_36 = x_118;
x_37 = x_93;
goto block_91;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_93, 0);
x_120 = lean_ctor_get(x_93, 1);
x_121 = lean_ctor_get(x_93, 2);
x_122 = lean_ctor_get(x_93, 3);
x_123 = lean_ctor_get(x_93, 4);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_93);
lean_inc(x_1);
x_124 = l_Lean_Meta_inferType(x_15, x_1, x_119);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_1);
x_127 = l_Lean_Meta_inferType(x_19, x_1, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_120);
lean_ctor_set(x_130, 2, x_121);
lean_ctor_set(x_130, 3, x_122);
lean_ctor_set(x_130, 4, x_123);
x_131 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_131, 0, x_125);
x_132 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_133 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_134, 0, x_128);
x_135 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_137 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_136, x_135, x_1, x_130);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_138);
x_36 = x_140;
x_37 = x_139;
goto block_91;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_125);
x_141 = lean_ctor_get(x_127, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_127, 1);
lean_inc(x_142);
lean_dec(x_127);
x_143 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_120);
lean_ctor_set(x_143, 2, x_121);
lean_ctor_set(x_143, 3, x_122);
lean_ctor_set(x_143, 4, x_123);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_141);
x_36 = x_144;
x_37 = x_143;
goto block_91;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_19);
x_145 = lean_ctor_get(x_124, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_124, 1);
lean_inc(x_146);
lean_dec(x_124);
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_120);
lean_ctor_set(x_147, 2, x_121);
lean_ctor_set(x_147, 3, x_122);
lean_ctor_set(x_147, 4, x_123);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_145);
x_36 = x_148;
x_37 = x_147;
goto block_91;
}
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_201; lean_object* x_202; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_161 = lean_ctor_get(x_33, 0);
x_162 = lean_ctor_get(x_33, 1);
x_163 = lean_ctor_get(x_33, 2);
x_164 = lean_ctor_get(x_33, 3);
x_165 = lean_ctor_get(x_33, 4);
x_166 = lean_ctor_get(x_33, 5);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_33);
x_236 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_236, 0, x_161);
lean_ctor_set(x_236, 1, x_31);
lean_ctor_set(x_236, 2, x_163);
lean_ctor_set(x_236, 3, x_164);
lean_ctor_set(x_236, 4, x_165);
lean_ctor_set(x_236, 5, x_166);
lean_ctor_set(x_29, 0, x_236);
x_237 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_29);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get_uint8(x_238, sizeof(void*)*1);
lean_dec(x_238);
if (x_239 == 0)
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = 0;
x_201 = x_241;
x_202 = x_240;
goto block_235;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_242 = lean_ctor_get(x_237, 1);
lean_inc(x_242);
lean_dec(x_237);
x_243 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_244 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_243, x_1, x_242);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_unbox(x_245);
lean_dec(x_245);
x_201 = x_247;
x_202 = x_246;
goto block_235;
}
block_200:
{
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_5);
lean_dec(x_1);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 0);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_168, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_168, 4);
lean_inc(x_174);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 x_175 = x_168;
} else {
 lean_dec_ref(x_168);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_169, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_169, 2);
lean_inc(x_177);
x_178 = lean_ctor_get(x_169, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_169, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_169, 5);
lean_inc(x_180);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 lean_ctor_release(x_169, 4);
 lean_ctor_release(x_169, 5);
 x_181 = x_169;
} else {
 lean_dec_ref(x_169);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 6, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_176);
lean_ctor_set(x_182, 1, x_162);
lean_ctor_set(x_182, 2, x_177);
lean_ctor_set(x_182, 3, x_178);
lean_ctor_set(x_182, 4, x_179);
lean_ctor_set(x_182, 5, x_180);
if (lean_is_scalar(x_175)) {
 x_183 = lean_alloc_ctor(0, 5, 0);
} else {
 x_183 = x_175;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_171);
lean_ctor_set(x_183, 2, x_172);
lean_ctor_set(x_183, 3, x_173);
lean_ctor_set(x_183, 4, x_174);
if (lean_is_scalar(x_30)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_30;
 lean_ctor_set_tag(x_184, 1);
}
lean_ctor_set(x_184, 0, x_170);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_167);
lean_dec(x_30);
x_185 = lean_ctor_get(x_168, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_168, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_168, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_168, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_168, 4);
lean_inc(x_189);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 x_190 = x_168;
} else {
 lean_dec_ref(x_168);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_185, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_185, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_185, 3);
lean_inc(x_193);
x_194 = lean_ctor_get(x_185, 4);
lean_inc(x_194);
x_195 = lean_ctor_get(x_185, 5);
lean_inc(x_195);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 lean_ctor_release(x_185, 4);
 lean_ctor_release(x_185, 5);
 x_196 = x_185;
} else {
 lean_dec_ref(x_185);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 6, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_191);
lean_ctor_set(x_197, 1, x_162);
lean_ctor_set(x_197, 2, x_192);
lean_ctor_set(x_197, 3, x_193);
lean_ctor_set(x_197, 4, x_194);
lean_ctor_set(x_197, 5, x_195);
if (lean_is_scalar(x_190)) {
 x_198 = lean_alloc_ctor(0, 5, 0);
} else {
 x_198 = x_190;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_186);
lean_ctor_set(x_198, 2, x_187);
lean_ctor_set(x_198, 3, x_188);
lean_ctor_set(x_198, 4, x_189);
x_199 = l_Lean_Meta_SynthInstance_consume(x_5, x_1, x_198);
return x_199;
}
}
block_235:
{
if (x_201 == 0)
{
lean_object* x_203; 
lean_dec(x_19);
lean_dec(x_15);
x_203 = l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
x_167 = x_203;
x_168 = x_202;
goto block_200;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_202, 2);
lean_inc(x_206);
x_207 = lean_ctor_get(x_202, 3);
lean_inc(x_207);
x_208 = lean_ctor_get(x_202, 4);
lean_inc(x_208);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 lean_ctor_release(x_202, 3);
 lean_ctor_release(x_202, 4);
 x_209 = x_202;
} else {
 lean_dec_ref(x_202);
 x_209 = lean_box(0);
}
lean_inc(x_1);
x_210 = l_Lean_Meta_inferType(x_15, x_1, x_204);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
lean_inc(x_1);
x_213 = l_Lean_Meta_inferType(x_19, x_1, x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
if (lean_is_scalar(x_209)) {
 x_216 = lean_alloc_ctor(0, 5, 0);
} else {
 x_216 = x_209;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_205);
lean_ctor_set(x_216, 2, x_206);
lean_ctor_set(x_216, 3, x_207);
lean_ctor_set(x_216, 4, x_208);
x_217 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_217, 0, x_211);
x_218 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_219 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_220, 0, x_214);
x_221 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_222 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_223 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_222, x_221, x_1, x_216);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_224);
x_167 = x_226;
x_168 = x_225;
goto block_200;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_211);
x_227 = lean_ctor_get(x_213, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_213, 1);
lean_inc(x_228);
lean_dec(x_213);
if (lean_is_scalar(x_209)) {
 x_229 = lean_alloc_ctor(0, 5, 0);
} else {
 x_229 = x_209;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_205);
lean_ctor_set(x_229, 2, x_206);
lean_ctor_set(x_229, 3, x_207);
lean_ctor_set(x_229, 4, x_208);
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_227);
x_167 = x_230;
x_168 = x_229;
goto block_200;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_19);
x_231 = lean_ctor_get(x_210, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_210, 1);
lean_inc(x_232);
lean_dec(x_210);
if (lean_is_scalar(x_209)) {
 x_233 = lean_alloc_ctor(0, 5, 0);
} else {
 x_233 = x_209;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_205);
lean_ctor_set(x_233, 2, x_206);
lean_ctor_set(x_233, 3, x_207);
lean_ctor_set(x_233, 4, x_208);
x_234 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_234, 0, x_231);
x_167 = x_234;
x_168 = x_233;
goto block_200;
}
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_294; lean_object* x_295; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_248 = lean_ctor_get(x_29, 0);
x_249 = lean_ctor_get(x_29, 1);
x_250 = lean_ctor_get(x_29, 2);
x_251 = lean_ctor_get(x_29, 3);
x_252 = lean_ctor_get(x_29, 4);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_29);
x_253 = lean_ctor_get(x_248, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_248, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_248, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_248, 3);
lean_inc(x_256);
x_257 = lean_ctor_get(x_248, 4);
lean_inc(x_257);
x_258 = lean_ctor_get(x_248, 5);
lean_inc(x_258);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 lean_ctor_release(x_248, 2);
 lean_ctor_release(x_248, 3);
 lean_ctor_release(x_248, 4);
 lean_ctor_release(x_248, 5);
 x_259 = x_248;
} else {
 lean_dec_ref(x_248);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_329 = lean_alloc_ctor(0, 6, 0);
} else {
 x_329 = x_259;
}
lean_ctor_set(x_329, 0, x_253);
lean_ctor_set(x_329, 1, x_31);
lean_ctor_set(x_329, 2, x_255);
lean_ctor_set(x_329, 3, x_256);
lean_ctor_set(x_329, 4, x_257);
lean_ctor_set(x_329, 5, x_258);
x_330 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_249);
lean_ctor_set(x_330, 2, x_250);
lean_ctor_set(x_330, 3, x_251);
lean_ctor_set(x_330, 4, x_252);
x_331 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_330);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get_uint8(x_332, sizeof(void*)*1);
lean_dec(x_332);
if (x_333 == 0)
{
lean_object* x_334; uint8_t x_335; 
x_334 = lean_ctor_get(x_331, 1);
lean_inc(x_334);
lean_dec(x_331);
x_335 = 0;
x_294 = x_335;
x_295 = x_334;
goto block_328;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_336 = lean_ctor_get(x_331, 1);
lean_inc(x_336);
lean_dec(x_331);
x_337 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_338 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_337, x_1, x_336);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_unbox(x_339);
lean_dec(x_339);
x_294 = x_341;
x_295 = x_340;
goto block_328;
}
block_293:
{
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_5);
lean_dec(x_1);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_260, 0);
lean_inc(x_263);
lean_dec(x_260);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_261, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_261, 3);
lean_inc(x_266);
x_267 = lean_ctor_get(x_261, 4);
lean_inc(x_267);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 lean_ctor_release(x_261, 4);
 x_268 = x_261;
} else {
 lean_dec_ref(x_261);
 x_268 = lean_box(0);
}
x_269 = lean_ctor_get(x_262, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_262, 2);
lean_inc(x_270);
x_271 = lean_ctor_get(x_262, 3);
lean_inc(x_271);
x_272 = lean_ctor_get(x_262, 4);
lean_inc(x_272);
x_273 = lean_ctor_get(x_262, 5);
lean_inc(x_273);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 lean_ctor_release(x_262, 3);
 lean_ctor_release(x_262, 4);
 lean_ctor_release(x_262, 5);
 x_274 = x_262;
} else {
 lean_dec_ref(x_262);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(0, 6, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_269);
lean_ctor_set(x_275, 1, x_254);
lean_ctor_set(x_275, 2, x_270);
lean_ctor_set(x_275, 3, x_271);
lean_ctor_set(x_275, 4, x_272);
lean_ctor_set(x_275, 5, x_273);
if (lean_is_scalar(x_268)) {
 x_276 = lean_alloc_ctor(0, 5, 0);
} else {
 x_276 = x_268;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_264);
lean_ctor_set(x_276, 2, x_265);
lean_ctor_set(x_276, 3, x_266);
lean_ctor_set(x_276, 4, x_267);
if (lean_is_scalar(x_30)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_30;
 lean_ctor_set_tag(x_277, 1);
}
lean_ctor_set(x_277, 0, x_263);
lean_ctor_set(x_277, 1, x_276);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_260);
lean_dec(x_30);
x_278 = lean_ctor_get(x_261, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_261, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_261, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_261, 3);
lean_inc(x_281);
x_282 = lean_ctor_get(x_261, 4);
lean_inc(x_282);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 lean_ctor_release(x_261, 4);
 x_283 = x_261;
} else {
 lean_dec_ref(x_261);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_278, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_278, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_278, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_278, 4);
lean_inc(x_287);
x_288 = lean_ctor_get(x_278, 5);
lean_inc(x_288);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 lean_ctor_release(x_278, 2);
 lean_ctor_release(x_278, 3);
 lean_ctor_release(x_278, 4);
 lean_ctor_release(x_278, 5);
 x_289 = x_278;
} else {
 lean_dec_ref(x_278);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(0, 6, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_284);
lean_ctor_set(x_290, 1, x_254);
lean_ctor_set(x_290, 2, x_285);
lean_ctor_set(x_290, 3, x_286);
lean_ctor_set(x_290, 4, x_287);
lean_ctor_set(x_290, 5, x_288);
if (lean_is_scalar(x_283)) {
 x_291 = lean_alloc_ctor(0, 5, 0);
} else {
 x_291 = x_283;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_279);
lean_ctor_set(x_291, 2, x_280);
lean_ctor_set(x_291, 3, x_281);
lean_ctor_set(x_291, 4, x_282);
x_292 = l_Lean_Meta_SynthInstance_consume(x_5, x_1, x_291);
return x_292;
}
}
block_328:
{
if (x_294 == 0)
{
lean_object* x_296; 
lean_dec(x_19);
lean_dec(x_15);
x_296 = l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
x_260 = x_296;
x_261 = x_295;
goto block_293;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_297 = lean_ctor_get(x_295, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_295, 1);
lean_inc(x_298);
x_299 = lean_ctor_get(x_295, 2);
lean_inc(x_299);
x_300 = lean_ctor_get(x_295, 3);
lean_inc(x_300);
x_301 = lean_ctor_get(x_295, 4);
lean_inc(x_301);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 lean_ctor_release(x_295, 2);
 lean_ctor_release(x_295, 3);
 lean_ctor_release(x_295, 4);
 x_302 = x_295;
} else {
 lean_dec_ref(x_295);
 x_302 = lean_box(0);
}
lean_inc(x_1);
x_303 = l_Lean_Meta_inferType(x_15, x_1, x_297);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
lean_inc(x_1);
x_306 = l_Lean_Meta_inferType(x_19, x_1, x_305);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
if (lean_is_scalar(x_302)) {
 x_309 = lean_alloc_ctor(0, 5, 0);
} else {
 x_309 = x_302;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_298);
lean_ctor_set(x_309, 2, x_299);
lean_ctor_set(x_309, 3, x_300);
lean_ctor_set(x_309, 4, x_301);
x_310 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_310, 0, x_304);
x_311 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_312 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_313, 0, x_307);
x_314 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
x_315 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_316 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_315, x_314, x_1, x_309);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_317);
x_260 = x_319;
x_261 = x_318;
goto block_293;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_304);
x_320 = lean_ctor_get(x_306, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_306, 1);
lean_inc(x_321);
lean_dec(x_306);
if (lean_is_scalar(x_302)) {
 x_322 = lean_alloc_ctor(0, 5, 0);
} else {
 x_322 = x_302;
}
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_298);
lean_ctor_set(x_322, 2, x_299);
lean_ctor_set(x_322, 3, x_300);
lean_ctor_set(x_322, 4, x_301);
x_323 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_323, 0, x_320);
x_260 = x_323;
x_261 = x_322;
goto block_293;
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_19);
x_324 = lean_ctor_get(x_303, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_303, 1);
lean_inc(x_325);
lean_dec(x_303);
if (lean_is_scalar(x_302)) {
 x_326 = lean_alloc_ctor(0, 5, 0);
} else {
 x_326 = x_302;
}
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_298);
lean_ctor_set(x_326, 2, x_299);
lean_ctor_set(x_326, 3, x_300);
lean_ctor_set(x_326, 4, x_301);
x_327 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_327, 0, x_324);
x_260 = x_327;
x_261 = x_326;
goto block_293;
}
}
}
}
}
}
else
{
uint8_t x_342; 
lean_dec(x_20);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
x_342 = !lean_is_exclusive(x_21);
if (x_342 == 0)
{
return x_21;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_21, 0);
x_344 = lean_ctor_get(x_21, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_21);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_346 = lean_ctor_get(x_5, 0);
x_347 = lean_ctor_get(x_5, 1);
x_348 = lean_ctor_get(x_5, 2);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_5);
x_349 = lean_ctor_get(x_6, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_6, 1);
lean_inc(x_350);
lean_dec(x_6);
lean_inc(x_1);
lean_inc(x_349);
x_351 = l_Lean_Meta_SynthInstance_tryAnswer(x_348, x_349, x_13, x_1, x_12);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_1);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_354 = x_351;
} else {
 lean_dec_ref(x_351);
 x_354 = lean_box(0);
}
x_355 = lean_box(0);
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_353);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_408; lean_object* x_409; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_357 = lean_ctor_get(x_351, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_358 = x_351;
} else {
 lean_dec_ref(x_351);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_352, 0);
lean_inc(x_359);
lean_dec(x_352);
lean_inc(x_359);
lean_inc(x_346);
x_360 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_360, 0, x_346);
lean_ctor_set(x_360, 1, x_347);
lean_ctor_set(x_360, 2, x_359);
lean_ctor_set(x_360, 3, x_350);
x_361 = lean_ctor_get(x_357, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_357, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_357, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_357, 3);
lean_inc(x_364);
x_365 = lean_ctor_get(x_357, 4);
lean_inc(x_365);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 lean_ctor_release(x_357, 4);
 x_366 = x_357;
} else {
 lean_dec_ref(x_357);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_361, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_361, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_361, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_361, 3);
lean_inc(x_370);
x_371 = lean_ctor_get(x_361, 4);
lean_inc(x_371);
x_372 = lean_ctor_get(x_361, 5);
lean_inc(x_372);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 lean_ctor_release(x_361, 2);
 lean_ctor_release(x_361, 3);
 lean_ctor_release(x_361, 4);
 lean_ctor_release(x_361, 5);
 x_373 = x_361;
} else {
 lean_dec_ref(x_361);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_443 = lean_alloc_ctor(0, 6, 0);
} else {
 x_443 = x_373;
}
lean_ctor_set(x_443, 0, x_367);
lean_ctor_set(x_443, 1, x_359);
lean_ctor_set(x_443, 2, x_369);
lean_ctor_set(x_443, 3, x_370);
lean_ctor_set(x_443, 4, x_371);
lean_ctor_set(x_443, 5, x_372);
if (lean_is_scalar(x_366)) {
 x_444 = lean_alloc_ctor(0, 5, 0);
} else {
 x_444 = x_366;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_362);
lean_ctor_set(x_444, 2, x_363);
lean_ctor_set(x_444, 3, x_364);
lean_ctor_set(x_444, 4, x_365);
x_445 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_444);
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get_uint8(x_446, sizeof(void*)*1);
lean_dec(x_446);
if (x_447 == 0)
{
lean_object* x_448; uint8_t x_449; 
x_448 = lean_ctor_get(x_445, 1);
lean_inc(x_448);
lean_dec(x_445);
x_449 = 0;
x_408 = x_449;
x_409 = x_448;
goto block_442;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; 
x_450 = lean_ctor_get(x_445, 1);
lean_inc(x_450);
lean_dec(x_445);
x_451 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_452 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_451, x_1, x_450);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = lean_unbox(x_453);
lean_dec(x_453);
x_408 = x_455;
x_409 = x_454;
goto block_442;
}
block_407:
{
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_360);
lean_dec(x_1);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_374, 0);
lean_inc(x_377);
lean_dec(x_374);
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_375, 2);
lean_inc(x_379);
x_380 = lean_ctor_get(x_375, 3);
lean_inc(x_380);
x_381 = lean_ctor_get(x_375, 4);
lean_inc(x_381);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 lean_ctor_release(x_375, 4);
 x_382 = x_375;
} else {
 lean_dec_ref(x_375);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_376, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_376, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_376, 3);
lean_inc(x_385);
x_386 = lean_ctor_get(x_376, 4);
lean_inc(x_386);
x_387 = lean_ctor_get(x_376, 5);
lean_inc(x_387);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 lean_ctor_release(x_376, 4);
 lean_ctor_release(x_376, 5);
 x_388 = x_376;
} else {
 lean_dec_ref(x_376);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(0, 6, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_383);
lean_ctor_set(x_389, 1, x_368);
lean_ctor_set(x_389, 2, x_384);
lean_ctor_set(x_389, 3, x_385);
lean_ctor_set(x_389, 4, x_386);
lean_ctor_set(x_389, 5, x_387);
if (lean_is_scalar(x_382)) {
 x_390 = lean_alloc_ctor(0, 5, 0);
} else {
 x_390 = x_382;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_378);
lean_ctor_set(x_390, 2, x_379);
lean_ctor_set(x_390, 3, x_380);
lean_ctor_set(x_390, 4, x_381);
if (lean_is_scalar(x_358)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_358;
 lean_ctor_set_tag(x_391, 1);
}
lean_ctor_set(x_391, 0, x_377);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_374);
lean_dec(x_358);
x_392 = lean_ctor_get(x_375, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_375, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_375, 2);
lean_inc(x_394);
x_395 = lean_ctor_get(x_375, 3);
lean_inc(x_395);
x_396 = lean_ctor_get(x_375, 4);
lean_inc(x_396);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 lean_ctor_release(x_375, 4);
 x_397 = x_375;
} else {
 lean_dec_ref(x_375);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_392, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_392, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_392, 3);
lean_inc(x_400);
x_401 = lean_ctor_get(x_392, 4);
lean_inc(x_401);
x_402 = lean_ctor_get(x_392, 5);
lean_inc(x_402);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 lean_ctor_release(x_392, 4);
 lean_ctor_release(x_392, 5);
 x_403 = x_392;
} else {
 lean_dec_ref(x_392);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(0, 6, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_398);
lean_ctor_set(x_404, 1, x_368);
lean_ctor_set(x_404, 2, x_399);
lean_ctor_set(x_404, 3, x_400);
lean_ctor_set(x_404, 4, x_401);
lean_ctor_set(x_404, 5, x_402);
if (lean_is_scalar(x_397)) {
 x_405 = lean_alloc_ctor(0, 5, 0);
} else {
 x_405 = x_397;
}
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_393);
lean_ctor_set(x_405, 2, x_394);
lean_ctor_set(x_405, 3, x_395);
lean_ctor_set(x_405, 4, x_396);
x_406 = l_Lean_Meta_SynthInstance_consume(x_360, x_1, x_405);
return x_406;
}
}
block_442:
{
if (x_408 == 0)
{
lean_object* x_410; 
lean_dec(x_349);
lean_dec(x_346);
x_410 = l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
x_374 = x_410;
x_375 = x_409;
goto block_407;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_411 = lean_ctor_get(x_409, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_409, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_409, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_409, 3);
lean_inc(x_414);
x_415 = lean_ctor_get(x_409, 4);
lean_inc(x_415);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 lean_ctor_release(x_409, 2);
 lean_ctor_release(x_409, 3);
 lean_ctor_release(x_409, 4);
 x_416 = x_409;
} else {
 lean_dec_ref(x_409);
 x_416 = lean_box(0);
}
lean_inc(x_1);
x_417 = l_Lean_Meta_inferType(x_346, x_1, x_411);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
lean_inc(x_1);
x_420 = l_Lean_Meta_inferType(x_349, x_1, x_419);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
if (lean_is_scalar(x_416)) {
 x_423 = lean_alloc_ctor(0, 5, 0);
} else {
 x_423 = x_416;
}
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_412);
lean_ctor_set(x_423, 2, x_413);
lean_ctor_set(x_423, 3, x_414);
lean_ctor_set(x_423, 4, x_415);
x_424 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_424, 0, x_418);
x_425 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_426 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
x_427 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_427, 0, x_421);
x_428 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
x_429 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_430 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_429, x_428, x_1, x_423);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec(x_430);
x_433 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_433, 0, x_431);
x_374 = x_433;
x_375 = x_432;
goto block_407;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_418);
x_434 = lean_ctor_get(x_420, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_420, 1);
lean_inc(x_435);
lean_dec(x_420);
if (lean_is_scalar(x_416)) {
 x_436 = lean_alloc_ctor(0, 5, 0);
} else {
 x_436 = x_416;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_412);
lean_ctor_set(x_436, 2, x_413);
lean_ctor_set(x_436, 3, x_414);
lean_ctor_set(x_436, 4, x_415);
x_437 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_437, 0, x_434);
x_374 = x_437;
x_375 = x_436;
goto block_407;
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_349);
x_438 = lean_ctor_get(x_417, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_417, 1);
lean_inc(x_439);
lean_dec(x_417);
if (lean_is_scalar(x_416)) {
 x_440 = lean_alloc_ctor(0, 5, 0);
} else {
 x_440 = x_416;
}
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_412);
lean_ctor_set(x_440, 2, x_413);
lean_ctor_set(x_440, 3, x_414);
lean_ctor_set(x_440, 4, x_415);
x_441 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_441, 0, x_438);
x_374 = x_441;
x_375 = x_440;
goto block_407;
}
}
}
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_1);
x_456 = lean_ctor_get(x_351, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_351, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_458 = x_351;
} else {
 lean_dec_ref(x_351);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 2, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_456);
lean_ctor_set(x_459, 1, x_457);
return x_459;
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_step(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = l_Array_isEmpty___rarg(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SynthInstance_resume(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = 1;
x_9 = lean_box(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = l_Array_isEmpty___rarg(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Meta_SynthInstance_generate(x_1, x_2);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
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
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_2);
return x_35;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_getResult___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_getResult(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getResult___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_getResult___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_getResult(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("remaining fuel ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("synthInstance is out of fuel");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_synth___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_57; lean_object* x_58; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_68 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_3);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_69, sizeof(void*)*1);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = 0;
x_57 = x_72;
x_58 = x_71;
goto block_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_dec(x_68);
x_74 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_75 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_74, x_2, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_unbox(x_76);
lean_dec(x_76);
x_57 = x_78;
x_58 = x_77;
goto block_67;
}
block_56:
{
lean_object* x_9; 
lean_inc(x_2);
x_9 = l_Lean_Meta_SynthInstance_step(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_7);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_23 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_22, x_2, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
lean_ctor_set(x_23, 0, x_13);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_dec(x_23);
x_31 = l_Lean_Meta_SynthInstance_synth___main___closed__3;
x_32 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_22, x_31, x_2, x_30);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_13);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_dec(x_9);
x_38 = l_Lean_Meta_SynthInstance_getResult___rarg(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_1 = x_7;
x_3 = x_40;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_38, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_38, 0, x_46);
return x_38;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_49 = x_39;
} else {
 lean_dec_ref(x_39);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_7);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_9);
if (x_52 == 0)
{
return x_9;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_9, 0);
x_54 = lean_ctor_get(x_9, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_9);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
block_67:
{
if (x_57 == 0)
{
x_8 = x_58;
goto block_56;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_inc(x_7);
x_59 = l_Nat_repr(x_7);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_Meta_SynthInstance_synth___main___closed__6;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_65 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_64, x_63, x_2, x_58);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_8 = x_66;
goto block_56;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_3);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get_uint8(x_81, sizeof(void*)*1);
lean_dec(x_81);
if (x_82 == 0)
{
uint8_t x_83; 
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_80);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_80, 0);
lean_dec(x_84);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_80, 1);
lean_inc(x_87);
lean_dec(x_80);
x_88 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_89 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_88, x_2, x_87);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
uint8_t x_92; 
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_89, 0);
lean_dec(x_93);
lean_ctor_set(x_89, 0, x_79);
return x_89;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_79);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_dec(x_89);
x_97 = l_Lean_Meta_SynthInstance_synth___main___closed__9;
x_98 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_88, x_97, x_2, x_96);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
lean_ctor_set(x_98, 0, x_79);
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_79);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_synth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_synth___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("main goal ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_main___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_main___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_4, 4);
lean_inc(x_266);
x_267 = lean_ctor_get_uint8(x_266, sizeof(void*)*1);
lean_dec(x_266);
if (x_267 == 0)
{
uint8_t x_268; 
x_268 = 0;
x_5 = x_268;
x_6 = x_4;
goto block_265;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_269 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_270 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_269, x_3, x_4);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = lean_unbox(x_271);
lean_dec(x_271);
x_5 = x_273;
x_6 = x_272;
goto block_265;
}
block_265:
{
if (x_5 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_11 = 0;
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_11);
x_33 = lean_box(0);
x_34 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_35 = l_Lean_Meta_mkFreshExprMVar(x_1, x_33, x_34, x_3, x_6);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_inc(x_38);
x_39 = l_Lean_Meta_SynthInstance_mkTableKey(x_38, x_1);
x_40 = lean_box(0);
x_41 = l_Array_empty___closed__1;
x_42 = l_Lean_Meta_SynthInstance_main___closed__1;
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_43, 4, x_42);
x_44 = lean_box(1);
lean_inc(x_3);
x_45 = l_Lean_Meta_SynthInstance_newSubgoal(x_38, x_39, x_36, x_44, x_3, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 4);
lean_inc(x_50);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_47, 1);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_49, 4);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_10);
lean_ctor_set(x_47, 1, x_49);
return x_47;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_10);
lean_ctor_set(x_49, 4, x_57);
lean_ctor_set(x_47, 1, x_49);
return x_47;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_49, 0);
x_59 = lean_ctor_get(x_49, 1);
x_60 = lean_ctor_get(x_49, 2);
x_61 = lean_ctor_get(x_49, 3);
x_62 = lean_ctor_get(x_49, 5);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_64 = x_50;
} else {
 lean_dec_ref(x_50);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 1, 1);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_10);
x_66 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_59);
lean_ctor_set(x_66, 2, x_60);
lean_ctor_set(x_66, 3, x_61);
lean_ctor_set(x_66, 4, x_65);
lean_ctor_set(x_66, 5, x_62);
lean_ctor_set(x_47, 1, x_66);
return x_47;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_ctor_get(x_49, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_49, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_49, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_49, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_49, 5);
lean_inc(x_72);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 lean_ctor_release(x_49, 3);
 lean_ctor_release(x_49, 4);
 lean_ctor_release(x_49, 5);
 x_73 = x_49;
} else {
 lean_dec_ref(x_49);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_50, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_75 = x_50;
} else {
 lean_dec_ref(x_50);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 1, 1);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_10);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(0, 6, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_69);
lean_ctor_set(x_77, 2, x_70);
lean_ctor_set(x_77, 3, x_71);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set(x_77, 5, x_72);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_67);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_47, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_47, 1);
lean_inc(x_80);
lean_dec(x_47);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_12 = x_79;
x_13 = x_81;
goto block_32;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_3);
lean_dec(x_2);
x_82 = lean_ctor_get(x_45, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_45, 1);
lean_inc(x_83);
lean_dec(x_45);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_12 = x_82;
x_13 = x_84;
goto block_32;
}
block_32:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 4);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_10);
lean_ctor_set(x_13, 4, x_19);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_13, 4);
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
x_24 = lean_ctor_get(x_13, 2);
x_25 = lean_ctor_get(x_13, 3);
x_26 = lean_ctor_get(x_13, 5);
lean_inc(x_26);
lean_inc(x_21);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_28 = x_21;
} else {
 lean_dec_ref(x_21);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 1, 1);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_10);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_26);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_85 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_86 = lean_ctor_get(x_8, 0);
lean_inc(x_86);
lean_dec(x_8);
x_87 = 0;
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
lean_ctor_set(x_6, 4, x_88);
x_104 = lean_box(0);
x_105 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_106 = l_Lean_Meta_mkFreshExprMVar(x_1, x_104, x_105, x_3, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_inc(x_109);
x_110 = l_Lean_Meta_SynthInstance_mkTableKey(x_109, x_1);
x_111 = lean_box(0);
x_112 = l_Array_empty___closed__1;
x_113 = l_Lean_Meta_SynthInstance_main___closed__1;
x_114 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_111);
lean_ctor_set(x_114, 2, x_112);
lean_ctor_set(x_114, 3, x_112);
lean_ctor_set(x_114, 4, x_113);
x_115 = lean_box(1);
lean_inc(x_3);
x_116 = l_Lean_Meta_SynthInstance_newSubgoal(x_109, x_110, x_107, x_115, x_3, x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_ctor_get(x_120, 4);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_123 = x_118;
} else {
 lean_dec_ref(x_118);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_120, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_120, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_120, 5);
lean_inc(x_128);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 lean_ctor_release(x_120, 5);
 x_129 = x_120;
} else {
 lean_dec_ref(x_120);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_121, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_131 = x_121;
} else {
 lean_dec_ref(x_121);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 1, 1);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_85);
if (lean_is_scalar(x_129)) {
 x_133 = lean_alloc_ctor(0, 6, 0);
} else {
 x_133 = x_129;
}
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_127);
lean_ctor_set(x_133, 4, x_132);
lean_ctor_set(x_133, 5, x_128);
if (lean_is_scalar(x_123)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_123;
}
lean_ctor_set(x_134, 0, x_122);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_118, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_118, 1);
lean_inc(x_136);
lean_dec(x_118);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec(x_136);
x_89 = x_135;
x_90 = x_137;
goto block_103;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_3);
lean_dec(x_2);
x_138 = lean_ctor_get(x_116, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_116, 1);
lean_inc(x_139);
lean_dec(x_116);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec(x_139);
x_89 = x_138;
x_90 = x_140;
goto block_103;
}
block_103:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_91 = lean_ctor_get(x_90, 4);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 5);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 lean_ctor_release(x_90, 3);
 lean_ctor_release(x_90, 4);
 lean_ctor_release(x_90, 5);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_91, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_99 = x_91;
} else {
 lean_dec_ref(x_91);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 1, 1);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_85);
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(0, 6, 0);
} else {
 x_101 = x_97;
}
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_94);
lean_ctor_set(x_101, 3, x_95);
lean_ctor_set(x_101, 4, x_100);
lean_ctor_set(x_101, 5, x_96);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_89);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_141 = lean_ctor_get(x_6, 4);
x_142 = lean_ctor_get(x_6, 0);
x_143 = lean_ctor_get(x_6, 1);
x_144 = lean_ctor_get(x_6, 2);
x_145 = lean_ctor_get(x_6, 3);
x_146 = lean_ctor_get(x_6, 5);
lean_inc(x_146);
lean_inc(x_141);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_6);
x_147 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
x_148 = lean_ctor_get(x_141, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
 x_149 = lean_box(0);
}
x_150 = 0;
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_150);
x_152 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_152, 0, x_142);
lean_ctor_set(x_152, 1, x_143);
lean_ctor_set(x_152, 2, x_144);
lean_ctor_set(x_152, 3, x_145);
lean_ctor_set(x_152, 4, x_151);
lean_ctor_set(x_152, 5, x_146);
x_168 = lean_box(0);
x_169 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_170 = l_Lean_Meta_mkFreshExprMVar(x_1, x_168, x_169, x_3, x_152);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_inc(x_173);
x_174 = l_Lean_Meta_SynthInstance_mkTableKey(x_173, x_1);
x_175 = lean_box(0);
x_176 = l_Array_empty___closed__1;
x_177 = l_Lean_Meta_SynthInstance_main___closed__1;
x_178 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set(x_178, 2, x_176);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set(x_178, 4, x_177);
x_179 = lean_box(1);
lean_inc(x_3);
x_180 = l_Lean_Meta_SynthInstance_newSubgoal(x_173, x_174, x_171, x_179, x_3, x_178);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_182 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_ctor_get(x_184, 4);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_187 = x_182;
} else {
 lean_dec_ref(x_182);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_184, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_184, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_184, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_184, 5);
lean_inc(x_192);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 lean_ctor_release(x_184, 5);
 x_193 = x_184;
} else {
 lean_dec_ref(x_184);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_185, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_195 = x_185;
} else {
 lean_dec_ref(x_185);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(0, 1, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_193)) {
 x_197 = lean_alloc_ctor(0, 6, 0);
} else {
 x_197 = x_193;
}
lean_ctor_set(x_197, 0, x_188);
lean_ctor_set(x_197, 1, x_189);
lean_ctor_set(x_197, 2, x_190);
lean_ctor_set(x_197, 3, x_191);
lean_ctor_set(x_197, 4, x_196);
lean_ctor_set(x_197, 5, x_192);
if (lean_is_scalar(x_187)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_187;
}
lean_ctor_set(x_198, 0, x_186);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_182, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_182, 1);
lean_inc(x_200);
lean_dec(x_182);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec(x_200);
x_153 = x_199;
x_154 = x_201;
goto block_167;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_3);
lean_dec(x_2);
x_202 = lean_ctor_get(x_180, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_180, 1);
lean_inc(x_203);
lean_dec(x_180);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec(x_203);
x_153 = x_202;
x_154 = x_204;
goto block_167;
}
block_167:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_155 = lean_ctor_get(x_154, 4);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_154, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_154, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_154, 5);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 lean_ctor_release(x_154, 3);
 lean_ctor_release(x_154, 4);
 lean_ctor_release(x_154, 5);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_155, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_163 = x_155;
} else {
 lean_dec_ref(x_155);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 1, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_161)) {
 x_165 = lean_alloc_ctor(0, 6, 0);
} else {
 x_165 = x_161;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_157);
lean_ctor_set(x_165, 2, x_158);
lean_ctor_set(x_165, 3, x_159);
lean_ctor_set(x_165, 4, x_164);
lean_ctor_set(x_165, 5, x_160);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_153);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_252; uint8_t x_253; 
x_205 = l___private_Lean_Util_Trace_3__getResetTraces___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__6___rarg(x_6);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_252 = lean_ctor_get(x_207, 4);
lean_inc(x_252);
x_253 = lean_ctor_get_uint8(x_252, sizeof(void*)*1);
lean_dec(x_252);
if (x_253 == 0)
{
x_208 = x_207;
goto block_251;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_254 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_255 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_254, x_3, x_207);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_unbox(x_256);
lean_dec(x_256);
if (x_257 == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_255, 1);
lean_inc(x_258);
lean_dec(x_255);
x_208 = x_258;
goto block_251;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
lean_dec(x_255);
lean_inc(x_1);
x_260 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_260, 0, x_1);
x_261 = l_Lean_Meta_SynthInstance_main___closed__4;
x_262 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
x_263 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_254, x_262, x_3, x_259);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_208 = x_264;
goto block_251;
}
}
block_251:
{
lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_209 = lean_box(0);
x_210 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_211 = l_Lean_Meta_mkFreshExprMVar(x_1, x_209, x_210, x_3, x_208);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_inc(x_214);
x_215 = l_Lean_Meta_SynthInstance_mkTableKey(x_214, x_1);
x_216 = lean_box(0);
x_217 = l_Array_empty___closed__1;
x_218 = l_Lean_Meta_SynthInstance_main___closed__1;
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_213);
lean_ctor_set(x_219, 1, x_216);
lean_ctor_set(x_219, 2, x_217);
lean_ctor_set(x_219, 3, x_217);
lean_ctor_set(x_219, 4, x_218);
x_220 = lean_box(1);
lean_inc(x_3);
x_221 = l_Lean_Meta_SynthInstance_newSubgoal(x_214, x_215, x_212, x_220, x_3, x_219);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
lean_inc(x_3);
x_223 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec(x_225);
x_227 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_228 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_206, x_227, x_3, x_226);
lean_dec(x_3);
x_229 = !lean_is_exclusive(x_228);
if (x_229 == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_228, 0);
lean_dec(x_230);
lean_ctor_set(x_228, 0, x_224);
return x_228;
}
else
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec(x_228);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_224);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_233 = lean_ctor_get(x_223, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_223, 1);
lean_inc(x_234);
lean_dec(x_223);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec(x_234);
x_236 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_237 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_206, x_236, x_3, x_235);
lean_dec(x_3);
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_237, 0);
lean_dec(x_239);
lean_ctor_set_tag(x_237, 1);
lean_ctor_set(x_237, 0, x_233);
return x_237;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_233);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
lean_dec(x_2);
x_242 = lean_ctor_get(x_221, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_221, 1);
lean_inc(x_243);
lean_dec(x_221);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec(x_243);
x_245 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_246 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_206, x_245, x_3, x_244);
lean_dec(x_3);
x_247 = !lean_is_exclusive(x_246);
if (x_247 == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_246, 0);
lean_dec(x_248);
lean_ctor_set_tag(x_246, 1);
lean_ctor_set(x_246, 0, x_242);
return x_246;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_242);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_2__preprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_whnf(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_mkForall(x_1, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_2__preprocess___lambda__1), 4, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_2__preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1;
x_5 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Meta_instantiateLevelMVars(x_7, x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Level_hasMVar(x_10);
if (x_12 == 0)
{
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_10);
x_1 = x_2;
x_2 = x_8;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
x_14 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_15);
x_1 = x_2;
x_2 = x_8;
x_4 = x_16;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = l_Lean_Meta_instantiateLevelMVars(x_18, x_3, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Level_hasMVar(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_1);
x_1 = x_24;
x_2 = x_19;
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_21);
x_26 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_1);
x_1 = x_29;
x_2 = x_19;
x_4 = x_28;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocessLevels(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(0);
x_5 = l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1(x_4, x_1, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_List_reverse___rarg(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_List_reverse___rarg(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocessLevels___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_SynthInstance_3__preprocessLevels(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type class resolution failed, insufficient number of arguments");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__3;
x_2 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = l_Lean_Meta_whnf(x_1, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_array_fget(x_3, x_2);
lean_inc(x_12);
x_15 = lean_is_out_param(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_inc(x_14);
x_16 = lean_array_fset(x_3, x_2, x_14);
x_17 = lean_expr_instantiate1(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_1 = x_17;
x_2 = x_19;
x_3 = x_16;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = 0;
lean_inc(x_4);
x_23 = l_Lean_Meta_mkFreshExprMVar(x_12, x_21, x_22, x_4, x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
x_26 = lean_array_fset(x_3, x_2, x_24);
x_27 = lean_expr_instantiate1(x_13, x_24);
lean_dec(x_24);
lean_dec(x_13);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_2, x_28);
lean_dec(x_2);
x_1 = x_27;
x_2 = x_29;
x_3 = x_26;
x_5 = x_25;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_9, 0);
lean_dec(x_32);
x_33 = l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__4;
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_33);
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_dec(x_9);
x_35 = l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__4;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessOutParam___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_getAppFn___main(x_3);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_inc(x_7);
x_10 = lean_has_out_params(x_9, x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_3__getAppArgsAux___main(x_3, x_15, x_17);
x_19 = l___private_Lean_Meta_SynthInstance_3__preprocessLevels(x_8, x_4, x_5);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkConst(x_7, x_20);
lean_inc(x_4);
lean_inc(x_22);
x_23 = l_Lean_Meta_inferType(x_22, x_4, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_4);
x_26 = l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main(x_24, x_12, x_18, x_4, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_27, x_27, x_12, x_22);
lean_dec(x_27);
x_30 = l_Lean_Meta_mkForall(x_2, x_29, x_4, x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_2);
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
else
{
lean_object* x_39; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_5);
return x_39;
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessOutParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_5__preprocessOutParam___lambda__1), 5, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Meta_forallTelescope___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_maxStepsOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maxSteps");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_maxStepsOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__73;
x_2 = l_Lean_Meta_maxStepsOption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_maxStepsOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10000u);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_maxStepsOption___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum steps for the type class instance synthesis procedure");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_maxStepsOption___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_maxStepsOption___closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_Meta_maxStepsOption___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_maxStepsOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_maxStepsOption___closed__2;
x_3 = l_Lean_Meta_maxStepsOption___closed__5;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_6__getMaxSteps(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_maxStepsOption___closed__2;
x_3 = lean_unsigned_to_nat(10000u);
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_6__getMaxSteps___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_SynthInstance_6__getMaxSteps(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_synthInstance_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Expr_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_Std_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
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
x_16 = lean_box(2);
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
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_Std_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_35, x_36, x_37, x_4, x_5);
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
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_Std_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
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
x_58 = lean_box(2);
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
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_Std_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_71, x_73, x_74, x_4, x_5);
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
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_synthInstance_x3f___spec__3(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = 1;
x_9 = l_Std_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Expr_hash(x_2);
x_15 = 1;
x_16 = l_Std_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
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
x_17 = x_2 >> x_5;
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
x_23 = l_Std_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6(x_3, x_4, x_2);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("FOUND result ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ==> ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
x_15 = l___private_Lean_Meta_SynthInstance_6__getMaxSteps(x_10);
x_16 = 1;
x_17 = 2;
x_18 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 2, x_11);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 3, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 4, x_13);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 5, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 6, x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_ctor_set(x_2, 0, x_18);
x_19 = l_Lean_Meta_instantiateMVars(x_1, x_2, x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1;
lean_inc(x_2);
x_24 = l_Lean_Meta_forallTelescopeReducing___rarg(x_20, x_23, x_2, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_63 = lean_ctor_get(x_26, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_26, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_26, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_26, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_26, 4);
lean_inc(x_67);
x_68 = lean_ctor_get(x_26, 5);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc(x_69);
x_70 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(x_69, x_25);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_26);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_166; lean_object* x_167; lean_object* x_179; lean_object* x_180; 
x_72 = lean_ctor_get(x_26, 5);
lean_dec(x_72);
x_73 = lean_ctor_get(x_26, 4);
lean_dec(x_73);
x_74 = lean_ctor_get(x_26, 3);
lean_dec(x_74);
x_75 = lean_ctor_get(x_26, 2);
lean_dec(x_75);
x_76 = lean_ctor_get(x_26, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_26, 0);
lean_dec(x_77);
lean_inc(x_64);
x_179 = l_Lean_MetavarContext_incDepth(x_64);
lean_ctor_set(x_26, 1, x_179);
lean_inc(x_2);
lean_inc(x_25);
x_180 = l___private_Lean_Meta_SynthInstance_5__preprocessOutParam(x_25, x_2, x_26);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_218; uint8_t x_219; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_218 = lean_ctor_get(x_182, 4);
lean_inc(x_218);
x_219 = lean_ctor_get_uint8(x_218, sizeof(void*)*1);
lean_dec(x_218);
if (x_219 == 0)
{
x_183 = x_182;
goto block_217;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_220 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_221 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_220, x_2, x_182);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_183 = x_224;
goto block_217;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
lean_dec(x_221);
lean_inc(x_25);
x_226 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_226, 0, x_25);
x_227 = l_Lean_Meta_synthInstance_x3f___closed__9;
x_228 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
lean_inc(x_181);
x_229 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_229, 0, x_181);
x_230 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_220, x_230, x_2, x_225);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_183 = x_232;
goto block_217;
}
}
block_217:
{
lean_object* x_184; 
lean_inc(x_2);
x_184 = l_Lean_Meta_SynthInstance_main(x_181, x_15, x_2, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
lean_dec(x_22);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_78 = x_185;
x_79 = x_186;
goto block_165;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_202; uint8_t x_203; 
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
lean_dec(x_184);
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_189 = x_185;
} else {
 lean_dec_ref(x_185);
 x_189 = lean_box(0);
}
x_202 = lean_ctor_get(x_187, 4);
lean_inc(x_202);
x_203 = lean_ctor_get_uint8(x_202, sizeof(void*)*1);
lean_dec(x_202);
if (x_203 == 0)
{
x_190 = x_187;
goto block_201;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_204 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_205 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_204, x_2, x_187);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_unbox(x_206);
lean_dec(x_206);
if (x_207 == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_dec(x_205);
x_190 = x_208;
goto block_201;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
lean_dec(x_205);
lean_inc(x_188);
x_210 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_210, 0, x_188);
x_211 = l_Lean_Meta_synthInstance_x3f___closed__6;
x_212 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_210);
x_213 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_204, x_212, x_2, x_209);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_190 = x_214;
goto block_201;
}
}
block_201:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_191 = l_Lean_Meta_instantiateMVars(x_188, x_2, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lean_Meta_hasAssignableMVar(x_192, x_2, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_unbox(x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_dec(x_194);
if (lean_is_scalar(x_189)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_189;
}
lean_ctor_set(x_198, 0, x_192);
x_78 = x_198;
x_79 = x_197;
goto block_165;
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_192);
lean_dec(x_189);
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
lean_dec(x_194);
x_200 = lean_box(0);
x_78 = x_200;
x_79 = x_199;
goto block_165;
}
}
}
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_215 = lean_ctor_get(x_184, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_184, 1);
lean_inc(x_216);
lean_dec(x_184);
x_166 = x_215;
x_167 = x_216;
goto block_178;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_233 = lean_ctor_get(x_180, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_180, 1);
lean_inc(x_234);
lean_dec(x_180);
x_166 = x_233;
x_167 = x_234;
goto block_178;
}
block_165:
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 4);
x_82 = lean_ctor_get(x_79, 1);
lean_dec(x_82);
lean_inc(x_81);
lean_ctor_set(x_79, 1, x_64);
if (lean_obj_tag(x_78) == 0)
{
lean_dec(x_81);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = x_78;
x_29 = x_79;
goto block_62;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_109; 
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_84 = x_78;
} else {
 lean_dec_ref(x_78);
 x_84 = lean_box(0);
}
x_109 = lean_ctor_get_uint8(x_81, sizeof(void*)*1);
lean_dec(x_81);
if (x_109 == 0)
{
x_85 = x_79;
goto block_108;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_111 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_110, x_2, x_79);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_85 = x_114;
goto block_108;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
lean_inc(x_83);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_83);
x_117 = l_Lean_Meta_synthInstance_x3f___closed__3;
x_118 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_110, x_118, x_2, x_115);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_85 = x_120;
goto block_108;
}
}
block_108:
{
lean_object* x_86; 
lean_inc(x_2);
lean_inc(x_83);
x_86 = l_Lean_Meta_inferType(x_83, x_2, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_5);
lean_ctor_set(x_89, 1, x_6);
lean_ctor_set(x_89, 2, x_7);
lean_ctor_set(x_89, 3, x_8);
lean_ctor_set(x_89, 4, x_9);
lean_inc(x_25);
x_90 = l_Lean_Meta_isExprDefEq(x_25, x_87, x_89, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_2);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_box(0);
x_28 = x_94;
x_29 = x_93;
goto block_62;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_dec(x_90);
x_96 = l_Lean_Meta_instantiateMVars(x_83, x_2, x_95);
lean_dec(x_2);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
if (lean_is_scalar(x_84)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_84;
}
lean_ctor_set(x_99, 0, x_97);
x_28 = x_99;
x_29 = x_98;
goto block_62;
}
}
else
{
uint8_t x_100; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_90);
if (x_100 == 0)
{
return x_90;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_90, 0);
x_102 = lean_ctor_get(x_90, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_90);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_104 = !lean_is_exclusive(x_86);
if (x_104 == 0)
{
return x_86;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_86, 0);
x_106 = lean_ctor_get(x_86, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_86);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_79, 0);
x_122 = lean_ctor_get(x_79, 2);
x_123 = lean_ctor_get(x_79, 3);
x_124 = lean_ctor_get(x_79, 4);
x_125 = lean_ctor_get(x_79, 5);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_79);
lean_inc(x_124);
x_126 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_126, 0, x_121);
lean_ctor_set(x_126, 1, x_64);
lean_ctor_set(x_126, 2, x_122);
lean_ctor_set(x_126, 3, x_123);
lean_ctor_set(x_126, 4, x_124);
lean_ctor_set(x_126, 5, x_125);
if (lean_obj_tag(x_78) == 0)
{
lean_dec(x_124);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = x_78;
x_29 = x_126;
goto block_62;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_153; 
x_127 = lean_ctor_get(x_78, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_128 = x_78;
} else {
 lean_dec_ref(x_78);
 x_128 = lean_box(0);
}
x_153 = lean_ctor_get_uint8(x_124, sizeof(void*)*1);
lean_dec(x_124);
if (x_153 == 0)
{
x_129 = x_126;
goto block_152;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_154 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_155 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_154, x_2, x_126);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec(x_155);
x_129 = x_158;
goto block_152;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_dec(x_155);
lean_inc(x_127);
x_160 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_160, 0, x_127);
x_161 = l_Lean_Meta_synthInstance_x3f___closed__3;
x_162 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_154, x_162, x_2, x_159);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_129 = x_164;
goto block_152;
}
}
block_152:
{
lean_object* x_130; 
lean_inc(x_2);
lean_inc(x_127);
x_130 = l_Lean_Meta_inferType(x_127, x_2, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_133, 0, x_5);
lean_ctor_set(x_133, 1, x_6);
lean_ctor_set(x_133, 2, x_7);
lean_ctor_set(x_133, 3, x_8);
lean_ctor_set(x_133, 4, x_9);
lean_inc(x_25);
x_134 = l_Lean_Meta_isExprDefEq(x_25, x_131, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_2);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_box(0);
x_28 = x_138;
x_29 = x_137;
goto block_62;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
lean_dec(x_134);
x_140 = l_Lean_Meta_instantiateMVars(x_127, x_2, x_139);
lean_dec(x_2);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
if (lean_is_scalar(x_128)) {
 x_143 = lean_alloc_ctor(1, 1, 0);
} else {
 x_143 = x_128;
}
lean_ctor_set(x_143, 0, x_141);
x_28 = x_143;
x_29 = x_142;
goto block_62;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
x_144 = lean_ctor_get(x_134, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_134, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_146 = x_134;
} else {
 lean_dec_ref(x_134);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_148 = lean_ctor_get(x_130, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_130, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_150 = x_130;
} else {
 lean_dec_ref(x_130);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
}
}
block_178:
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_167, 1);
lean_dec(x_169);
lean_ctor_set(x_167, 1, x_64);
if (lean_is_scalar(x_22)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_22;
 lean_ctor_set_tag(x_170, 1);
}
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_167);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = lean_ctor_get(x_167, 0);
x_172 = lean_ctor_get(x_167, 2);
x_173 = lean_ctor_get(x_167, 3);
x_174 = lean_ctor_get(x_167, 4);
x_175 = lean_ctor_get(x_167, 5);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_167);
x_176 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_176, 0, x_171);
lean_ctor_set(x_176, 1, x_64);
lean_ctor_set(x_176, 2, x_172);
lean_ctor_set(x_176, 3, x_173);
lean_ctor_set(x_176, 4, x_174);
lean_ctor_set(x_176, 5, x_175);
if (lean_is_scalar(x_22)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_22;
 lean_ctor_set_tag(x_177, 1);
}
lean_ctor_set(x_177, 0, x_166);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_283; lean_object* x_284; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_26);
lean_inc(x_64);
x_294 = l_Lean_MetavarContext_incDepth(x_64);
x_295 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_295, 0, x_63);
lean_ctor_set(x_295, 1, x_294);
lean_ctor_set(x_295, 2, x_65);
lean_ctor_set(x_295, 3, x_66);
lean_ctor_set(x_295, 4, x_67);
lean_ctor_set(x_295, 5, x_68);
lean_inc(x_2);
lean_inc(x_25);
x_296 = l___private_Lean_Meta_SynthInstance_5__preprocessOutParam(x_25, x_2, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_334; uint8_t x_335; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_334 = lean_ctor_get(x_298, 4);
lean_inc(x_334);
x_335 = lean_ctor_get_uint8(x_334, sizeof(void*)*1);
lean_dec(x_334);
if (x_335 == 0)
{
x_299 = x_298;
goto block_333;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_336 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_337 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_336, x_2, x_298);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_unbox(x_338);
lean_dec(x_338);
if (x_339 == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_337, 1);
lean_inc(x_340);
lean_dec(x_337);
x_299 = x_340;
goto block_333;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_341 = lean_ctor_get(x_337, 1);
lean_inc(x_341);
lean_dec(x_337);
lean_inc(x_25);
x_342 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_342, 0, x_25);
x_343 = l_Lean_Meta_synthInstance_x3f___closed__9;
x_344 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
lean_inc(x_297);
x_345 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_345, 0, x_297);
x_346 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
x_347 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_336, x_346, x_2, x_341);
x_348 = lean_ctor_get(x_347, 1);
lean_inc(x_348);
lean_dec(x_347);
x_299 = x_348;
goto block_333;
}
}
block_333:
{
lean_object* x_300; 
lean_inc(x_2);
x_300 = l_Lean_Meta_SynthInstance_main(x_297, x_15, x_2, x_299);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; 
lean_dec(x_22);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; 
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_235 = x_301;
x_236 = x_302;
goto block_282;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_318; uint8_t x_319; 
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
lean_dec(x_300);
x_304 = lean_ctor_get(x_301, 0);
lean_inc(x_304);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 x_305 = x_301;
} else {
 lean_dec_ref(x_301);
 x_305 = lean_box(0);
}
x_318 = lean_ctor_get(x_303, 4);
lean_inc(x_318);
x_319 = lean_ctor_get_uint8(x_318, sizeof(void*)*1);
lean_dec(x_318);
if (x_319 == 0)
{
x_306 = x_303;
goto block_317;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_320 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_321 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_320, x_2, x_303);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_unbox(x_322);
lean_dec(x_322);
if (x_323 == 0)
{
lean_object* x_324; 
x_324 = lean_ctor_get(x_321, 1);
lean_inc(x_324);
lean_dec(x_321);
x_306 = x_324;
goto block_317;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_325 = lean_ctor_get(x_321, 1);
lean_inc(x_325);
lean_dec(x_321);
lean_inc(x_304);
x_326 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_326, 0, x_304);
x_327 = l_Lean_Meta_synthInstance_x3f___closed__6;
x_328 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_326);
x_329 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_320, x_328, x_2, x_325);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
x_306 = x_330;
goto block_317;
}
}
block_317:
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_307 = l_Lean_Meta_instantiateMVars(x_304, x_2, x_306);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = l_Lean_Meta_hasAssignableMVar(x_308, x_2, x_309);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_unbox(x_311);
lean_dec(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_310, 1);
lean_inc(x_313);
lean_dec(x_310);
if (lean_is_scalar(x_305)) {
 x_314 = lean_alloc_ctor(1, 1, 0);
} else {
 x_314 = x_305;
}
lean_ctor_set(x_314, 0, x_308);
x_235 = x_314;
x_236 = x_313;
goto block_282;
}
else
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_308);
lean_dec(x_305);
x_315 = lean_ctor_get(x_310, 1);
lean_inc(x_315);
lean_dec(x_310);
x_316 = lean_box(0);
x_235 = x_316;
x_236 = x_315;
goto block_282;
}
}
}
}
else
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_331 = lean_ctor_get(x_300, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_300, 1);
lean_inc(x_332);
lean_dec(x_300);
x_283 = x_331;
x_284 = x_332;
goto block_293;
}
}
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_349 = lean_ctor_get(x_296, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_296, 1);
lean_inc(x_350);
lean_dec(x_296);
x_283 = x_349;
x_284 = x_350;
goto block_293;
}
block_282:
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_236, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_236, 4);
lean_inc(x_240);
x_241 = lean_ctor_get(x_236, 5);
lean_inc(x_241);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 lean_ctor_release(x_236, 3);
 lean_ctor_release(x_236, 4);
 lean_ctor_release(x_236, 5);
 x_242 = x_236;
} else {
 lean_dec_ref(x_236);
 x_242 = lean_box(0);
}
lean_inc(x_240);
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(0, 6, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_237);
lean_ctor_set(x_243, 1, x_64);
lean_ctor_set(x_243, 2, x_238);
lean_ctor_set(x_243, 3, x_239);
lean_ctor_set(x_243, 4, x_240);
lean_ctor_set(x_243, 5, x_241);
if (lean_obj_tag(x_235) == 0)
{
lean_dec(x_240);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = x_235;
x_29 = x_243;
goto block_62;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_270; 
x_244 = lean_ctor_get(x_235, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_245 = x_235;
} else {
 lean_dec_ref(x_235);
 x_245 = lean_box(0);
}
x_270 = lean_ctor_get_uint8(x_240, sizeof(void*)*1);
lean_dec(x_240);
if (x_270 == 0)
{
x_246 = x_243;
goto block_269;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_271 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_272 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_271, x_2, x_243);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_unbox(x_273);
lean_dec(x_273);
if (x_274 == 0)
{
lean_object* x_275; 
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
lean_dec(x_272);
x_246 = x_275;
goto block_269;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_276 = lean_ctor_get(x_272, 1);
lean_inc(x_276);
lean_dec(x_272);
lean_inc(x_244);
x_277 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_277, 0, x_244);
x_278 = l_Lean_Meta_synthInstance_x3f___closed__3;
x_279 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
x_280 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_271, x_279, x_2, x_276);
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
lean_dec(x_280);
x_246 = x_281;
goto block_269;
}
}
block_269:
{
lean_object* x_247; 
lean_inc(x_2);
lean_inc(x_244);
x_247 = l_Lean_Meta_inferType(x_244, x_2, x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_250, 0, x_5);
lean_ctor_set(x_250, 1, x_6);
lean_ctor_set(x_250, 2, x_7);
lean_ctor_set(x_250, 3, x_8);
lean_ctor_set(x_250, 4, x_9);
lean_inc(x_25);
x_251 = l_Lean_Meta_isExprDefEq(x_25, x_248, x_250, x_249);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; uint8_t x_253; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_unbox(x_252);
lean_dec(x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_2);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_box(0);
x_28 = x_255;
x_29 = x_254;
goto block_62;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_256 = lean_ctor_get(x_251, 1);
lean_inc(x_256);
lean_dec(x_251);
x_257 = l_Lean_Meta_instantiateMVars(x_244, x_2, x_256);
lean_dec(x_2);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
if (lean_is_scalar(x_245)) {
 x_260 = lean_alloc_ctor(1, 1, 0);
} else {
 x_260 = x_245;
}
lean_ctor_set(x_260, 0, x_258);
x_28 = x_260;
x_29 = x_259;
goto block_62;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
x_261 = lean_ctor_get(x_251, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_251, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_263 = x_251;
} else {
 lean_dec_ref(x_251);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_265 = lean_ctor_get(x_247, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_247, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_267 = x_247;
} else {
 lean_dec_ref(x_247);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
}
}
block_293:
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 2);
lean_inc(x_286);
x_287 = lean_ctor_get(x_284, 3);
lean_inc(x_287);
x_288 = lean_ctor_get(x_284, 4);
lean_inc(x_288);
x_289 = lean_ctor_get(x_284, 5);
lean_inc(x_289);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 lean_ctor_release(x_284, 2);
 lean_ctor_release(x_284, 3);
 lean_ctor_release(x_284, 4);
 lean_ctor_release(x_284, 5);
 x_290 = x_284;
} else {
 lean_dec_ref(x_284);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(0, 6, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_285);
lean_ctor_set(x_291, 1, x_64);
lean_ctor_set(x_291, 2, x_286);
lean_ctor_set(x_291, 3, x_287);
lean_ctor_set(x_291, 4, x_288);
lean_ctor_set(x_291, 5, x_289);
if (lean_is_scalar(x_22)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_22;
 lean_ctor_set_tag(x_292, 1);
}
lean_ctor_set(x_292, 0, x_283);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
else
{
lean_object* x_351; lean_object* x_352; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_351 = lean_ctor_get(x_70, 0);
lean_inc(x_351);
lean_dec(x_70);
if (lean_is_scalar(x_22)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_22;
}
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_26);
return x_352;
}
block_62:
{
uint8_t x_30; 
x_30 = l_Lean_Expr_hasMVar(x_25);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 2);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_28);
x_35 = l_Std_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(x_34, x_25, x_28);
lean_ctor_set(x_32, 2, x_35);
if (lean_is_scalar(x_27)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_27;
}
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
x_39 = lean_ctor_get(x_32, 2);
x_40 = lean_ctor_get(x_32, 3);
x_41 = lean_ctor_get(x_32, 4);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
lean_inc(x_28);
x_42 = l_Std_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(x_39, x_25, x_28);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_41);
lean_ctor_set(x_29, 2, x_43);
if (lean_is_scalar(x_27)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_27;
}
lean_ctor_set(x_44, 0, x_28);
lean_ctor_set(x_44, 1, x_29);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_45 = lean_ctor_get(x_29, 2);
x_46 = lean_ctor_get(x_29, 0);
x_47 = lean_ctor_get(x_29, 1);
x_48 = lean_ctor_get(x_29, 3);
x_49 = lean_ctor_get(x_29, 4);
x_50 = lean_ctor_get(x_29, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_45);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_29);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_45, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_45, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_45, 4);
lean_inc(x_55);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 lean_ctor_release(x_45, 4);
 x_56 = x_45;
} else {
 lean_dec_ref(x_45);
 x_56 = lean_box(0);
}
lean_inc(x_28);
x_57 = l_Std_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(x_53, x_25, x_28);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_52);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_58, 3, x_54);
lean_ctor_set(x_58, 4, x_55);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_46);
lean_ctor_set(x_59, 1, x_47);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set(x_59, 3, x_48);
lean_ctor_set(x_59, 4, x_49);
lean_ctor_set(x_59, 5, x_50);
if (lean_is_scalar(x_27)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_27;
}
lean_ctor_set(x_60, 0, x_28);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_25);
if (lean_is_scalar(x_27)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_27;
}
lean_ctor_set(x_61, 0, x_28);
lean_ctor_set(x_61, 1, x_29);
return x_61;
}
}
}
else
{
uint8_t x_353; 
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_353 = !lean_is_exclusive(x_24);
if (x_353 == 0)
{
return x_24;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_24, 0);
x_355 = lean_ctor_get(x_24, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_24);
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; uint8_t x_364; uint8_t x_365; uint8_t x_366; lean_object* x_367; uint8_t x_368; uint8_t x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_357 = lean_ctor_get(x_2, 0);
x_358 = lean_ctor_get(x_2, 1);
x_359 = lean_ctor_get(x_2, 2);
x_360 = lean_ctor_get(x_2, 3);
x_361 = lean_ctor_get(x_2, 4);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_2);
x_362 = lean_ctor_get(x_357, 0);
lean_inc(x_362);
x_363 = lean_ctor_get_uint8(x_357, sizeof(void*)*1 + 2);
x_364 = lean_ctor_get_uint8(x_357, sizeof(void*)*1 + 3);
x_365 = lean_ctor_get_uint8(x_357, sizeof(void*)*1 + 4);
x_366 = lean_ctor_get_uint8(x_357, sizeof(void*)*1 + 5);
x_367 = l___private_Lean_Meta_SynthInstance_6__getMaxSteps(x_362);
x_368 = 1;
x_369 = 2;
x_370 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_370, 0, x_362);
lean_ctor_set_uint8(x_370, sizeof(void*)*1, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*1 + 1, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*1 + 2, x_363);
lean_ctor_set_uint8(x_370, sizeof(void*)*1 + 3, x_364);
lean_ctor_set_uint8(x_370, sizeof(void*)*1 + 4, x_365);
lean_ctor_set_uint8(x_370, sizeof(void*)*1 + 5, x_366);
lean_ctor_set_uint8(x_370, sizeof(void*)*1 + 6, x_369);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
x_371 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_358);
lean_ctor_set(x_371, 2, x_359);
lean_ctor_set(x_371, 3, x_360);
lean_ctor_set(x_371, 4, x_361);
x_372 = l_Lean_Meta_instantiateMVars(x_1, x_371, x_3);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_375 = x_372;
} else {
 lean_dec_ref(x_372);
 x_375 = lean_box(0);
}
x_376 = l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1;
lean_inc(x_371);
x_377 = l_Lean_Meta_forallTelescopeReducing___rarg(x_373, x_376, x_371, x_374);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_380 = x_377;
} else {
 lean_dec_ref(x_377);
 x_380 = lean_box(0);
}
x_403 = lean_ctor_get(x_379, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_379, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_379, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_379, 3);
lean_inc(x_406);
x_407 = lean_ctor_get(x_379, 4);
lean_inc(x_407);
x_408 = lean_ctor_get(x_379, 5);
lean_inc(x_408);
x_409 = lean_ctor_get(x_405, 2);
lean_inc(x_409);
x_410 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(x_409, x_378);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_460; lean_object* x_461; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 lean_ctor_release(x_379, 4);
 lean_ctor_release(x_379, 5);
 x_411 = x_379;
} else {
 lean_dec_ref(x_379);
 x_411 = lean_box(0);
}
lean_inc(x_404);
x_471 = l_Lean_MetavarContext_incDepth(x_404);
if (lean_is_scalar(x_411)) {
 x_472 = lean_alloc_ctor(0, 6, 0);
} else {
 x_472 = x_411;
}
lean_ctor_set(x_472, 0, x_403);
lean_ctor_set(x_472, 1, x_471);
lean_ctor_set(x_472, 2, x_405);
lean_ctor_set(x_472, 3, x_406);
lean_ctor_set(x_472, 4, x_407);
lean_ctor_set(x_472, 5, x_408);
lean_inc(x_371);
lean_inc(x_378);
x_473 = l___private_Lean_Meta_SynthInstance_5__preprocessOutParam(x_378, x_371, x_472);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_511; uint8_t x_512; 
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
lean_dec(x_473);
x_511 = lean_ctor_get(x_475, 4);
lean_inc(x_511);
x_512 = lean_ctor_get_uint8(x_511, sizeof(void*)*1);
lean_dec(x_511);
if (x_512 == 0)
{
x_476 = x_475;
goto block_510;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
x_513 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_514 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_513, x_371, x_475);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_unbox(x_515);
lean_dec(x_515);
if (x_516 == 0)
{
lean_object* x_517; 
x_517 = lean_ctor_get(x_514, 1);
lean_inc(x_517);
lean_dec(x_514);
x_476 = x_517;
goto block_510;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_518 = lean_ctor_get(x_514, 1);
lean_inc(x_518);
lean_dec(x_514);
lean_inc(x_378);
x_519 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_519, 0, x_378);
x_520 = l_Lean_Meta_synthInstance_x3f___closed__9;
x_521 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_521, 0, x_519);
lean_ctor_set(x_521, 1, x_520);
lean_inc(x_474);
x_522 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_522, 0, x_474);
x_523 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set(x_523, 1, x_522);
x_524 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_513, x_523, x_371, x_518);
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
lean_dec(x_524);
x_476 = x_525;
goto block_510;
}
}
block_510:
{
lean_object* x_477; 
lean_inc(x_371);
x_477 = l_Lean_Meta_SynthInstance_main(x_474, x_367, x_371, x_476);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; 
lean_dec(x_375);
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; 
x_479 = lean_ctor_get(x_477, 1);
lean_inc(x_479);
lean_dec(x_477);
x_412 = x_478;
x_413 = x_479;
goto block_459;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_495; uint8_t x_496; 
x_480 = lean_ctor_get(x_477, 1);
lean_inc(x_480);
lean_dec(x_477);
x_481 = lean_ctor_get(x_478, 0);
lean_inc(x_481);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 x_482 = x_478;
} else {
 lean_dec_ref(x_478);
 x_482 = lean_box(0);
}
x_495 = lean_ctor_get(x_480, 4);
lean_inc(x_495);
x_496 = lean_ctor_get_uint8(x_495, sizeof(void*)*1);
lean_dec(x_495);
if (x_496 == 0)
{
x_483 = x_480;
goto block_494;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; 
x_497 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_498 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_497, x_371, x_480);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_unbox(x_499);
lean_dec(x_499);
if (x_500 == 0)
{
lean_object* x_501; 
x_501 = lean_ctor_get(x_498, 1);
lean_inc(x_501);
lean_dec(x_498);
x_483 = x_501;
goto block_494;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_502 = lean_ctor_get(x_498, 1);
lean_inc(x_502);
lean_dec(x_498);
lean_inc(x_481);
x_503 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_503, 0, x_481);
x_504 = l_Lean_Meta_synthInstance_x3f___closed__6;
x_505 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_505, 0, x_504);
lean_ctor_set(x_505, 1, x_503);
x_506 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_497, x_505, x_371, x_502);
x_507 = lean_ctor_get(x_506, 1);
lean_inc(x_507);
lean_dec(x_506);
x_483 = x_507;
goto block_494;
}
}
block_494:
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; uint8_t x_489; 
x_484 = l_Lean_Meta_instantiateMVars(x_481, x_371, x_483);
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
lean_dec(x_484);
x_487 = l_Lean_Meta_hasAssignableMVar(x_485, x_371, x_486);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_unbox(x_488);
lean_dec(x_488);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; 
x_490 = lean_ctor_get(x_487, 1);
lean_inc(x_490);
lean_dec(x_487);
if (lean_is_scalar(x_482)) {
 x_491 = lean_alloc_ctor(1, 1, 0);
} else {
 x_491 = x_482;
}
lean_ctor_set(x_491, 0, x_485);
x_412 = x_491;
x_413 = x_490;
goto block_459;
}
else
{
lean_object* x_492; lean_object* x_493; 
lean_dec(x_485);
lean_dec(x_482);
x_492 = lean_ctor_get(x_487, 1);
lean_inc(x_492);
lean_dec(x_487);
x_493 = lean_box(0);
x_412 = x_493;
x_413 = x_492;
goto block_459;
}
}
}
}
else
{
lean_object* x_508; lean_object* x_509; 
lean_dec(x_380);
lean_dec(x_378);
lean_dec(x_371);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
x_508 = lean_ctor_get(x_477, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_477, 1);
lean_inc(x_509);
lean_dec(x_477);
x_460 = x_508;
x_461 = x_509;
goto block_470;
}
}
}
else
{
lean_object* x_526; lean_object* x_527; 
lean_dec(x_380);
lean_dec(x_378);
lean_dec(x_371);
lean_dec(x_367);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
x_526 = lean_ctor_get(x_473, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_473, 1);
lean_inc(x_527);
lean_dec(x_473);
x_460 = x_526;
x_461 = x_527;
goto block_470;
}
block_459:
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_413, 3);
lean_inc(x_416);
x_417 = lean_ctor_get(x_413, 4);
lean_inc(x_417);
x_418 = lean_ctor_get(x_413, 5);
lean_inc(x_418);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 lean_ctor_release(x_413, 2);
 lean_ctor_release(x_413, 3);
 lean_ctor_release(x_413, 4);
 lean_ctor_release(x_413, 5);
 x_419 = x_413;
} else {
 lean_dec_ref(x_413);
 x_419 = lean_box(0);
}
lean_inc(x_417);
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(0, 6, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_414);
lean_ctor_set(x_420, 1, x_404);
lean_ctor_set(x_420, 2, x_415);
lean_ctor_set(x_420, 3, x_416);
lean_ctor_set(x_420, 4, x_417);
lean_ctor_set(x_420, 5, x_418);
if (lean_obj_tag(x_412) == 0)
{
lean_dec(x_417);
lean_dec(x_371);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
x_381 = x_412;
x_382 = x_420;
goto block_402;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_447; 
x_421 = lean_ctor_get(x_412, 0);
lean_inc(x_421);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 x_422 = x_412;
} else {
 lean_dec_ref(x_412);
 x_422 = lean_box(0);
}
x_447 = lean_ctor_get_uint8(x_417, sizeof(void*)*1);
lean_dec(x_417);
if (x_447 == 0)
{
x_423 = x_420;
goto block_446;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; 
x_448 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_449 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_448, x_371, x_420);
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_unbox(x_450);
lean_dec(x_450);
if (x_451 == 0)
{
lean_object* x_452; 
x_452 = lean_ctor_get(x_449, 1);
lean_inc(x_452);
lean_dec(x_449);
x_423 = x_452;
goto block_446;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_453 = lean_ctor_get(x_449, 1);
lean_inc(x_453);
lean_dec(x_449);
lean_inc(x_421);
x_454 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_454, 0, x_421);
x_455 = l_Lean_Meta_synthInstance_x3f___closed__3;
x_456 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_454);
x_457 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_448, x_456, x_371, x_453);
x_458 = lean_ctor_get(x_457, 1);
lean_inc(x_458);
lean_dec(x_457);
x_423 = x_458;
goto block_446;
}
}
block_446:
{
lean_object* x_424; 
lean_inc(x_371);
lean_inc(x_421);
x_424 = l_Lean_Meta_inferType(x_421, x_371, x_423);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_427, 0, x_357);
lean_ctor_set(x_427, 1, x_358);
lean_ctor_set(x_427, 2, x_359);
lean_ctor_set(x_427, 3, x_360);
lean_ctor_set(x_427, 4, x_361);
lean_inc(x_378);
x_428 = l_Lean_Meta_isExprDefEq(x_378, x_425, x_427, x_426);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; uint8_t x_430; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_unbox(x_429);
lean_dec(x_429);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; 
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_371);
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
lean_dec(x_428);
x_432 = lean_box(0);
x_381 = x_432;
x_382 = x_431;
goto block_402;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_433 = lean_ctor_get(x_428, 1);
lean_inc(x_433);
lean_dec(x_428);
x_434 = l_Lean_Meta_instantiateMVars(x_421, x_371, x_433);
lean_dec(x_371);
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
if (lean_is_scalar(x_422)) {
 x_437 = lean_alloc_ctor(1, 1, 0);
} else {
 x_437 = x_422;
}
lean_ctor_set(x_437, 0, x_435);
x_381 = x_437;
x_382 = x_436;
goto block_402;
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_380);
lean_dec(x_378);
lean_dec(x_371);
x_438 = lean_ctor_get(x_428, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_428, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_440 = x_428;
} else {
 lean_dec_ref(x_428);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_380);
lean_dec(x_378);
lean_dec(x_371);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
x_442 = lean_ctor_get(x_424, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_424, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_444 = x_424;
} else {
 lean_dec_ref(x_424);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
}
}
block_470:
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 2);
lean_inc(x_463);
x_464 = lean_ctor_get(x_461, 3);
lean_inc(x_464);
x_465 = lean_ctor_get(x_461, 4);
lean_inc(x_465);
x_466 = lean_ctor_get(x_461, 5);
lean_inc(x_466);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 lean_ctor_release(x_461, 2);
 lean_ctor_release(x_461, 3);
 lean_ctor_release(x_461, 4);
 lean_ctor_release(x_461, 5);
 x_467 = x_461;
} else {
 lean_dec_ref(x_461);
 x_467 = lean_box(0);
}
if (lean_is_scalar(x_467)) {
 x_468 = lean_alloc_ctor(0, 6, 0);
} else {
 x_468 = x_467;
}
lean_ctor_set(x_468, 0, x_462);
lean_ctor_set(x_468, 1, x_404);
lean_ctor_set(x_468, 2, x_463);
lean_ctor_set(x_468, 3, x_464);
lean_ctor_set(x_468, 4, x_465);
lean_ctor_set(x_468, 5, x_466);
if (lean_is_scalar(x_375)) {
 x_469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_469 = x_375;
 lean_ctor_set_tag(x_469, 1);
}
lean_ctor_set(x_469, 0, x_460);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
}
else
{
lean_object* x_528; lean_object* x_529; 
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_380);
lean_dec(x_378);
lean_dec(x_371);
lean_dec(x_367);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
x_528 = lean_ctor_get(x_410, 0);
lean_inc(x_528);
lean_dec(x_410);
if (lean_is_scalar(x_375)) {
 x_529 = lean_alloc_ctor(0, 2, 0);
} else {
 x_529 = x_375;
}
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_379);
return x_529;
}
block_402:
{
uint8_t x_383; 
x_383 = l_Lean_Expr_hasMVar(x_378);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_384 = lean_ctor_get(x_382, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_382, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_382, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_382, 3);
lean_inc(x_387);
x_388 = lean_ctor_get(x_382, 4);
lean_inc(x_388);
x_389 = lean_ctor_get(x_382, 5);
lean_inc(x_389);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 lean_ctor_release(x_382, 2);
 lean_ctor_release(x_382, 3);
 lean_ctor_release(x_382, 4);
 lean_ctor_release(x_382, 5);
 x_390 = x_382;
} else {
 lean_dec_ref(x_382);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_384, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_384, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_384, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_384, 3);
lean_inc(x_394);
x_395 = lean_ctor_get(x_384, 4);
lean_inc(x_395);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 lean_ctor_release(x_384, 2);
 lean_ctor_release(x_384, 3);
 lean_ctor_release(x_384, 4);
 x_396 = x_384;
} else {
 lean_dec_ref(x_384);
 x_396 = lean_box(0);
}
lean_inc(x_381);
x_397 = l_Std_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(x_393, x_378, x_381);
if (lean_is_scalar(x_396)) {
 x_398 = lean_alloc_ctor(0, 5, 0);
} else {
 x_398 = x_396;
}
lean_ctor_set(x_398, 0, x_391);
lean_ctor_set(x_398, 1, x_392);
lean_ctor_set(x_398, 2, x_397);
lean_ctor_set(x_398, 3, x_394);
lean_ctor_set(x_398, 4, x_395);
if (lean_is_scalar(x_390)) {
 x_399 = lean_alloc_ctor(0, 6, 0);
} else {
 x_399 = x_390;
}
lean_ctor_set(x_399, 0, x_385);
lean_ctor_set(x_399, 1, x_386);
lean_ctor_set(x_399, 2, x_398);
lean_ctor_set(x_399, 3, x_387);
lean_ctor_set(x_399, 4, x_388);
lean_ctor_set(x_399, 5, x_389);
if (lean_is_scalar(x_380)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_380;
}
lean_ctor_set(x_400, 0, x_381);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
else
{
lean_object* x_401; 
lean_dec(x_378);
if (lean_is_scalar(x_380)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_380;
}
lean_ctor_set(x_401, 0, x_381);
lean_ctor_set(x_401, 1, x_382);
return x_401;
}
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_375);
lean_dec(x_371);
lean_dec(x_367);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
x_530 = lean_ctor_get(x_377, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_377, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_532 = x_377;
} else {
 lean_dec_ref(x_377);
 x_532 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_533 = lean_alloc_ctor(1, 2, 0);
} else {
 x_533 = x_532;
}
lean_ctor_set(x_533, 0, x_530);
lean_ctor_set(x_533, 1, x_531);
return x_533;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_trySynthInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 4, x_7);
x_8 = l_Lean_Meta_synthInstance_x3f(x_1, x_2, x_3);
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
switch (lean_obj_tag(x_16)) {
case 11:
{
uint8_t x_17; 
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = lean_box(2);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_box(2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
case 12:
{
uint8_t x_23; 
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_8, 0);
lean_dec(x_24);
x_25 = lean_box(2);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_box(2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_8, 0);
lean_dec(x_30);
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_dec(x_8);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_5, 0);
x_34 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_35 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_36 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_37 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
x_39 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 6);
lean_inc(x_33);
lean_dec(x_5);
x_40 = 1;
x_41 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_34);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 1, x_35);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 2, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 3, x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 4, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 5, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 6, x_39);
lean_ctor_set(x_2, 0, x_41);
x_42 = l_Lean_Meta_synthInstance_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = l_Option_toLOption___rarg(x_43);
lean_dec(x_43);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
switch (lean_obj_tag(x_48)) {
case 11:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_48);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_50 = x_42;
} else {
 lean_dec_ref(x_42);
 x_50 = lean_box(0);
}
x_51 = lean_box(2);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
 lean_ctor_set_tag(x_52, 0);
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
case 12:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_48);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_54 = x_42;
} else {
 lean_dec_ref(x_42);
 x_54 = lean_box(0);
}
x_55 = lean_box(2);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
 lean_ctor_set_tag(x_56, 0);
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
default: 
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_58 = x_42;
} else {
 lean_dec_ref(x_42);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = lean_ctor_get(x_2, 1);
x_62 = lean_ctor_get(x_2, 2);
x_63 = lean_ctor_get(x_2, 3);
x_64 = lean_ctor_get(x_2, 4);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_2);
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_60, sizeof(void*)*1);
x_67 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 1);
x_68 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 2);
x_69 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 3);
x_70 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 5);
x_71 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 6);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_72 = x_60;
} else {
 lean_dec_ref(x_60);
 x_72 = lean_box(0);
}
x_73 = 1;
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 1, 7);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_66);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 1, x_67);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 2, x_68);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 3, x_69);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 4, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 5, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 6, x_71);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_61);
lean_ctor_set(x_75, 2, x_62);
lean_ctor_set(x_75, 3, x_63);
lean_ctor_set(x_75, 4, x_64);
x_76 = l_Lean_Meta_synthInstance_x3f(x_1, x_75, x_3);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = l_Option_toLOption___rarg(x_77);
lean_dec(x_77);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_inc(x_82);
switch (lean_obj_tag(x_82)) {
case 11:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_82);
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_84 = x_76;
} else {
 lean_dec_ref(x_76);
 x_84 = lean_box(0);
}
x_85 = lean_box(2);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
 lean_ctor_set_tag(x_86, 0);
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
case 12:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_82);
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_88 = x_76;
} else {
 lean_dec_ref(x_76);
 x_88 = lean_box(0);
}
x_89 = lean_box(2);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
 lean_ctor_set_tag(x_90, 0);
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
default: 
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_76, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_92 = x_76;
} else {
 lean_dec_ref(x_76);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
}
}
lean_object* l_Lean_Meta_synthInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_synthInstance_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_13);
x_15 = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_4, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
return x_4;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Lean_Meta_synthPendingImp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_Meta_getMVarDecl(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*5);
x_7 = lean_box(x_6);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
lean_dec(x_5);
lean_inc(x_2);
lean_inc(x_9);
x_10 = l_Lean_Meta_isClass(x_9, x_2, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
lean_inc(x_2);
x_21 = l_Lean_Meta_synthInstance_x3f(x_9, x_2, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
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
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_21, 1);
x_33 = lean_ctor_get(x_21, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_1);
x_36 = lean_metavar_ctx_is_expr_assigned(x_35, x_1);
if (x_36 == 0)
{
lean_object* x_37; 
lean_free_object(x_21);
x_37 = l_Lean_Meta_assignExprMVar(x_1, x_34, x_2, x_32);
lean_dec(x_2);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = 1;
x_41 = lean_box(x_40);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = 1;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 0);
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_37);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; lean_object* x_51; 
lean_dec(x_34);
lean_dec(x_2);
lean_dec(x_1);
x_50 = 0;
x_51 = lean_box(x_50);
lean_ctor_set(x_21, 0, x_51);
return x_21;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
lean_dec(x_21);
x_53 = lean_ctor_get(x_22, 0);
lean_inc(x_53);
lean_dec(x_22);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_inc(x_1);
x_55 = lean_metavar_ctx_is_expr_assigned(x_54, x_1);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_Lean_Meta_assignExprMVar(x_1, x_53, x_2, x_52);
lean_dec(x_2);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = 1;
x_60 = lean_box(x_59);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_53);
lean_dec(x_2);
lean_dec(x_1);
x_66 = 0;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_52);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_21);
if (x_69 == 0)
{
return x_21;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_21, 0);
x_71 = lean_ctor_get(x_21, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_21);
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
uint8_t x_73; 
lean_dec(x_9);
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
else
{
uint8_t x_77; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_4);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_4, 0);
lean_dec(x_78);
x_79 = 0;
x_80 = lean_box(x_79);
lean_ctor_set(x_4, 0, x_80);
return x_4;
}
else
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_4, 1);
lean_inc(x_81);
lean_dec(x_4);
x_82 = 0;
x_83 = lean_box(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_4);
if (x_85 == 0)
{
return x_4;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_4, 0);
x_87 = lean_ctor_get(x_4, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_4);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
lean_object* _init_l_Lean_Meta_setSynthPendingRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_synthPendingImp), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_setSynthPendingRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_synthPendingRef;
x_3 = l_Lean_Meta_setSynthPendingRef___closed__1;
x_4 = lean_io_ref_set(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_7__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_9 = l_Lean_registerTraceClass(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_12 = l_Lean_registerTraceClass(x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_15 = l_Lean_registerTraceClass(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_18 = l_Lean_registerTraceClass(x_17, x_16);
return x_18;
}
else
{
uint8_t x_19; 
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
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_6);
if (x_31 == 0)
{
return x_6;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
return x_3;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_3);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_Instances(lean_object*);
lean_object* initialize_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Lean_Meta_AbstractMVars(lean_object*);
lean_object* initialize_Lean_Meta_WHNF(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_SynthInstance(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Instances(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AbstractMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1 = _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1);
l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2 = _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2);
l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3 = _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3);
l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4 = _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4);
res = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr);
lean_dec_ref(res);
l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1 = _init_l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1);
l_Lean_Meta_SynthInstance_GeneratorNode_inhabited = _init_l_Lean_Meta_SynthInstance_GeneratorNode_inhabited();
lean_mark_persistent(l_Lean_Meta_SynthInstance_GeneratorNode_inhabited);
l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1 = _init_l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1);
l_Lean_Meta_SynthInstance_Consumernode_inhabited = _init_l_Lean_Meta_SynthInstance_Consumernode_inhabited();
lean_mark_persistent(l_Lean_Meta_SynthInstance_Consumernode_inhabited);
l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1 = _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1);
l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2 = _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2);
l_Lean_Meta_SynthInstance_mkTableKey___closed__1 = _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKey___closed__1);
l_Lean_Meta_SynthInstance_mkTableKey___closed__2 = _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKey___closed__2);
l_Lean_Meta_SynthInstance_mkTableKey___closed__3 = _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKey___closed__3);
l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1 = _init_l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1);
l_Lean_Meta_SynthInstance_Answer_inhabited = _init_l_Lean_Meta_SynthInstance_Answer_inhabited();
lean_mark_persistent(l_Lean_Meta_SynthInstance_Answer_inhabited);
l_Lean_Meta_SynthInstance_SynthM_inhabited___closed__1 = _init_l_Lean_Meta_SynthInstance_SynthM_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_SynthM_inhabited___closed__1);
l_Lean_Meta_SynthInstance_tracer___closed__1 = _init_l_Lean_Meta_SynthInstance_tracer___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tracer___closed__1);
l_Lean_Meta_SynthInstance_tracer___closed__2 = _init_l_Lean_Meta_SynthInstance_tracer___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tracer___closed__2);
l_Lean_Meta_SynthInstance_tracer___closed__3 = _init_l_Lean_Meta_SynthInstance_tracer___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tracer___closed__3);
l_Lean_Meta_SynthInstance_tracer___closed__4 = _init_l_Lean_Meta_SynthInstance_tracer___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tracer___closed__4);
l_Lean_Meta_SynthInstance_tracer___closed__5 = _init_l_Lean_Meta_SynthInstance_tracer___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tracer___closed__5);
l_Lean_Meta_SynthInstance_tracer = _init_l_Lean_Meta_SynthInstance_tracer();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tracer);
l_Lean_Meta_SynthInstance_meta2Synth___closed__1 = _init_l_Lean_Meta_SynthInstance_meta2Synth___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_meta2Synth___closed__1);
l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1);
l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2);
l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3);
l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3);
l_Lean_Meta_SynthInstance_getInstances___closed__1 = _init_l_Lean_Meta_SynthInstance_getInstances___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___closed__1);
l_Lean_Meta_SynthInstance_newSubgoal___closed__1 = _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___closed__1);
l_Lean_Meta_SynthInstance_newSubgoal___closed__2 = _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___closed__2);
l_Lean_Meta_SynthInstance_getEntry___closed__1 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__1);
l_Lean_Meta_SynthInstance_getEntry___closed__2 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__2);
l_Lean_Meta_SynthInstance_getEntry___closed__3 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__3);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5);
l_Lean_Meta_SynthInstance_tryAnswer___closed__1 = _init_l_Lean_Meta_SynthInstance_tryAnswer___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryAnswer___closed__1);
l_Lean_Meta_SynthInstance_wakeUp___closed__1 = _init_l_Lean_Meta_SynthInstance_wakeUp___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___closed__1);
l_Lean_Meta_SynthInstance_wakeUp___closed__2 = _init_l_Lean_Meta_SynthInstance_wakeUp___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___closed__2);
l_Lean_Meta_SynthInstance_wakeUp___closed__3 = _init_l_Lean_Meta_SynthInstance_wakeUp___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___closed__3);
l_Lean_Meta_SynthInstance_addAnswer___closed__1 = _init_l_Lean_Meta_SynthInstance_addAnswer___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___closed__1);
l_Lean_Meta_SynthInstance_addAnswer___closed__2 = _init_l_Lean_Meta_SynthInstance_addAnswer___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___closed__2);
l_Lean_Meta_SynthInstance_generate___closed__1 = _init_l_Lean_Meta_SynthInstance_generate___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__1);
l_Lean_Meta_SynthInstance_generate___closed__2 = _init_l_Lean_Meta_SynthInstance_generate___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__2);
l_Lean_Meta_SynthInstance_generate___closed__3 = _init_l_Lean_Meta_SynthInstance_generate___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__3);
l_Lean_Meta_SynthInstance_generate___closed__4 = _init_l_Lean_Meta_SynthInstance_generate___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__4);
l_Lean_Meta_SynthInstance_generate___closed__5 = _init_l_Lean_Meta_SynthInstance_generate___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__5);
l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1 = _init_l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1();
lean_mark_persistent(l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1);
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
l_Lean_Meta_SynthInstance_synth___main___closed__1 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__1);
l_Lean_Meta_SynthInstance_synth___main___closed__2 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__2);
l_Lean_Meta_SynthInstance_synth___main___closed__3 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__3);
l_Lean_Meta_SynthInstance_synth___main___closed__4 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__4);
l_Lean_Meta_SynthInstance_synth___main___closed__5 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__5);
l_Lean_Meta_SynthInstance_synth___main___closed__6 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__6);
l_Lean_Meta_SynthInstance_synth___main___closed__7 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__7);
l_Lean_Meta_SynthInstance_synth___main___closed__8 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__8();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__8);
l_Lean_Meta_SynthInstance_synth___main___closed__9 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__9();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__9);
l_Lean_Meta_SynthInstance_main___closed__1 = _init_l_Lean_Meta_SynthInstance_main___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___closed__1);
l_Lean_Meta_SynthInstance_main___closed__2 = _init_l_Lean_Meta_SynthInstance_main___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___closed__2);
l_Lean_Meta_SynthInstance_main___closed__3 = _init_l_Lean_Meta_SynthInstance_main___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___closed__3);
l_Lean_Meta_SynthInstance_main___closed__4 = _init_l_Lean_Meta_SynthInstance_main___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___closed__4);
l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1 = _init_l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1);
l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1 = _init_l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1);
l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2 = _init_l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2);
l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__3 = _init_l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__3);
l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__4 = _init_l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__4);
l_Lean_Meta_maxStepsOption___closed__1 = _init_l_Lean_Meta_maxStepsOption___closed__1();
lean_mark_persistent(l_Lean_Meta_maxStepsOption___closed__1);
l_Lean_Meta_maxStepsOption___closed__2 = _init_l_Lean_Meta_maxStepsOption___closed__2();
lean_mark_persistent(l_Lean_Meta_maxStepsOption___closed__2);
l_Lean_Meta_maxStepsOption___closed__3 = _init_l_Lean_Meta_maxStepsOption___closed__3();
lean_mark_persistent(l_Lean_Meta_maxStepsOption___closed__3);
l_Lean_Meta_maxStepsOption___closed__4 = _init_l_Lean_Meta_maxStepsOption___closed__4();
lean_mark_persistent(l_Lean_Meta_maxStepsOption___closed__4);
l_Lean_Meta_maxStepsOption___closed__5 = _init_l_Lean_Meta_maxStepsOption___closed__5();
lean_mark_persistent(l_Lean_Meta_maxStepsOption___closed__5);
res = l_Lean_Meta_maxStepsOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_synthInstance_x3f___closed__1 = _init_l_Lean_Meta_synthInstance_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__1);
l_Lean_Meta_synthInstance_x3f___closed__2 = _init_l_Lean_Meta_synthInstance_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__2);
l_Lean_Meta_synthInstance_x3f___closed__3 = _init_l_Lean_Meta_synthInstance_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__3);
l_Lean_Meta_synthInstance_x3f___closed__4 = _init_l_Lean_Meta_synthInstance_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__4);
l_Lean_Meta_synthInstance_x3f___closed__5 = _init_l_Lean_Meta_synthInstance_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__5);
l_Lean_Meta_synthInstance_x3f___closed__6 = _init_l_Lean_Meta_synthInstance_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__6);
l_Lean_Meta_synthInstance_x3f___closed__7 = _init_l_Lean_Meta_synthInstance_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__7);
l_Lean_Meta_synthInstance_x3f___closed__8 = _init_l_Lean_Meta_synthInstance_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__8);
l_Lean_Meta_synthInstance_x3f___closed__9 = _init_l_Lean_Meta_synthInstance_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__9);
l_Lean_Meta_setSynthPendingRef___closed__1 = _init_l_Lean_Meta_setSynthPendingRef___closed__1();
lean_mark_persistent(l_Lean_Meta_setSynthPendingRef___closed__1);
res = l_Lean_Meta_setSynthPendingRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_SynthInstance_7__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

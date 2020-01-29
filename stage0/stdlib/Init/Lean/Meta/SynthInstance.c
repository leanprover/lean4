// Lean compiler output
// Module: Init.Lean.Meta.SynthInstance
// Imports: Init.Default Init.Lean.Meta.Basic Init.Lean.Meta.Instances Init.Lean.Meta.LevelDefEq Init.Lean.Meta.AbstractMVars
#include "runtime/lean.h"
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
lean_object* l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__51;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__3;
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_out_param(lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_addAnswer(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__1(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getTop(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__2;
lean_object* l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__1;
lean_object* l_Lean_Meta_SynthInstance_tryAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_toLOption___rarg(lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__7(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_SynthInstance_7__regTraceClasses(lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___closed__5;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_Meta_SynthInstance_addAnswer___closed__1;
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__7;
lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_addAnswer___closed__2;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
lean_object* l_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_Basic_10__regTraceClasses___closed__2;
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getResult(lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_maxStepsOption___closed__5;
lean_object* l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___closed__3;
lean_object* l_Lean_Meta_SynthInstance_getTraceState___boxed(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__1;
lean_object* l_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__2(lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_maxStepsOption(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Answer_inhabited;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_withMCtx(lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_synthInstance_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5;
extern lean_object* l_Lean_Meta_Exception_Inhabited___closed__1;
lean_object* l___private_Init_Lean_Meta_SynthInstance_2__preprocess(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__2;
lean_object* l_Lean_Meta_SynthInstance_main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2;
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2;
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_maxStepsOption___closed__3;
lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3;
lean_object* l___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___boxed(lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_SynthInstance_2__preprocess___closed__1;
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__5;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_AssocList_find___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__73;
lean_object* l___private_Init_Lean_Meta_SynthInstance_6__getMaxSteps(lean_object*);
lean_object* l___private_Init_Lean_Meta_SynthInstance_2__preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVarsResult_inhabited___closed__1;
uint8_t l_Lean_Meta_SynthInstance_Waiter_isRoot(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_meta2Synth(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getTop___boxed(lean_object*);
extern lean_object* l_Lean_TagAttribute_Inhabited___closed__1;
lean_object* l_Lean_Meta_abstractMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_SynthInstance_6__getMaxSteps___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_SynthInstance_5__preprocessOutParam___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__6;
lean_object* l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__3;
lean_object* l_Lean_Meta_SynthInstance_getTraceState(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getOptions(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___closed__3;
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(lean_object*, lean_object*);
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
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_modifyTop(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___boxed(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__2;
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(lean_object*, lean_object*);
extern lean_object* l_Lean_mkReducibilityAttrs___lambda__1___closed__1;
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_GeneratorNode_inhabited;
lean_object* l_Lean_Meta_SynthInstance_getTraceState___rarg(lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_getGlobalInstances___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getOptions___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__4;
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1;
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_step(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__9;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Meta_SynthInstance_main___spec__1(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__5;
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l___private_Init_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_posOfAux___main___closed__2;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__3;
extern uint8_t l_String_posOfAux___main___closed__1;
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getNextToResume___boxed(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__7;
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___closed__4;
size_t l_USize_land(size_t, size_t);
lean_object* l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getResult___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__4;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4;
lean_object* l_Lean_Meta_SynthInstance_getEntry(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___closed__6;
lean_object* l_Lean_Meta_SynthInstance_synth(lean_object*, lean_object*, lean_object*);
lean_object* l_fix1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__2;
uint8_t l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__1;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_SynthInstance_1__getSubgoalsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__2;
lean_object* l_Lean_Meta_synthInstance_x3f___closed__3;
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__5;
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2;
lean_object* l_Lean_Meta_SynthInstance_wakeUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_withMCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getTop___rarg(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__6;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Meta_SynthInstance_isNewAnswer(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__6;
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__8;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
lean_object* l_List_foldlM___main___at___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_addContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Waiter_isRoot___boxed(lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_incDepth(lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getResult___boxed(lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__2;
lean_object* l_Lean_Meta_SynthInstance_tracer;
lean_object* l_Lean_Meta_SynthInstance_mkTableKey(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_SynthInstance_5__preprocessOutParam(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__72;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__4;
lean_object* l_Lean_Meta_SynthInstance_getNextToResume(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_isNewAnswer___boxed(lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isLevelAssignable(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__9;
lean_object* l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
lean_object* l_Lean_Meta_SynthInstance_Consumernode_inhabited;
extern lean_object* l_Lean_Meta_isLevelDefEq___closed__9;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2;
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_modifyTop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___closed__2;
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Meta_SynthInstance_generate___closed__1;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__1;
lean_object* l_Lean_Meta_maxStepsOption___closed__1;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1;
lean_object* l_Lean_Meta_maxStepsOption___closed__2;
lean_object* l_Lean_Meta_SynthInstance_getInstances___closed__1;
uint8_t l_Lean_MetavarContext_isExprAssignable(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1;
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_SynthInstance_liftMeta___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
lean_object* l_Lean_Meta_SynthInstance_consume(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__4;
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__1___rarg(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__2;
lean_object* l___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2;
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3;
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__1;
lean_object* l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__2;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___closed__2;
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_Lean_Meta_SynthInstance_tracer___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_has_out_params(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__2;
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__8;
lean_object* l_Lean_Meta_SynthInstance_generate___closed__4;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___closed__1;
lean_object* l_Lean_Meta_SynthInstance_resume___closed__1;
lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__3;
lean_object* l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_toArray___rarg(lean_object*);
lean_object* l_Lean_Meta_maxStepsOption___closed__4;
lean_object* l_Lean_Meta_SynthInstance_liftMeta(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkReducibilityAttrs___lambda__1___closed__1;
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
lean_object* _init_l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_TagAttribute_Inhabited___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__1;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_AttributeImpl_inhabited___closed__2;
x_2 = l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
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
lean_object* l_AssocList_find___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__7(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(x_2, x_10);
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_10);
x_16 = lean_array_uset(x_6, x_9, x_15);
x_17 = lean_nat_dec_le(x_14, x_7);
lean_dec(x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(x_14, x_16);
return x_18;
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
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Name_hash(x_2);
x_25 = lean_usize_modn(x_24, x_23);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(x_2, x_26);
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_21, x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_26);
x_32 = lean_array_uset(x_22, x_25, x_31);
x_33 = lean_nat_dec_le(x_30, x_23);
lean_dec(x_23);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(x_30, x_32);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
uint8_t x_4; uint8_t x_77; 
x_77 = l_Lean_Level_hasMVar(x_1);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = 1;
x_4 = x_78;
goto block_76;
}
else
{
uint8_t x_79; 
x_79 = 0;
x_4 = x_79;
goto block_76;
}
block_76:
{
uint8_t x_5; 
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
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
lean_object* x_41; uint8_t x_42; uint8_t x_71; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_71 = l_Lean_MetavarContext_isLevelAssignable(x_2, x_41);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = 1;
x_42 = x_72;
goto block_70;
}
else
{
uint8_t x_73; 
x_73 = 0;
x_42 = x_73;
goto block_70;
}
block_70:
{
uint8_t x_43; 
x_43 = l_coeDecidableEq(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
x_47 = l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(x_45, x_41);
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
x_57 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(x_45, x_41, x_54);
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
x_64 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(x_45, x_41, x_61);
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
else
{
lean_object* x_69; 
lean_dec(x_41);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_3);
return x_69;
}
}
}
default: 
{
lean_object* x_74; 
lean_dec(x_2);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_3);
return x_74;
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_2);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_3);
return x_75;
}
}
}
}
lean_object* l_AssocList_find___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(x_1, x_2);
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
lean_object* l_AssocList_find___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__7(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(x_2, x_10);
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_10);
x_16 = lean_array_uset(x_6, x_9, x_15);
x_17 = lean_nat_dec_le(x_14, x_7);
lean_dec(x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(x_14, x_16);
return x_18;
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
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Name_hash(x_2);
x_25 = lean_usize_modn(x_24, x_23);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(x_2, x_26);
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_21, x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_26);
x_32 = lean_array_uset(x_22, x_25, x_31);
x_33 = lean_nat_dec_le(x_30, x_23);
lean_dec(x_23);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(x_30, x_32);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
uint8_t x_4; uint8_t x_140; 
x_140 = l_Lean_Expr_hasMVar(x_1);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = 1;
x_4 = x_141;
goto block_139;
}
else
{
uint8_t x_142; 
x_142 = 0;
x_4 = x_142;
goto block_139;
}
block_139:
{
uint8_t x_5; 
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_6; uint8_t x_7; uint8_t x_36; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_36 = l_Lean_MetavarContext_isExprAssignable(x_2, x_6);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = 1;
x_7 = x_37;
goto block_35;
}
else
{
uint8_t x_38; 
x_38 = 0;
x_7 = x_38;
goto block_35;
}
block_35:
{
uint8_t x_8; 
x_8 = l_coeDecidableEq(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(x_11, x_6);
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
x_22 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(x_11, x_6, x_19);
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
x_29 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(x_11, x_6, x_26);
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
else
{
lean_object* x_34; 
lean_dec(x_6);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
}
}
case 3:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_39, x_2, x_3);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_expr_update_sort(x_1, x_42);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_expr_update_sort(x_1, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
case 4:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(x_48, x_2, x_3);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_expr_update_const(x_1, x_51);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_expr_update_const(x_1, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
case 5:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
lean_inc(x_2);
x_59 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_57, x_2, x_3);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_58, x_2, x_61);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_expr_update_app(x_1, x_60, x_64);
lean_ctor_set(x_62, 0, x_65);
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_62);
x_68 = lean_expr_update_app(x_1, x_60, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
case 6:
{
lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_70 = lean_ctor_get(x_1, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 2);
lean_inc(x_71);
x_72 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_2);
x_73 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_70, x_2, x_3);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_71, x_2, x_75);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = (uint8_t)((x_72 << 24) >> 61);
x_80 = lean_expr_update_lambda(x_1, x_79, x_74, x_78);
lean_ctor_set(x_76, 0, x_80);
return x_76;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_76, 0);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_76);
x_83 = (uint8_t)((x_72 << 24) >> 61);
x_84 = lean_expr_update_lambda(x_1, x_83, x_74, x_81);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
case 7:
{
lean_object* x_86; lean_object* x_87; uint64_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_86 = lean_ctor_get(x_1, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 2);
lean_inc(x_87);
x_88 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_2);
x_89 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_86, x_2, x_3);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_87, x_2, x_91);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = (uint8_t)((x_88 << 24) >> 61);
x_96 = lean_expr_update_forall(x_1, x_95, x_90, x_94);
lean_ctor_set(x_92, 0, x_96);
return x_92;
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_92, 0);
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_92);
x_99 = (uint8_t)((x_88 << 24) >> 61);
x_100 = lean_expr_update_forall(x_1, x_99, x_90, x_97);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
}
case 8:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_102 = lean_ctor_get(x_1, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_1, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_1, 3);
lean_inc(x_104);
lean_inc(x_2);
x_105 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_102, x_2, x_3);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_2);
x_108 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_103, x_2, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_104, x_2, x_110);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_expr_update_let(x_1, x_106, x_109, x_113);
lean_ctor_set(x_111, 0, x_114);
return x_111;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_111, 0);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_111);
x_117 = lean_expr_update_let(x_1, x_106, x_109, x_115);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
case 10:
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_1, 1);
lean_inc(x_119);
x_120 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_119, x_2, x_3);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_expr_update_mdata(x_1, x_122);
lean_ctor_set(x_120, 0, x_123);
return x_120;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_120, 0);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_120);
x_126 = lean_expr_update_mdata(x_1, x_124);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
case 11:
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_128 = lean_ctor_get(x_1, 2);
lean_inc(x_128);
x_129 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_128, x_2, x_3);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_expr_update_proj(x_1, x_131);
lean_ctor_set(x_129, 0, x_132);
return x_129;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_129, 0);
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_129);
x_135 = lean_expr_update_proj(x_1, x_133);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
default: 
{
lean_object* x_137; 
lean_dec(x_2);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_3);
return x_137;
}
}
}
else
{
lean_object* x_138; 
lean_dec(x_2);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_1);
lean_ctor_set(x_138, 1, x_3);
return x_138;
}
}
}
}
lean_object* l_AssocList_find___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(x_1, x_2);
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
lean_object* l_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
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
x_1 = l_Lean_Meta_Exception_Inhabited___closed__1;
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
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_6, 1, x_1);
x_9 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_11, 1);
lean_dec(x_17);
lean_ctor_set(x_11, 1, x_8);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
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
return x_9;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_10, 1);
x_25 = lean_ctor_get(x_10, 2);
x_26 = lean_ctor_get(x_10, 3);
x_27 = lean_ctor_get(x_10, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_11, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_11, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 5);
lean_inc(x_32);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_33 = x_11;
} else {
 lean_dec_ref(x_11);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set(x_9, 1, x_35);
return x_9;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_9, 0);
lean_inc(x_36);
lean_dec(x_9);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_10, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_10, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_10, 4);
lean_inc(x_40);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 x_41 = x_10;
} else {
 lean_dec_ref(x_10);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_11, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_11, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_11, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_11, 5);
lean_inc(x_46);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_47 = x_11;
} else {
 lean_dec_ref(x_11);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 6, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_8);
lean_ctor_set(x_48, 2, x_43);
lean_ctor_set(x_48, 3, x_44);
lean_ctor_set(x_48, 4, x_45);
lean_ctor_set(x_48, 5, x_46);
if (lean_is_scalar(x_41)) {
 x_49 = lean_alloc_ctor(0, 5, 0);
} else {
 x_49 = x_41;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_37);
lean_ctor_set(x_49, 2, x_38);
lean_ctor_set(x_49, 3, x_39);
lean_ctor_set(x_49, 4, x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_9, 1);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_51, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_52, 1);
lean_dec(x_58);
lean_ctor_set(x_52, 1, x_8);
return x_9;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_52, 0);
x_60 = lean_ctor_get(x_52, 2);
x_61 = lean_ctor_get(x_52, 3);
x_62 = lean_ctor_get(x_52, 4);
x_63 = lean_ctor_get(x_52, 5);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_52);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_8);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_63);
lean_ctor_set(x_51, 0, x_64);
return x_9;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_65 = lean_ctor_get(x_51, 1);
x_66 = lean_ctor_get(x_51, 2);
x_67 = lean_ctor_get(x_51, 3);
x_68 = lean_ctor_get(x_51, 4);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_51);
x_69 = lean_ctor_get(x_52, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_52, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_52, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_52, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_52, 5);
lean_inc(x_73);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 x_74 = x_52;
} else {
 lean_dec_ref(x_52);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 6, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_8);
lean_ctor_set(x_75, 2, x_70);
lean_ctor_set(x_75, 3, x_71);
lean_ctor_set(x_75, 4, x_72);
lean_ctor_set(x_75, 5, x_73);
x_76 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_65);
lean_ctor_set(x_76, 2, x_66);
lean_ctor_set(x_76, 3, x_67);
lean_ctor_set(x_76, 4, x_68);
lean_ctor_set(x_9, 1, x_76);
return x_9;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_77 = lean_ctor_get(x_9, 0);
lean_inc(x_77);
lean_dec(x_9);
x_78 = lean_ctor_get(x_51, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_51, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_51, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_51, 4);
lean_inc(x_81);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 lean_ctor_release(x_51, 4);
 x_82 = x_51;
} else {
 lean_dec_ref(x_51);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_52, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_52, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_52, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_52, 4);
lean_inc(x_86);
x_87 = lean_ctor_get(x_52, 5);
lean_inc(x_87);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 x_88 = x_52;
} else {
 lean_dec_ref(x_52);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 6, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_8);
lean_ctor_set(x_89, 2, x_84);
lean_ctor_set(x_89, 3, x_85);
lean_ctor_set(x_89, 4, x_86);
lean_ctor_set(x_89, 5, x_87);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 5, 0);
} else {
 x_90 = x_82;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_78);
lean_ctor_set(x_90, 2, x_79);
lean_ctor_set(x_90, 3, x_80);
lean_ctor_set(x_90, 4, x_81);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_77);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_6, 0);
x_93 = lean_ctor_get(x_6, 1);
x_94 = lean_ctor_get(x_6, 2);
x_95 = lean_ctor_get(x_6, 3);
x_96 = lean_ctor_get(x_6, 4);
x_97 = lean_ctor_get(x_6, 5);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_6);
x_98 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_98, 0, x_92);
lean_ctor_set(x_98, 1, x_1);
lean_ctor_set(x_98, 2, x_94);
lean_ctor_set(x_98, 3, x_95);
lean_ctor_set(x_98, 4, x_96);
lean_ctor_set(x_98, 5, x_97);
lean_ctor_set(x_4, 0, x_98);
x_99 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_103 = x_99;
} else {
 lean_dec_ref(x_99);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_100, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_100, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_100, 4);
lean_inc(x_107);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 lean_ctor_release(x_100, 2);
 lean_ctor_release(x_100, 3);
 lean_ctor_release(x_100, 4);
 x_108 = x_100;
} else {
 lean_dec_ref(x_100);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_101, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_101, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_101, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_101, 4);
lean_inc(x_112);
x_113 = lean_ctor_get(x_101, 5);
lean_inc(x_113);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 lean_ctor_release(x_101, 4);
 lean_ctor_release(x_101, 5);
 x_114 = x_101;
} else {
 lean_dec_ref(x_101);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 6, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_93);
lean_ctor_set(x_115, 2, x_110);
lean_ctor_set(x_115, 3, x_111);
lean_ctor_set(x_115, 4, x_112);
lean_ctor_set(x_115, 5, x_113);
if (lean_is_scalar(x_108)) {
 x_116 = lean_alloc_ctor(0, 5, 0);
} else {
 x_116 = x_108;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_104);
lean_ctor_set(x_116, 2, x_105);
lean_ctor_set(x_116, 3, x_106);
lean_ctor_set(x_116, 4, x_107);
if (lean_is_scalar(x_103)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_103;
}
lean_ctor_set(x_117, 0, x_102);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_118 = lean_ctor_get(x_99, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_99, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_121 = x_99;
} else {
 lean_dec_ref(x_99);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_118, 3);
lean_inc(x_124);
x_125 = lean_ctor_get(x_118, 4);
lean_inc(x_125);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 x_126 = x_118;
} else {
 lean_dec_ref(x_118);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_119, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_119, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_119, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_119, 4);
lean_inc(x_130);
x_131 = lean_ctor_get(x_119, 5);
lean_inc(x_131);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 lean_ctor_release(x_119, 5);
 x_132 = x_119;
} else {
 lean_dec_ref(x_119);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 6, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_93);
lean_ctor_set(x_133, 2, x_128);
lean_ctor_set(x_133, 3, x_129);
lean_ctor_set(x_133, 4, x_130);
lean_ctor_set(x_133, 5, x_131);
if (lean_is_scalar(x_126)) {
 x_134 = lean_alloc_ctor(0, 5, 0);
} else {
 x_134 = x_126;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_122);
lean_ctor_set(x_134, 2, x_123);
lean_ctor_set(x_134, 3, x_124);
lean_ctor_set(x_134, 4, x_125);
if (lean_is_scalar(x_121)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_121;
}
lean_ctor_set(x_135, 0, x_120);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_136 = lean_ctor_get(x_4, 0);
x_137 = lean_ctor_get(x_4, 1);
x_138 = lean_ctor_get(x_4, 2);
x_139 = lean_ctor_get(x_4, 3);
x_140 = lean_ctor_get(x_4, 4);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_4);
x_141 = lean_ctor_get(x_136, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_136, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_136, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_136, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_136, 5);
lean_inc(x_146);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 lean_ctor_release(x_136, 3);
 lean_ctor_release(x_136, 4);
 lean_ctor_release(x_136, 5);
 x_147 = x_136;
} else {
 lean_dec_ref(x_136);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 6, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_1);
lean_ctor_set(x_148, 2, x_143);
lean_ctor_set(x_148, 3, x_144);
lean_ctor_set(x_148, 4, x_145);
lean_ctor_set(x_148, 5, x_146);
x_149 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_137);
lean_ctor_set(x_149, 2, x_138);
lean_ctor_set(x_149, 3, x_139);
lean_ctor_set(x_149, 4, x_140);
x_150 = lean_apply_2(x_2, x_3, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_154 = x_150;
} else {
 lean_dec_ref(x_150);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_151, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_151, 4);
lean_inc(x_158);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 lean_ctor_release(x_151, 3);
 lean_ctor_release(x_151, 4);
 x_159 = x_151;
} else {
 lean_dec_ref(x_151);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_152, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_152, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_152, 3);
lean_inc(x_162);
x_163 = lean_ctor_get(x_152, 4);
lean_inc(x_163);
x_164 = lean_ctor_get(x_152, 5);
lean_inc(x_164);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 lean_ctor_release(x_152, 2);
 lean_ctor_release(x_152, 3);
 lean_ctor_release(x_152, 4);
 lean_ctor_release(x_152, 5);
 x_165 = x_152;
} else {
 lean_dec_ref(x_152);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 6, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_160);
lean_ctor_set(x_166, 1, x_142);
lean_ctor_set(x_166, 2, x_161);
lean_ctor_set(x_166, 3, x_162);
lean_ctor_set(x_166, 4, x_163);
lean_ctor_set(x_166, 5, x_164);
if (lean_is_scalar(x_159)) {
 x_167 = lean_alloc_ctor(0, 5, 0);
} else {
 x_167 = x_159;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_155);
lean_ctor_set(x_167, 2, x_156);
lean_ctor_set(x_167, 3, x_157);
lean_ctor_set(x_167, 4, x_158);
if (lean_is_scalar(x_154)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_154;
}
lean_ctor_set(x_168, 0, x_153);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_169 = lean_ctor_get(x_150, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_150, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_172 = x_150;
} else {
 lean_dec_ref(x_150);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_169, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_169, 4);
lean_inc(x_176);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 lean_ctor_release(x_169, 4);
 x_177 = x_169;
} else {
 lean_dec_ref(x_169);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_170, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_170, 2);
lean_inc(x_179);
x_180 = lean_ctor_get(x_170, 3);
lean_inc(x_180);
x_181 = lean_ctor_get(x_170, 4);
lean_inc(x_181);
x_182 = lean_ctor_get(x_170, 5);
lean_inc(x_182);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 lean_ctor_release(x_170, 5);
 x_183 = x_170;
} else {
 lean_dec_ref(x_170);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 6, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_178);
lean_ctor_set(x_184, 1, x_142);
lean_ctor_set(x_184, 2, x_179);
lean_ctor_set(x_184, 3, x_180);
lean_ctor_set(x_184, 4, x_181);
lean_ctor_set(x_184, 5, x_182);
if (lean_is_scalar(x_177)) {
 x_185 = lean_alloc_ctor(0, 5, 0);
} else {
 x_185 = x_177;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_173);
lean_ctor_set(x_185, 2, x_174);
lean_ctor_set(x_185, 3, x_175);
lean_ctor_set(x_185, 4, x_176);
if (lean_is_scalar(x_172)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_172;
}
lean_ctor_set(x_186, 0, x_171);
lean_ctor_set(x_186, 1, x_185);
return x_186;
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
x_1 = lean_mk_string("Init.Lean.Meta.SynthInstance");
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
x_2 = lean_unsigned_to_nat(190u);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_fget(x_2, x_1);
x_11 = lean_box(0);
x_12 = x_11;
x_13 = lean_array_fset(x_2, x_1, x_12);
if (lean_obj_tag(x_10) == 4)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
x_28 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_27, x_3, x_4);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_10);
x_31 = lean_expr_update_const(x_10, x_30);
lean_ctor_set(x_28, 0, x_31);
x_14 = x_28;
goto block_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
lean_inc(x_10);
x_34 = lean_expr_update_const(x_10, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_14 = x_35;
goto block_26;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_Meta_isClassQuick___main___closed__1;
x_37 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3;
x_38 = lean_panic_fn(x_36, x_37);
lean_inc(x_3);
x_39 = lean_apply_2(x_38, x_3, x_4);
x_14 = x_39;
goto block_26;
}
block_26:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_1, x_17);
x_19 = x_15;
lean_dec(x_10);
x_20 = lean_array_fset(x_13, x_1, x_19);
lean_dec(x_1);
x_1 = x_18;
x_2 = x_20;
x_4 = x_16;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
x_11 = l_coeDecidableEq(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
if (x_11 == 0)
{
lean_dec(x_8);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_array_push(x_5, x_15);
x_4 = x_13;
x_5 = x_16;
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
x_11 = l_coeDecidableEq(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
if (x_11 == 0)
{
lean_dec(x_8);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_array_push(x_5, x_15);
x_4 = x_13;
x_5 = x_16;
goto _start;
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_Basic_10__regTraceClasses___closed__2;
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_35 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2(x_34, x_32, x_3, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_61; uint8_t x_62; 
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
x_61 = lean_ctor_get(x_37, 4);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_61, sizeof(void*)*1);
lean_dec(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = l_String_posOfAux___main___closed__2;
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3;
x_65 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_64, x_3, x_37);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_39 = x_68;
x_40 = x_67;
goto block_60;
}
else
{
uint8_t x_69; 
x_69 = 0;
x_39 = x_69;
x_40 = x_37;
goto block_60;
}
}
else
{
uint8_t x_70; 
x_70 = l_String_posOfAux___main___closed__1;
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3;
x_72 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_71, x_3, x_37);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unbox(x_73);
lean_dec(x_73);
x_39 = x_75;
x_40 = x_74;
goto block_60;
}
else
{
uint8_t x_76; 
x_76 = 0;
x_39 = x_76;
x_40 = x_37;
goto block_60;
}
}
block_60:
{
if (x_39 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
x_41 = lean_ctor_get(x_3, 2);
lean_inc(x_41);
x_42 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(x_3, x_27, x_41, x_34, x_36);
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_3);
if (lean_is_scalar(x_38)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_38;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_38);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_2);
x_45 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_48 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_36, x_34, x_47);
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3;
x_51 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_50, x_49, x_3, x_40);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_3, 2);
lean_inc(x_54);
x_55 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_3, x_27, x_54, x_34, x_36);
lean_dec(x_54);
lean_dec(x_27);
lean_dec(x_3);
lean_ctor_set(x_51, 0, x_55);
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_3, x_27, x_57, x_34, x_36);
lean_dec(x_57);
lean_dec(x_27);
lean_dec(x_3);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_35);
if (x_77 == 0)
{
return x_35;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_35, 0);
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_35);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_31);
if (x_81 == 0)
{
return x_31;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_31, 0);
x_83 = lean_ctor_get(x_31, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_31);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_5);
if (x_85 == 0)
{
return x_5;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_5, 0);
x_87 = lean_ctor_get(x_5, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_5);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
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
uint8_t l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_2, x_10);
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_10);
x_16 = lean_array_uset(x_6, x_9, x_15);
x_17 = lean_nat_dec_le(x_14, x_7);
lean_dec(x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_14, x_16);
return x_18;
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
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Expr_hash(x_2);
x_25 = lean_usize_modn(x_24, x_23);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_2, x_26);
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_21, x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_26);
x_32 = lean_array_uset(x_22, x_25, x_31);
x_33 = lean_nat_dec_le(x_30, x_23);
lean_dec(x_23);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_30, x_32);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_19 = l_PersistentArray_push___rarg(x_17, x_18);
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
x_24 = l_PersistentArray_push___rarg(x_22, x_23);
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
x_36 = l_PersistentArray_push___rarg(x_33, x_35);
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
x_54 = l_PersistentArray_push___rarg(x_51, x_53);
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
x_75 = l_PersistentArray_push___rarg(x_72, x_74);
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
lean_object* l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_44; lean_object* x_45; lean_object* x_73; uint8_t x_145; lean_object* x_146; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_14 = lean_ctor_get(x_7, 1);
lean_ctor_set(x_7, 1, x_1);
x_152 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_152, 0, x_7);
lean_ctor_set(x_152, 1, x_8);
lean_ctor_set(x_152, 2, x_9);
lean_ctor_set(x_152, 3, x_10);
lean_ctor_set(x_152, 4, x_11);
x_153 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_154, sizeof(void*)*1);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_157 = l_String_posOfAux___main___closed__2;
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_158 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_159 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_158, x_5, x_156);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_unbox(x_160);
lean_dec(x_160);
x_145 = x_162;
x_146 = x_161;
goto block_151;
}
else
{
uint8_t x_163; 
x_163 = 0;
x_145 = x_163;
x_146 = x_156;
goto block_151;
}
}
else
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_153, 1);
lean_inc(x_164);
lean_dec(x_153);
x_165 = l_String_posOfAux___main___closed__1;
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_166 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_167 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_166, x_5, x_164);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_unbox(x_168);
lean_dec(x_168);
x_145 = x_170;
x_146 = x_169;
goto block_151;
}
else
{
uint8_t x_171; 
x_171 = 0;
x_145 = x_171;
x_146 = x_164;
goto block_151;
}
}
block_43:
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
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 1);
lean_dec(x_20);
lean_ctor_set(x_18, 1, x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 2);
x_24 = lean_ctor_get(x_18, 3);
x_25 = lean_ctor_get(x_18, 4);
x_26 = lean_ctor_get(x_18, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_25);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_16, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_16);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
x_31 = lean_ctor_get(x_16, 2);
x_32 = lean_ctor_get(x_16, 3);
x_33 = lean_ctor_get(x_16, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_29, 5);
lean_inc(x_38);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 x_39 = x_29;
} else {
 lean_dec_ref(x_29);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 6, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_14);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_38);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 3, x_32);
lean_ctor_set(x_41, 4, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_15);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
block_72:
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 1);
lean_dec(x_49);
lean_ctor_set(x_47, 1, x_14);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 2);
x_53 = lean_ctor_get(x_47, 3);
x_54 = lean_ctor_get(x_47, 4);
x_55 = lean_ctor_get(x_47, 5);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_14);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set(x_56, 3, x_53);
lean_ctor_set(x_56, 4, x_54);
lean_ctor_set(x_56, 5, x_55);
lean_ctor_set(x_45, 0, x_56);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_45);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_58 = lean_ctor_get(x_45, 0);
x_59 = lean_ctor_get(x_45, 1);
x_60 = lean_ctor_get(x_45, 2);
x_61 = lean_ctor_get(x_45, 3);
x_62 = lean_ctor_get(x_45, 4);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_45);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_58, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_58, 5);
lean_inc(x_67);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 lean_ctor_release(x_58, 4);
 lean_ctor_release(x_58, 5);
 x_68 = x_58;
} else {
 lean_dec_ref(x_58);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 6, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_14);
lean_ctor_set(x_69, 2, x_64);
lean_ctor_set(x_69, 3, x_65);
lean_ctor_set(x_69, 4, x_66);
lean_ctor_set(x_69, 5, x_67);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_59);
lean_ctor_set(x_70, 2, x_60);
lean_ctor_set(x_70, 3, x_61);
lean_ctor_set(x_70, 4, x_62);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_44);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
block_144:
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_ctor_get(x_73, 2);
x_78 = lean_ctor_get(x_73, 3);
x_79 = lean_ctor_get(x_73, 4);
lean_inc(x_5);
lean_inc(x_3);
x_80 = l_Lean_Meta_inferType(x_3, x_5, x_75);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Meta_instantiateMVars(x_81, x_5, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Meta_SynthInstance_getInstances___closed__1;
x_87 = l_Lean_Meta_forallTelescopeReducing___rarg(x_84, x_86, x_5, x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_89);
lean_ctor_set(x_73, 0, x_89);
x_91 = l_Array_isEmpty___rarg(x_88);
x_92 = l_coeDecidableEq(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_73);
x_93 = lean_array_get_size(x_88);
lean_inc(x_2);
x_94 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_94, 0, x_3);
lean_ctor_set(x_94, 1, x_2);
lean_ctor_set(x_94, 2, x_90);
lean_ctor_set(x_94, 3, x_88);
lean_ctor_set(x_94, 4, x_93);
x_95 = l_Lean_mkOptionalNode___closed__2;
x_96 = lean_array_push(x_95, x_4);
x_97 = l_Array_empty___closed__1;
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_array_push(x_77, x_94);
x_100 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_79, x_2, x_98);
if (lean_is_scalar(x_12)) {
 x_101 = lean_alloc_ctor(0, 5, 0);
} else {
 x_101 = x_12;
}
lean_ctor_set(x_101, 0, x_89);
lean_ctor_set(x_101, 1, x_76);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_78);
lean_ctor_set(x_101, 4, x_100);
x_102 = lean_box(0);
x_15 = x_102;
x_16 = x_101;
goto block_43;
}
else
{
lean_object* x_103; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = lean_box(0);
x_15 = x_103;
x_16 = x_73;
goto block_43;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_ctor_get(x_87, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_87, 1);
lean_inc(x_105);
lean_dec(x_87);
lean_ctor_set(x_73, 0, x_105);
x_44 = x_104;
x_45 = x_73;
goto block_72;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = lean_ctor_get(x_80, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_80, 1);
lean_inc(x_107);
lean_dec(x_80);
lean_ctor_set(x_73, 0, x_107);
x_44 = x_106;
x_45 = x_73;
goto block_72;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_73, 0);
x_109 = lean_ctor_get(x_73, 1);
x_110 = lean_ctor_get(x_73, 2);
x_111 = lean_ctor_get(x_73, 3);
x_112 = lean_ctor_get(x_73, 4);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_73);
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
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; 
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
x_126 = l_coeDecidableEq(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_124);
x_127 = lean_array_get_size(x_121);
lean_inc(x_2);
x_128 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_128, 0, x_3);
lean_ctor_set(x_128, 1, x_2);
lean_ctor_set(x_128, 2, x_123);
lean_ctor_set(x_128, 3, x_121);
lean_ctor_set(x_128, 4, x_127);
x_129 = l_Lean_mkOptionalNode___closed__2;
x_130 = lean_array_push(x_129, x_4);
x_131 = l_Array_empty___closed__1;
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_array_push(x_110, x_128);
x_134 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_112, x_2, x_132);
if (lean_is_scalar(x_12)) {
 x_135 = lean_alloc_ctor(0, 5, 0);
} else {
 x_135 = x_12;
}
lean_ctor_set(x_135, 0, x_122);
lean_ctor_set(x_135, 1, x_109);
lean_ctor_set(x_135, 2, x_133);
lean_ctor_set(x_135, 3, x_111);
lean_ctor_set(x_135, 4, x_134);
x_136 = lean_box(0);
x_15 = x_136;
x_16 = x_135;
goto block_43;
}
else
{
lean_object* x_137; 
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
x_137 = lean_box(0);
x_15 = x_137;
x_16 = x_124;
goto block_43;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_138 = lean_ctor_get(x_120, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_120, 1);
lean_inc(x_139);
lean_dec(x_120);
x_140 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_109);
lean_ctor_set(x_140, 2, x_110);
lean_ctor_set(x_140, 3, x_111);
lean_ctor_set(x_140, 4, x_112);
x_44 = x_138;
x_45 = x_140;
goto block_72;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
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
x_44 = x_141;
x_45 = x_143;
goto block_72;
}
}
}
block_151:
{
if (x_145 == 0)
{
x_73 = x_146;
goto block_144;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_inc(x_2);
x_147 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_147, 0, x_2);
x_148 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_149 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_148, x_147, x_5, x_146);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_73 = x_150;
goto block_144;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_196; lean_object* x_197; lean_object* x_214; uint8_t x_253; lean_object* x_254; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_172 = lean_ctor_get(x_7, 0);
x_173 = lean_ctor_get(x_7, 1);
x_174 = lean_ctor_get(x_7, 2);
x_175 = lean_ctor_get(x_7, 3);
x_176 = lean_ctor_get(x_7, 4);
x_177 = lean_ctor_get(x_7, 5);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_7);
x_260 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_260, 0, x_172);
lean_ctor_set(x_260, 1, x_1);
lean_ctor_set(x_260, 2, x_174);
lean_ctor_set(x_260, 3, x_175);
lean_ctor_set(x_260, 4, x_176);
lean_ctor_set(x_260, 5, x_177);
x_261 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_8);
lean_ctor_set(x_261, 2, x_9);
lean_ctor_set(x_261, 3, x_10);
lean_ctor_set(x_261, 4, x_11);
x_262 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_261);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get_uint8(x_263, sizeof(void*)*1);
lean_dec(x_263);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
lean_dec(x_262);
x_266 = l_String_posOfAux___main___closed__2;
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_267 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_268 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_267, x_5, x_265);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_unbox(x_269);
lean_dec(x_269);
x_253 = x_271;
x_254 = x_270;
goto block_259;
}
else
{
uint8_t x_272; 
x_272 = 0;
x_253 = x_272;
x_254 = x_265;
goto block_259;
}
}
else
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_ctor_get(x_262, 1);
lean_inc(x_273);
lean_dec(x_262);
x_274 = l_String_posOfAux___main___closed__1;
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_275 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_276 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_275, x_5, x_273);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_unbox(x_277);
lean_dec(x_277);
x_253 = x_279;
x_254 = x_278;
goto block_259;
}
else
{
uint8_t x_280; 
x_280 = 0;
x_253 = x_280;
x_254 = x_273;
goto block_259;
}
}
block_195:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 4);
lean_inc(x_184);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 x_185 = x_179;
} else {
 lean_dec_ref(x_179);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_180, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_180, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_180, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_180, 4);
lean_inc(x_189);
x_190 = lean_ctor_get(x_180, 5);
lean_inc(x_190);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 lean_ctor_release(x_180, 4);
 lean_ctor_release(x_180, 5);
 x_191 = x_180;
} else {
 lean_dec_ref(x_180);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(0, 6, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_186);
lean_ctor_set(x_192, 1, x_173);
lean_ctor_set(x_192, 2, x_187);
lean_ctor_set(x_192, 3, x_188);
lean_ctor_set(x_192, 4, x_189);
lean_ctor_set(x_192, 5, x_190);
if (lean_is_scalar(x_185)) {
 x_193 = lean_alloc_ctor(0, 5, 0);
} else {
 x_193 = x_185;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_181);
lean_ctor_set(x_193, 2, x_182);
lean_ctor_set(x_193, 3, x_183);
lean_ctor_set(x_193, 4, x_184);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_178);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
block_213:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_197, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_197, 3);
lean_inc(x_201);
x_202 = lean_ctor_get(x_197, 4);
lean_inc(x_202);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 lean_ctor_release(x_197, 3);
 lean_ctor_release(x_197, 4);
 x_203 = x_197;
} else {
 lean_dec_ref(x_197);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_198, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_198, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_198, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_198, 4);
lean_inc(x_207);
x_208 = lean_ctor_get(x_198, 5);
lean_inc(x_208);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 lean_ctor_release(x_198, 4);
 lean_ctor_release(x_198, 5);
 x_209 = x_198;
} else {
 lean_dec_ref(x_198);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 6, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_204);
lean_ctor_set(x_210, 1, x_173);
lean_ctor_set(x_210, 2, x_205);
lean_ctor_set(x_210, 3, x_206);
lean_ctor_set(x_210, 4, x_207);
lean_ctor_set(x_210, 5, x_208);
if (lean_is_scalar(x_203)) {
 x_211 = lean_alloc_ctor(0, 5, 0);
} else {
 x_211 = x_203;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_199);
lean_ctor_set(x_211, 2, x_200);
lean_ctor_set(x_211, 3, x_201);
lean_ctor_set(x_211, 4, x_202);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_196);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
block_252:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 2);
lean_inc(x_217);
x_218 = lean_ctor_get(x_214, 3);
lean_inc(x_218);
x_219 = lean_ctor_get(x_214, 4);
lean_inc(x_219);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 lean_ctor_release(x_214, 3);
 lean_ctor_release(x_214, 4);
 x_220 = x_214;
} else {
 lean_dec_ref(x_214);
 x_220 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_3);
x_221 = l_Lean_Meta_inferType(x_3, x_5, x_215);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = l_Lean_Meta_instantiateMVars(x_222, x_5, x_223);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = l_Lean_Meta_SynthInstance_getInstances___closed__1;
x_228 = l_Lean_Meta_forallTelescopeReducing___rarg(x_225, x_227, x_5, x_226);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; uint8_t x_234; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_230);
if (lean_is_scalar(x_220)) {
 x_232 = lean_alloc_ctor(0, 5, 0);
} else {
 x_232 = x_220;
}
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_216);
lean_ctor_set(x_232, 2, x_217);
lean_ctor_set(x_232, 3, x_218);
lean_ctor_set(x_232, 4, x_219);
x_233 = l_Array_isEmpty___rarg(x_229);
x_234 = l_coeDecidableEq(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_232);
x_235 = lean_array_get_size(x_229);
lean_inc(x_2);
x_236 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_236, 0, x_3);
lean_ctor_set(x_236, 1, x_2);
lean_ctor_set(x_236, 2, x_231);
lean_ctor_set(x_236, 3, x_229);
lean_ctor_set(x_236, 4, x_235);
x_237 = l_Lean_mkOptionalNode___closed__2;
x_238 = lean_array_push(x_237, x_4);
x_239 = l_Array_empty___closed__1;
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_array_push(x_217, x_236);
x_242 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_219, x_2, x_240);
if (lean_is_scalar(x_12)) {
 x_243 = lean_alloc_ctor(0, 5, 0);
} else {
 x_243 = x_12;
}
lean_ctor_set(x_243, 0, x_230);
lean_ctor_set(x_243, 1, x_216);
lean_ctor_set(x_243, 2, x_241);
lean_ctor_set(x_243, 3, x_218);
lean_ctor_set(x_243, 4, x_242);
x_244 = lean_box(0);
x_178 = x_244;
x_179 = x_243;
goto block_195;
}
else
{
lean_object* x_245; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_245 = lean_box(0);
x_178 = x_245;
x_179 = x_232;
goto block_195;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_246 = lean_ctor_get(x_228, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_228, 1);
lean_inc(x_247);
lean_dec(x_228);
if (lean_is_scalar(x_220)) {
 x_248 = lean_alloc_ctor(0, 5, 0);
} else {
 x_248 = x_220;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_216);
lean_ctor_set(x_248, 2, x_217);
lean_ctor_set(x_248, 3, x_218);
lean_ctor_set(x_248, 4, x_219);
x_196 = x_246;
x_197 = x_248;
goto block_213;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_249 = lean_ctor_get(x_221, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_221, 1);
lean_inc(x_250);
lean_dec(x_221);
if (lean_is_scalar(x_220)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_220;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_216);
lean_ctor_set(x_251, 2, x_217);
lean_ctor_set(x_251, 3, x_218);
lean_ctor_set(x_251, 4, x_219);
x_196 = x_249;
x_197 = x_251;
goto block_213;
}
}
block_259:
{
if (x_253 == 0)
{
x_214 = x_254;
goto block_252;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_inc(x_2);
x_255 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_255, 0, x_2);
x_256 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_257 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_256, x_255, x_5, x_254);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec(x_257);
x_214 = x_258;
goto block_252;
}
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_AssocList_find___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(x_2, x_7);
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
x_5 = l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(x_4, x_1);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_AssocList_find___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(x_1, x_2);
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
x_2 = lean_unsigned_to_nat(229u);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_38; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
lean_ctor_set(x_6, 1, x_1);
lean_inc(x_3);
x_38 = l_Lean_Meta_inferType(x_2, x_3, x_6);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_instantiateMVars(x_39, x_3, x_40);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_43);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_44, 1);
lean_dec(x_47);
lean_ctor_set(x_44, 1, x_8);
lean_ctor_set(x_4, 0, x_44);
lean_ctor_set(x_41, 1, x_4);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 2);
x_50 = lean_ctor_get(x_44, 3);
x_51 = lean_ctor_get(x_44, 4);
x_52 = lean_ctor_get(x_44, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_8);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_51);
lean_ctor_set(x_53, 5, x_52);
lean_ctor_set(x_4, 0, x_53);
lean_ctor_set(x_41, 1, x_4);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_41, 0);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_41);
x_56 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 5);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 6, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_8);
lean_ctor_set(x_63, 2, x_58);
lean_ctor_set(x_63, 3, x_59);
lean_ctor_set(x_63, 4, x_60);
lean_ctor_set(x_63, 5, x_61);
lean_ctor_set(x_4, 0, x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_4);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
lean_dec(x_1);
x_65 = lean_ctor_get(x_38, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_38, 1);
lean_inc(x_66);
lean_dec(x_38);
lean_ctor_set(x_4, 0, x_66);
x_9 = x_65;
x_10 = x_4;
goto block_37;
}
block_37:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_dec(x_14);
lean_ctor_set(x_12, 1, x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 2);
x_18 = lean_ctor_get(x_12, 3);
x_19 = lean_ctor_get(x_12, 4);
x_20 = lean_ctor_get(x_12, 5);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set(x_21, 4, x_19);
lean_ctor_set(x_21, 5, x_20);
lean_ctor_set(x_10, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
x_25 = lean_ctor_get(x_10, 2);
x_26 = lean_ctor_get(x_10, 3);
x_27 = lean_ctor_get(x_10, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_23, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_23, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 5);
lean_inc(x_32);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 lean_ctor_release(x_23, 5);
 x_33 = x_23;
} else {
 lean_dec_ref(x_23);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_91; lean_object* x_92; 
x_67 = lean_ctor_get(x_6, 0);
x_68 = lean_ctor_get(x_6, 1);
x_69 = lean_ctor_get(x_6, 2);
x_70 = lean_ctor_get(x_6, 3);
x_71 = lean_ctor_get(x_6, 4);
x_72 = lean_ctor_get(x_6, 5);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_6);
lean_inc(x_1);
x_91 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_91, 0, x_67);
lean_ctor_set(x_91, 1, x_1);
lean_ctor_set(x_91, 2, x_69);
lean_ctor_set(x_91, 3, x_70);
lean_ctor_set(x_91, 4, x_71);
lean_ctor_set(x_91, 5, x_72);
lean_inc(x_3);
x_92 = l_Lean_Meta_inferType(x_2, x_3, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Meta_instantiateMVars(x_93, x_3, x_94);
lean_dec(x_3);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
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
x_99 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_96);
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_97, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_97, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_97, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_97, 5);
lean_inc(x_104);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 lean_ctor_release(x_97, 2);
 lean_ctor_release(x_97, 3);
 lean_ctor_release(x_97, 4);
 lean_ctor_release(x_97, 5);
 x_105 = x_97;
} else {
 lean_dec_ref(x_97);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 6, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_68);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_104);
lean_ctor_set(x_4, 0, x_106);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_4);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_3);
lean_dec(x_1);
x_108 = lean_ctor_get(x_92, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_92, 1);
lean_inc(x_109);
lean_dec(x_92);
lean_ctor_set(x_4, 0, x_109);
x_73 = x_108;
x_74 = x_4;
goto block_90;
}
block_90:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 4);
lean_inc(x_79);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 x_80 = x_74;
} else {
 lean_dec_ref(x_74);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_75, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_75, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_75, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_75, 5);
lean_inc(x_85);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 x_86 = x_75;
} else {
 lean_dec_ref(x_75);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 6, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_68);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set(x_87, 4, x_84);
lean_ctor_set(x_87, 5, x_85);
if (lean_is_scalar(x_80)) {
 x_88 = lean_alloc_ctor(0, 5, 0);
} else {
 x_88 = x_80;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_76);
lean_ctor_set(x_88, 2, x_77);
lean_ctor_set(x_88, 3, x_78);
lean_ctor_set(x_88, 4, x_79);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_73);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_140; lean_object* x_141; 
x_110 = lean_ctor_get(x_4, 0);
x_111 = lean_ctor_get(x_4, 1);
x_112 = lean_ctor_get(x_4, 2);
x_113 = lean_ctor_get(x_4, 3);
x_114 = lean_ctor_get(x_4, 4);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_4);
x_115 = lean_ctor_get(x_110, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_110, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_110, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_110, 5);
lean_inc(x_120);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 lean_ctor_release(x_110, 5);
 x_121 = x_110;
} else {
 lean_dec_ref(x_110);
 x_121 = lean_box(0);
}
lean_inc(x_1);
if (lean_is_scalar(x_121)) {
 x_140 = lean_alloc_ctor(0, 6, 0);
} else {
 x_140 = x_121;
}
lean_ctor_set(x_140, 0, x_115);
lean_ctor_set(x_140, 1, x_1);
lean_ctor_set(x_140, 2, x_117);
lean_ctor_set(x_140, 3, x_118);
lean_ctor_set(x_140, 4, x_119);
lean_ctor_set(x_140, 5, x_120);
lean_inc(x_3);
x_141 = l_Lean_Meta_inferType(x_2, x_3, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_Lean_Meta_instantiateMVars(x_142, x_3, x_143);
lean_dec(x_3);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_145);
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_146, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_146, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_146, 5);
lean_inc(x_153);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 lean_ctor_release(x_146, 5);
 x_154 = x_146;
} else {
 lean_dec_ref(x_146);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(0, 6, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_149);
lean_ctor_set(x_155, 1, x_116);
lean_ctor_set(x_155, 2, x_150);
lean_ctor_set(x_155, 3, x_151);
lean_ctor_set(x_155, 4, x_152);
lean_ctor_set(x_155, 5, x_153);
x_156 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_111);
lean_ctor_set(x_156, 2, x_112);
lean_ctor_set(x_156, 3, x_113);
lean_ctor_set(x_156, 4, x_114);
if (lean_is_scalar(x_147)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_147;
}
lean_ctor_set(x_157, 0, x_148);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_3);
lean_dec(x_1);
x_158 = lean_ctor_get(x_141, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_141, 1);
lean_inc(x_159);
lean_dec(x_141);
x_160 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_111);
lean_ctor_set(x_160, 2, x_112);
lean_ctor_set(x_160, 3, x_113);
lean_ctor_set(x_160, 4, x_114);
x_122 = x_158;
x_123 = x_160;
goto block_139;
}
block_139:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 4);
lean_inc(x_128);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 x_129 = x_123;
} else {
 lean_dec_ref(x_123);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_124, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_124, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_124, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_124, 4);
lean_inc(x_133);
x_134 = lean_ctor_get(x_124, 5);
lean_inc(x_134);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 x_135 = x_124;
} else {
 lean_dec_ref(x_124);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 6, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_130);
lean_ctor_set(x_136, 1, x_116);
lean_ctor_set(x_136, 2, x_131);
lean_ctor_set(x_136, 3, x_132);
lean_ctor_set(x_136, 4, x_133);
lean_ctor_set(x_136, 5, x_134);
if (lean_is_scalar(x_129)) {
 x_137 = lean_alloc_ctor(0, 5, 0);
} else {
 x_137 = x_129;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_125);
lean_ctor_set(x_137, 2, x_126);
lean_ctor_set(x_137, 3, x_127);
lean_ctor_set(x_137, 4, x_128);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_122);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
if (lean_obj_tag(x_8) == 7)
{
lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_8, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_37 = lean_array_get_size(x_4);
x_38 = lean_expr_instantiate_rev_range(x_34, x_5, x_37, x_4);
lean_dec(x_37);
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_3);
x_39 = l_Lean_Meta_mkForall(x_3, x_38, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Lean_Meta_mkFreshExprMVarAt(x_1, x_2, x_40, x_42, x_43, x_9, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(0u);
lean_inc(x_45);
x_48 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_3, x_3, x_47, x_45);
lean_inc(x_48);
x_49 = l_Lean_mkApp(x_7, x_48);
x_50 = (uint8_t)((x_36 << 24) >> 61);
x_51 = l_Lean_BinderInfo_isInstImplicit(x_50);
x_52 = l_coeDecidableEq(x_51);
x_53 = lean_array_push(x_4, x_48);
if (x_52 == 0)
{
lean_dec(x_45);
x_4 = x_53;
x_7 = x_49;
x_8 = x_35;
x_10 = x_46;
goto _start;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_6);
x_4 = x_53;
x_6 = x_55;
x_7 = x_49;
x_8 = x_35;
x_10 = x_46;
goto _start;
}
}
else
{
uint8_t x_57; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_39);
if (x_57 == 0)
{
return x_39;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
x_61 = lean_box(0);
x_11 = x_61;
goto block_33;
}
block_33:
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
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Expr_isForall(x_16);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_7);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_14, 0, x_20);
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
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = l_Lean_Expr_isForall(x_22);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_7);
lean_ctor_set(x_26, 2, x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
else
{
x_5 = x_12;
x_8 = x_22;
x_10 = x_23;
goto _start;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_SynthInstance_1__getSubgoalsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_13 = l___private_Init_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(x_1, x_2, x_3, x_11, x_12, x_10, x_4, x_8, x_5, x_9);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_142; lean_object* x_143; lean_object* x_153; uint8_t x_154; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_15);
lean_dec(x_10);
x_153 = lean_ctor_get(x_11, 4);
lean_inc(x_153);
x_154 = lean_ctor_get_uint8(x_153, sizeof(void*)*1);
lean_dec(x_153);
if (x_154 == 0)
{
uint8_t x_155; 
x_155 = l_String_posOfAux___main___closed__2;
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_156 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_157 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_156, x_7, x_11);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_unbox(x_158);
lean_dec(x_158);
x_142 = x_160;
x_143 = x_159;
goto block_152;
}
else
{
uint8_t x_161; 
x_161 = 0;
x_142 = x_161;
x_143 = x_11;
goto block_152;
}
}
else
{
uint8_t x_162; 
x_162 = l_String_posOfAux___main___closed__1;
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_163 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_164 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_163, x_7, x_11);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_unbox(x_165);
lean_dec(x_165);
x_142 = x_167;
x_143 = x_166;
goto block_152;
}
else
{
uint8_t x_168; 
x_168 = 0;
x_142 = x_168;
x_143 = x_11;
goto block_152;
}
}
block_141:
{
uint8_t x_17; lean_object* x_18; lean_object* x_31; 
lean_inc(x_7);
x_31 = l_Lean_Meta_isExprDefEq(x_6, x_15, x_7, x_16);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_34, 4);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_String_posOfAux___main___closed__2;
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_39 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_38, x_7, x_34);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unbox(x_40);
lean_dec(x_40);
x_17 = x_42;
x_18 = x_41;
goto block_30;
}
else
{
uint8_t x_43; 
x_43 = 0;
x_17 = x_43;
x_18 = x_34;
goto block_30;
}
}
else
{
uint8_t x_44; 
x_44 = l_String_posOfAux___main___closed__1;
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_46 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_45, x_7, x_34);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
x_17 = x_49;
x_18 = x_48;
goto block_30;
}
else
{
uint8_t x_50; 
x_50 = 0;
x_17 = x_50;
x_18 = x_34;
goto block_30;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_12);
x_51 = lean_ctor_get(x_31, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_52 = x_31;
} else {
 lean_dec_ref(x_31);
 x_52 = lean_box(0);
}
lean_inc(x_7);
x_53 = l_Lean_Meta_mkLambda(x_5, x_14, x_7, x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_71; lean_object* x_72; lean_object* x_92; 
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
lean_inc(x_7);
x_92 = l_Lean_Meta_isExprDefEq(x_4, x_54, x_7, x_55);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_52);
lean_dec(x_13);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_ctor_get(x_95, 4);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_96, sizeof(void*)*1);
lean_dec(x_96);
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = l_String_posOfAux___main___closed__2;
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_100 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_99, x_7, x_95);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_unbox(x_101);
lean_dec(x_101);
x_57 = x_103;
x_58 = x_102;
goto block_70;
}
else
{
uint8_t x_104; 
x_104 = 0;
x_57 = x_104;
x_58 = x_95;
goto block_70;
}
}
else
{
uint8_t x_105; 
x_105 = l_String_posOfAux___main___closed__1;
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_107 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_106, x_7, x_95);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_unbox(x_108);
lean_dec(x_108);
x_57 = x_110;
x_58 = x_109;
goto block_70;
}
else
{
uint8_t x_111; 
x_111 = 0;
x_57 = x_111;
x_58 = x_95;
goto block_70;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_dec(x_56);
x_112 = lean_ctor_get(x_92, 1);
lean_inc(x_112);
lean_dec(x_92);
x_113 = lean_ctor_get(x_112, 4);
lean_inc(x_113);
x_114 = lean_ctor_get_uint8(x_113, sizeof(void*)*1);
lean_dec(x_113);
if (x_114 == 0)
{
uint8_t x_115; 
x_115 = l_String_posOfAux___main___closed__2;
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_117 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_116, x_7, x_112);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_unbox(x_118);
lean_dec(x_118);
x_71 = x_120;
x_72 = x_119;
goto block_91;
}
else
{
uint8_t x_121; 
x_121 = 0;
x_71 = x_121;
x_72 = x_112;
goto block_91;
}
}
else
{
uint8_t x_122; 
x_122 = l_String_posOfAux___main___closed__1;
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_123 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_124 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_123, x_7, x_112);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_unbox(x_125);
lean_dec(x_125);
x_71 = x_127;
x_72 = x_126;
goto block_91;
}
else
{
uint8_t x_128; 
x_128 = 0;
x_71 = x_128;
x_72 = x_112;
goto block_91;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_56);
lean_dec(x_52);
lean_dec(x_13);
lean_dec(x_7);
x_129 = !lean_is_exclusive(x_92);
if (x_129 == 0)
{
return x_92;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_92, 0);
x_131 = lean_ctor_get(x_92, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_92);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
block_70:
{
if (x_57 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_7);
x_59 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_56);
x_61 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_62 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5;
x_63 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_61, x_62, x_7, x_58);
lean_dec(x_7);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_63, 0, x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
block_91:
{
if (x_71 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_7);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_13);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_52)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_52;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_52);
x_77 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_78 = l_Lean_Meta_isLevelDefEq___closed__9;
x_79 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_77, x_78, x_7, x_72);
lean_dec(x_7);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_79, 1);
x_82 = lean_ctor_get(x_79, 0);
lean_dec(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_13);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_79, 0, x_85);
return x_79;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_13);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
return x_90;
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_52);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_53);
if (x_133 == 0)
{
return x_53;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_53, 0);
x_135 = lean_ctor_get(x_53, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_53);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_137 = !lean_is_exclusive(x_31);
if (x_137 == 0)
{
return x_31;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_31, 0);
x_139 = lean_ctor_get(x_31, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_31);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
block_30:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = lean_box(0);
if (lean_is_scalar(x_12)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_12;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_12);
x_21 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_22 = l_Lean_Meta_isLevelDefEq___closed__6;
x_23 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_21, x_22, x_7, x_18);
lean_dec(x_7);
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
}
}
block_152:
{
if (x_142 == 0)
{
x_16 = x_143;
goto block_141;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_inc(x_6);
x_144 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_144, 0, x_6);
x_145 = l_Lean_Meta_Exception_toTraceMessageData___closed__51;
x_146 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
lean_inc(x_15);
x_147 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_147, 0, x_15);
x_148 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_150 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_149, x_148, x_7, x_143);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_16 = x_151;
goto block_141;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_9);
if (x_169 == 0)
{
return x_9;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_9, 0);
x_171 = lean_ctor_get(x_9, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_9);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
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
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(lean_object* x_1) {
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
x_16 = l_PersistentArray_empty___closed__3;
lean_ctor_set(x_5, 0, x_16);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_dec(x_5);
x_18 = l_PersistentArray_empty___closed__3;
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
x_27 = l_PersistentArray_empty___closed__3;
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
x_42 = l_PersistentArray_empty___closed__3;
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
x_61 = l_PersistentArray_empty___closed__3;
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
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_13 = l_PersistentArray_toArray___rarg(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_PersistentArray_push___rarg(x_1, x_15);
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
x_21 = l_PersistentArray_toArray___rarg(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_PersistentArray_push___rarg(x_1, x_23);
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
x_36 = l_PersistentArray_toArray___rarg(x_34);
lean_dec(x_34);
x_37 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_PersistentArray_push___rarg(x_1, x_38);
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
x_57 = l_PersistentArray_toArray___rarg(x_55);
lean_dec(x_55);
x_58 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_2);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_PersistentArray_push___rarg(x_1, x_59);
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
uint8_t x_6; lean_object* x_7; lean_object* x_545; lean_object* x_546; uint8_t x_547; 
x_545 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_5);
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get_uint8(x_546, sizeof(void*)*1);
lean_dec(x_546);
if (x_547 == 0)
{
lean_object* x_548; uint8_t x_549; 
x_548 = lean_ctor_get(x_545, 1);
lean_inc(x_548);
lean_dec(x_545);
x_549 = l_String_posOfAux___main___closed__2;
if (x_549 == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; 
x_550 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_551 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_550, x_4, x_548);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
x_554 = lean_unbox(x_552);
lean_dec(x_552);
x_6 = x_554;
x_7 = x_553;
goto block_544;
}
else
{
uint8_t x_555; 
x_555 = 0;
x_6 = x_555;
x_7 = x_548;
goto block_544;
}
}
else
{
lean_object* x_556; uint8_t x_557; 
x_556 = lean_ctor_get(x_545, 1);
lean_inc(x_556);
lean_dec(x_545);
x_557 = l_String_posOfAux___main___closed__1;
if (x_557 == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; 
x_558 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_559 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_558, x_4, x_556);
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_562 = lean_unbox(x_560);
lean_dec(x_560);
x_6 = x_562;
x_7 = x_561;
goto block_544;
}
else
{
uint8_t x_563; 
x_563 = 0;
x_6 = x_563;
x_7 = x_556;
goto block_544;
}
}
block_544:
{
uint8_t x_8; 
if (x_6 == 0)
{
uint8_t x_542; 
x_542 = 1;
x_8 = x_542;
goto block_541;
}
else
{
uint8_t x_543; 
x_543 = 0;
x_8 = x_543;
goto block_541;
}
block_541:
{
uint8_t x_9; 
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 1);
lean_ctor_set(x_12, 1, x_1);
lean_inc(x_4);
x_18 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_dec(x_22);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_11, 0, x_19);
x_23 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_24 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_13, x_23, x_4, x_11);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 2);
x_31 = lean_ctor_get(x_19, 3);
x_32 = lean_ctor_get(x_19, 4);
x_33 = lean_ctor_get(x_19, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_17);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_31);
lean_ctor_set(x_34, 4, x_32);
lean_ctor_set(x_34, 5, x_33);
lean_ctor_set(x_11, 0, x_34);
x_35 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_36 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_13, x_35, x_4, x_11);
lean_dec(x_4);
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
lean_ctor_set(x_39, 0, x_20);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
lean_dec(x_18);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_40, 1);
lean_dec(x_43);
lean_ctor_set(x_40, 1, x_17);
lean_ctor_set(x_11, 0, x_40);
x_44 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_45 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_13, x_44, x_4, x_11);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_41);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_40, 0);
x_51 = lean_ctor_get(x_40, 2);
x_52 = lean_ctor_get(x_40, 3);
x_53 = lean_ctor_get(x_40, 4);
x_54 = lean_ctor_get(x_40, 5);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_40);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_17);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set(x_55, 3, x_52);
lean_ctor_set(x_55, 4, x_53);
lean_ctor_set(x_55, 5, x_54);
lean_ctor_set(x_11, 0, x_55);
x_56 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_57 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_13, x_56, x_4, x_11);
lean_dec(x_4);
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
lean_ctor_set(x_60, 0, x_41);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_12, 0);
x_62 = lean_ctor_get(x_12, 1);
x_63 = lean_ctor_get(x_12, 2);
x_64 = lean_ctor_get(x_12, 3);
x_65 = lean_ctor_get(x_12, 4);
x_66 = lean_ctor_get(x_12, 5);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_12);
x_67 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_1);
lean_ctor_set(x_67, 2, x_63);
lean_ctor_set(x_67, 3, x_64);
lean_ctor_set(x_67, 4, x_65);
lean_ctor_set(x_67, 5, x_66);
lean_inc(x_4);
x_68 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 4);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 5);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 lean_ctor_release(x_69, 3);
 lean_ctor_release(x_69, 4);
 lean_ctor_release(x_69, 5);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 6, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_62);
lean_ctor_set(x_77, 2, x_72);
lean_ctor_set(x_77, 3, x_73);
lean_ctor_set(x_77, 4, x_74);
lean_ctor_set(x_77, 5, x_75);
lean_ctor_set(x_11, 0, x_77);
x_78 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_79 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_13, x_78, x_4, x_11);
lean_dec(x_4);
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
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_83 = lean_ctor_get(x_68, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_68, 0);
lean_inc(x_84);
lean_dec(x_68);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_83, 4);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 5);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 lean_ctor_release(x_83, 3);
 lean_ctor_release(x_83, 4);
 lean_ctor_release(x_83, 5);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 6, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_62);
lean_ctor_set(x_91, 2, x_86);
lean_ctor_set(x_91, 3, x_87);
lean_ctor_set(x_91, 4, x_88);
lean_ctor_set(x_91, 5, x_89);
lean_ctor_set(x_11, 0, x_91);
x_92 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_93 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_13, x_92, x_4, x_11);
lean_dec(x_4);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
 lean_ctor_set_tag(x_96, 1);
}
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_97 = lean_ctor_get(x_11, 1);
x_98 = lean_ctor_get(x_11, 2);
x_99 = lean_ctor_get(x_11, 3);
x_100 = lean_ctor_get(x_11, 4);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_11);
x_101 = lean_ctor_get(x_12, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_12, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_12, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_12, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_12, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_12, 5);
lean_inc(x_106);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 lean_ctor_release(x_12, 5);
 x_107 = x_12;
} else {
 lean_dec_ref(x_12);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 6, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_1);
lean_ctor_set(x_108, 2, x_103);
lean_ctor_set(x_108, 3, x_104);
lean_ctor_set(x_108, 4, x_105);
lean_ctor_set(x_108, 5, x_106);
lean_inc(x_4);
x_109 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 4);
lean_inc(x_115);
x_116 = lean_ctor_get(x_110, 5);
lean_inc(x_116);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 lean_ctor_release(x_110, 5);
 x_117 = x_110;
} else {
 lean_dec_ref(x_110);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 6, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_102);
lean_ctor_set(x_118, 2, x_113);
lean_ctor_set(x_118, 3, x_114);
lean_ctor_set(x_118, 4, x_115);
lean_ctor_set(x_118, 5, x_116);
x_119 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_97);
lean_ctor_set(x_119, 2, x_98);
lean_ctor_set(x_119, 3, x_99);
lean_ctor_set(x_119, 4, x_100);
x_120 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_121 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_13, x_120, x_4, x_119);
lean_dec(x_4);
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
lean_ctor_set(x_124, 0, x_111);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_125 = lean_ctor_get(x_109, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_109, 0);
lean_inc(x_126);
lean_dec(x_109);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_125, 4);
lean_inc(x_130);
x_131 = lean_ctor_get(x_125, 5);
lean_inc(x_131);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 lean_ctor_release(x_125, 5);
 x_132 = x_125;
} else {
 lean_dec_ref(x_125);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 6, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_102);
lean_ctor_set(x_133, 2, x_128);
lean_ctor_set(x_133, 3, x_129);
lean_ctor_set(x_133, 4, x_130);
lean_ctor_set(x_133, 5, x_131);
x_134 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_97);
lean_ctor_set(x_134, 2, x_98);
lean_ctor_set(x_134, 3, x_99);
lean_ctor_set(x_134, 4, x_100);
x_135 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_136 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_13, x_135, x_4, x_134);
lean_dec(x_4);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
 lean_ctor_set_tag(x_139, 1);
}
lean_ctor_set(x_139, 0, x_126);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
x_140 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_7);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 4);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
lean_dec(x_141);
x_146 = !lean_is_exclusive(x_142);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_142, 0);
lean_dec(x_147);
x_148 = !lean_is_exclusive(x_143);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = lean_ctor_get(x_143, 1);
x_150 = lean_ctor_get(x_143, 4);
lean_dec(x_150);
x_151 = !lean_is_exclusive(x_144);
if (x_151 == 0)
{
uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_213; 
x_152 = 0;
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_152);
lean_ctor_set(x_143, 1, x_1);
x_213 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_143);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
lean_dec(x_213);
x_216 = !lean_is_exclusive(x_214);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = lean_ctor_get(x_214, 1);
lean_dec(x_217);
lean_ctor_set(x_214, 1, x_149);
lean_ctor_set(x_142, 0, x_214);
x_218 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_142);
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_220 = lean_ctor_get(x_218, 1);
x_221 = lean_ctor_get(x_218, 0);
lean_dec(x_221);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_222, 4);
lean_inc(x_223);
x_224 = !lean_is_exclusive(x_220);
if (x_224 == 0)
{
lean_object* x_225; uint8_t x_226; 
x_225 = lean_ctor_get(x_220, 0);
lean_dec(x_225);
x_226 = !lean_is_exclusive(x_222);
if (x_226 == 0)
{
lean_object* x_227; uint8_t x_228; 
x_227 = lean_ctor_get(x_222, 4);
lean_dec(x_227);
x_228 = !lean_is_exclusive(x_223);
if (x_228 == 0)
{
lean_ctor_set_uint8(x_223, sizeof(void*)*1, x_145);
lean_ctor_set(x_218, 0, x_215);
return x_218;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_223, 0);
lean_inc(x_229);
lean_dec(x_223);
x_230 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set_uint8(x_230, sizeof(void*)*1, x_145);
lean_ctor_set(x_222, 4, x_230);
lean_ctor_set(x_218, 0, x_215);
return x_218;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_231 = lean_ctor_get(x_222, 0);
x_232 = lean_ctor_get(x_222, 1);
x_233 = lean_ctor_get(x_222, 2);
x_234 = lean_ctor_get(x_222, 3);
x_235 = lean_ctor_get(x_222, 5);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_222);
x_236 = lean_ctor_get(x_223, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_237 = x_223;
} else {
 lean_dec_ref(x_223);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(0, 1, 1);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*1, x_145);
x_239 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_239, 0, x_231);
lean_ctor_set(x_239, 1, x_232);
lean_ctor_set(x_239, 2, x_233);
lean_ctor_set(x_239, 3, x_234);
lean_ctor_set(x_239, 4, x_238);
lean_ctor_set(x_239, 5, x_235);
lean_ctor_set(x_220, 0, x_239);
lean_ctor_set(x_218, 0, x_215);
return x_218;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_240 = lean_ctor_get(x_220, 1);
x_241 = lean_ctor_get(x_220, 2);
x_242 = lean_ctor_get(x_220, 3);
x_243 = lean_ctor_get(x_220, 4);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_220);
x_244 = lean_ctor_get(x_222, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_222, 1);
lean_inc(x_245);
x_246 = lean_ctor_get(x_222, 2);
lean_inc(x_246);
x_247 = lean_ctor_get(x_222, 3);
lean_inc(x_247);
x_248 = lean_ctor_get(x_222, 5);
lean_inc(x_248);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 lean_ctor_release(x_222, 2);
 lean_ctor_release(x_222, 3);
 lean_ctor_release(x_222, 4);
 lean_ctor_release(x_222, 5);
 x_249 = x_222;
} else {
 lean_dec_ref(x_222);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_223, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_251 = x_223;
} else {
 lean_dec_ref(x_223);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(0, 1, 1);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set_uint8(x_252, sizeof(void*)*1, x_145);
if (lean_is_scalar(x_249)) {
 x_253 = lean_alloc_ctor(0, 6, 0);
} else {
 x_253 = x_249;
}
lean_ctor_set(x_253, 0, x_244);
lean_ctor_set(x_253, 1, x_245);
lean_ctor_set(x_253, 2, x_246);
lean_ctor_set(x_253, 3, x_247);
lean_ctor_set(x_253, 4, x_252);
lean_ctor_set(x_253, 5, x_248);
x_254 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_240);
lean_ctor_set(x_254, 2, x_241);
lean_ctor_set(x_254, 3, x_242);
lean_ctor_set(x_254, 4, x_243);
lean_ctor_set(x_218, 1, x_254);
lean_ctor_set(x_218, 0, x_215);
return x_218;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_255 = lean_ctor_get(x_218, 1);
lean_inc(x_255);
lean_dec(x_218);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_256, 4);
lean_inc(x_257);
x_258 = lean_ctor_get(x_255, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_255, 2);
lean_inc(x_259);
x_260 = lean_ctor_get(x_255, 3);
lean_inc(x_260);
x_261 = lean_ctor_get(x_255, 4);
lean_inc(x_261);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 lean_ctor_release(x_255, 3);
 lean_ctor_release(x_255, 4);
 x_262 = x_255;
} else {
 lean_dec_ref(x_255);
 x_262 = lean_box(0);
}
x_263 = lean_ctor_get(x_256, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_256, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_256, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_256, 3);
lean_inc(x_266);
x_267 = lean_ctor_get(x_256, 5);
lean_inc(x_267);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 lean_ctor_release(x_256, 3);
 lean_ctor_release(x_256, 4);
 lean_ctor_release(x_256, 5);
 x_268 = x_256;
} else {
 lean_dec_ref(x_256);
 x_268 = lean_box(0);
}
x_269 = lean_ctor_get(x_257, 0);
lean_inc(x_269);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_270 = x_257;
} else {
 lean_dec_ref(x_257);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(0, 1, 1);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set_uint8(x_271, sizeof(void*)*1, x_145);
if (lean_is_scalar(x_268)) {
 x_272 = lean_alloc_ctor(0, 6, 0);
} else {
 x_272 = x_268;
}
lean_ctor_set(x_272, 0, x_263);
lean_ctor_set(x_272, 1, x_264);
lean_ctor_set(x_272, 2, x_265);
lean_ctor_set(x_272, 3, x_266);
lean_ctor_set(x_272, 4, x_271);
lean_ctor_set(x_272, 5, x_267);
if (lean_is_scalar(x_262)) {
 x_273 = lean_alloc_ctor(0, 5, 0);
} else {
 x_273 = x_262;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_258);
lean_ctor_set(x_273, 2, x_259);
lean_ctor_set(x_273, 3, x_260);
lean_ctor_set(x_273, 4, x_261);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_215);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_275 = lean_ctor_get(x_214, 0);
x_276 = lean_ctor_get(x_214, 2);
x_277 = lean_ctor_get(x_214, 3);
x_278 = lean_ctor_get(x_214, 4);
x_279 = lean_ctor_get(x_214, 5);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_214);
x_280 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_280, 0, x_275);
lean_ctor_set(x_280, 1, x_149);
lean_ctor_set(x_280, 2, x_276);
lean_ctor_set(x_280, 3, x_277);
lean_ctor_set(x_280, 4, x_278);
lean_ctor_set(x_280, 5, x_279);
lean_ctor_set(x_142, 0, x_280);
x_281 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_142);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_283 = x_281;
} else {
 lean_dec_ref(x_281);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_282, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_284, 4);
lean_inc(x_285);
x_286 = lean_ctor_get(x_282, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_282, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_282, 3);
lean_inc(x_288);
x_289 = lean_ctor_get(x_282, 4);
lean_inc(x_289);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 lean_ctor_release(x_282, 2);
 lean_ctor_release(x_282, 3);
 lean_ctor_release(x_282, 4);
 x_290 = x_282;
} else {
 lean_dec_ref(x_282);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_284, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_284, 1);
lean_inc(x_292);
x_293 = lean_ctor_get(x_284, 2);
lean_inc(x_293);
x_294 = lean_ctor_get(x_284, 3);
lean_inc(x_294);
x_295 = lean_ctor_get(x_284, 5);
lean_inc(x_295);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 lean_ctor_release(x_284, 2);
 lean_ctor_release(x_284, 3);
 lean_ctor_release(x_284, 4);
 lean_ctor_release(x_284, 5);
 x_296 = x_284;
} else {
 lean_dec_ref(x_284);
 x_296 = lean_box(0);
}
x_297 = lean_ctor_get(x_285, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_298 = x_285;
} else {
 lean_dec_ref(x_285);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(0, 1, 1);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*1, x_145);
if (lean_is_scalar(x_296)) {
 x_300 = lean_alloc_ctor(0, 6, 0);
} else {
 x_300 = x_296;
}
lean_ctor_set(x_300, 0, x_291);
lean_ctor_set(x_300, 1, x_292);
lean_ctor_set(x_300, 2, x_293);
lean_ctor_set(x_300, 3, x_294);
lean_ctor_set(x_300, 4, x_299);
lean_ctor_set(x_300, 5, x_295);
if (lean_is_scalar(x_290)) {
 x_301 = lean_alloc_ctor(0, 5, 0);
} else {
 x_301 = x_290;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_286);
lean_ctor_set(x_301, 2, x_287);
lean_ctor_set(x_301, 3, x_288);
lean_ctor_set(x_301, 4, x_289);
if (lean_is_scalar(x_283)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_283;
}
lean_ctor_set(x_302, 0, x_215);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_303 = lean_ctor_get(x_213, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_213, 0);
lean_inc(x_304);
lean_dec(x_213);
x_305 = !lean_is_exclusive(x_303);
if (x_305 == 0)
{
lean_object* x_306; 
x_306 = lean_ctor_get(x_303, 1);
lean_dec(x_306);
lean_ctor_set(x_303, 1, x_149);
lean_ctor_set(x_142, 0, x_303);
x_153 = x_304;
x_154 = x_142;
goto block_212;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_307 = lean_ctor_get(x_303, 0);
x_308 = lean_ctor_get(x_303, 2);
x_309 = lean_ctor_get(x_303, 3);
x_310 = lean_ctor_get(x_303, 4);
x_311 = lean_ctor_get(x_303, 5);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_303);
x_312 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_312, 0, x_307);
lean_ctor_set(x_312, 1, x_149);
lean_ctor_set(x_312, 2, x_308);
lean_ctor_set(x_312, 3, x_309);
lean_ctor_set(x_312, 4, x_310);
lean_ctor_set(x_312, 5, x_311);
lean_ctor_set(x_142, 0, x_312);
x_153 = x_304;
x_154 = x_142;
goto block_212;
}
}
block_212:
{
lean_object* x_155; uint8_t x_156; 
x_155 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_154);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_155, 1);
x_158 = lean_ctor_get(x_155, 0);
lean_dec(x_158);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_159, 4);
lean_inc(x_160);
x_161 = !lean_is_exclusive(x_157);
if (x_161 == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_ctor_get(x_157, 0);
lean_dec(x_162);
x_163 = !lean_is_exclusive(x_159);
if (x_163 == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_159, 4);
lean_dec(x_164);
x_165 = !lean_is_exclusive(x_160);
if (x_165 == 0)
{
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_145);
lean_ctor_set_tag(x_155, 1);
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_160, 0);
lean_inc(x_166);
lean_dec(x_160);
x_167 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set_uint8(x_167, sizeof(void*)*1, x_145);
lean_ctor_set(x_159, 4, x_167);
lean_ctor_set_tag(x_155, 1);
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_168 = lean_ctor_get(x_159, 0);
x_169 = lean_ctor_get(x_159, 1);
x_170 = lean_ctor_get(x_159, 2);
x_171 = lean_ctor_get(x_159, 3);
x_172 = lean_ctor_get(x_159, 5);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_159);
x_173 = lean_ctor_get(x_160, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_174 = x_160;
} else {
 lean_dec_ref(x_160);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(0, 1, 1);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_145);
x_176 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_176, 2, x_170);
lean_ctor_set(x_176, 3, x_171);
lean_ctor_set(x_176, 4, x_175);
lean_ctor_set(x_176, 5, x_172);
lean_ctor_set(x_157, 0, x_176);
lean_ctor_set_tag(x_155, 1);
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_177 = lean_ctor_get(x_157, 1);
x_178 = lean_ctor_get(x_157, 2);
x_179 = lean_ctor_get(x_157, 3);
x_180 = lean_ctor_get(x_157, 4);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_157);
x_181 = lean_ctor_get(x_159, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_159, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_159, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_159, 3);
lean_inc(x_184);
x_185 = lean_ctor_get(x_159, 5);
lean_inc(x_185);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 lean_ctor_release(x_159, 2);
 lean_ctor_release(x_159, 3);
 lean_ctor_release(x_159, 4);
 lean_ctor_release(x_159, 5);
 x_186 = x_159;
} else {
 lean_dec_ref(x_159);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_160, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_188 = x_160;
} else {
 lean_dec_ref(x_160);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(0, 1, 1);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set_uint8(x_189, sizeof(void*)*1, x_145);
if (lean_is_scalar(x_186)) {
 x_190 = lean_alloc_ctor(0, 6, 0);
} else {
 x_190 = x_186;
}
lean_ctor_set(x_190, 0, x_181);
lean_ctor_set(x_190, 1, x_182);
lean_ctor_set(x_190, 2, x_183);
lean_ctor_set(x_190, 3, x_184);
lean_ctor_set(x_190, 4, x_189);
lean_ctor_set(x_190, 5, x_185);
x_191 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_177);
lean_ctor_set(x_191, 2, x_178);
lean_ctor_set(x_191, 3, x_179);
lean_ctor_set(x_191, 4, x_180);
lean_ctor_set_tag(x_155, 1);
lean_ctor_set(x_155, 1, x_191);
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_192 = lean_ctor_get(x_155, 1);
lean_inc(x_192);
lean_dec(x_155);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_193, 4);
lean_inc(x_194);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_192, 3);
lean_inc(x_197);
x_198 = lean_ctor_get(x_192, 4);
lean_inc(x_198);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 x_199 = x_192;
} else {
 lean_dec_ref(x_192);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_193, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_193, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 2);
lean_inc(x_202);
x_203 = lean_ctor_get(x_193, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_193, 5);
lean_inc(x_204);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 lean_ctor_release(x_193, 4);
 lean_ctor_release(x_193, 5);
 x_205 = x_193;
} else {
 lean_dec_ref(x_193);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_194, 0);
lean_inc(x_206);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_207 = x_194;
} else {
 lean_dec_ref(x_194);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 1, 1);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set_uint8(x_208, sizeof(void*)*1, x_145);
if (lean_is_scalar(x_205)) {
 x_209 = lean_alloc_ctor(0, 6, 0);
} else {
 x_209 = x_205;
}
lean_ctor_set(x_209, 0, x_200);
lean_ctor_set(x_209, 1, x_201);
lean_ctor_set(x_209, 2, x_202);
lean_ctor_set(x_209, 3, x_203);
lean_ctor_set(x_209, 4, x_208);
lean_ctor_set(x_209, 5, x_204);
if (lean_is_scalar(x_199)) {
 x_210 = lean_alloc_ctor(0, 5, 0);
} else {
 x_210 = x_199;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_195);
lean_ctor_set(x_210, 2, x_196);
lean_ctor_set(x_210, 3, x_197);
lean_ctor_set(x_210, 4, x_198);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_153);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_341; 
x_313 = lean_ctor_get(x_144, 0);
lean_inc(x_313);
lean_dec(x_144);
x_314 = 0;
x_315 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set_uint8(x_315, sizeof(void*)*1, x_314);
lean_ctor_set(x_143, 4, x_315);
lean_ctor_set(x_143, 1, x_1);
x_341 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_143);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_342 = lean_ctor_get(x_341, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 0);
lean_inc(x_343);
lean_dec(x_341);
x_344 = lean_ctor_get(x_342, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_342, 2);
lean_inc(x_345);
x_346 = lean_ctor_get(x_342, 3);
lean_inc(x_346);
x_347 = lean_ctor_get(x_342, 4);
lean_inc(x_347);
x_348 = lean_ctor_get(x_342, 5);
lean_inc(x_348);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 lean_ctor_release(x_342, 3);
 lean_ctor_release(x_342, 4);
 lean_ctor_release(x_342, 5);
 x_349 = x_342;
} else {
 lean_dec_ref(x_342);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(0, 6, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_344);
lean_ctor_set(x_350, 1, x_149);
lean_ctor_set(x_350, 2, x_345);
lean_ctor_set(x_350, 3, x_346);
lean_ctor_set(x_350, 4, x_347);
lean_ctor_set(x_350, 5, x_348);
lean_ctor_set(x_142, 0, x_350);
x_351 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_142);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_353 = x_351;
} else {
 lean_dec_ref(x_351);
 x_353 = lean_box(0);
}
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_354, 4);
lean_inc(x_355);
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_352, 2);
lean_inc(x_357);
x_358 = lean_ctor_get(x_352, 3);
lean_inc(x_358);
x_359 = lean_ctor_get(x_352, 4);
lean_inc(x_359);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 lean_ctor_release(x_352, 3);
 lean_ctor_release(x_352, 4);
 x_360 = x_352;
} else {
 lean_dec_ref(x_352);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_354, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_354, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_354, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_354, 3);
lean_inc(x_364);
x_365 = lean_ctor_get(x_354, 5);
lean_inc(x_365);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 lean_ctor_release(x_354, 4);
 lean_ctor_release(x_354, 5);
 x_366 = x_354;
} else {
 lean_dec_ref(x_354);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_355, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 x_368 = x_355;
} else {
 lean_dec_ref(x_355);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(0, 1, 1);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set_uint8(x_369, sizeof(void*)*1, x_145);
if (lean_is_scalar(x_366)) {
 x_370 = lean_alloc_ctor(0, 6, 0);
} else {
 x_370 = x_366;
}
lean_ctor_set(x_370, 0, x_361);
lean_ctor_set(x_370, 1, x_362);
lean_ctor_set(x_370, 2, x_363);
lean_ctor_set(x_370, 3, x_364);
lean_ctor_set(x_370, 4, x_369);
lean_ctor_set(x_370, 5, x_365);
if (lean_is_scalar(x_360)) {
 x_371 = lean_alloc_ctor(0, 5, 0);
} else {
 x_371 = x_360;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_356);
lean_ctor_set(x_371, 2, x_357);
lean_ctor_set(x_371, 3, x_358);
lean_ctor_set(x_371, 4, x_359);
if (lean_is_scalar(x_353)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_353;
}
lean_ctor_set(x_372, 0, x_343);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_373 = lean_ctor_get(x_341, 1);
lean_inc(x_373);
x_374 = lean_ctor_get(x_341, 0);
lean_inc(x_374);
lean_dec(x_341);
x_375 = lean_ctor_get(x_373, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_373, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_373, 3);
lean_inc(x_377);
x_378 = lean_ctor_get(x_373, 4);
lean_inc(x_378);
x_379 = lean_ctor_get(x_373, 5);
lean_inc(x_379);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 lean_ctor_release(x_373, 3);
 lean_ctor_release(x_373, 4);
 lean_ctor_release(x_373, 5);
 x_380 = x_373;
} else {
 lean_dec_ref(x_373);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(0, 6, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_375);
lean_ctor_set(x_381, 1, x_149);
lean_ctor_set(x_381, 2, x_376);
lean_ctor_set(x_381, 3, x_377);
lean_ctor_set(x_381, 4, x_378);
lean_ctor_set(x_381, 5, x_379);
lean_ctor_set(x_142, 0, x_381);
x_316 = x_374;
x_317 = x_142;
goto block_340;
}
block_340:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_318 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_317);
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_320 = x_318;
} else {
 lean_dec_ref(x_318);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_321, 4);
lean_inc(x_322);
x_323 = lean_ctor_get(x_319, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_319, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_319, 3);
lean_inc(x_325);
x_326 = lean_ctor_get(x_319, 4);
lean_inc(x_326);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 lean_ctor_release(x_319, 2);
 lean_ctor_release(x_319, 3);
 lean_ctor_release(x_319, 4);
 x_327 = x_319;
} else {
 lean_dec_ref(x_319);
 x_327 = lean_box(0);
}
x_328 = lean_ctor_get(x_321, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_321, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_321, 2);
lean_inc(x_330);
x_331 = lean_ctor_get(x_321, 3);
lean_inc(x_331);
x_332 = lean_ctor_get(x_321, 5);
lean_inc(x_332);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 lean_ctor_release(x_321, 5);
 x_333 = x_321;
} else {
 lean_dec_ref(x_321);
 x_333 = lean_box(0);
}
x_334 = lean_ctor_get(x_322, 0);
lean_inc(x_334);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 x_335 = x_322;
} else {
 lean_dec_ref(x_322);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(0, 1, 1);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set_uint8(x_336, sizeof(void*)*1, x_145);
if (lean_is_scalar(x_333)) {
 x_337 = lean_alloc_ctor(0, 6, 0);
} else {
 x_337 = x_333;
}
lean_ctor_set(x_337, 0, x_328);
lean_ctor_set(x_337, 1, x_329);
lean_ctor_set(x_337, 2, x_330);
lean_ctor_set(x_337, 3, x_331);
lean_ctor_set(x_337, 4, x_336);
lean_ctor_set(x_337, 5, x_332);
if (lean_is_scalar(x_327)) {
 x_338 = lean_alloc_ctor(0, 5, 0);
} else {
 x_338 = x_327;
}
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_323);
lean_ctor_set(x_338, 2, x_324);
lean_ctor_set(x_338, 3, x_325);
lean_ctor_set(x_338, 4, x_326);
if (lean_is_scalar(x_320)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_320;
 lean_ctor_set_tag(x_339, 1);
}
lean_ctor_set(x_339, 0, x_316);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_416; lean_object* x_417; 
x_382 = lean_ctor_get(x_143, 0);
x_383 = lean_ctor_get(x_143, 1);
x_384 = lean_ctor_get(x_143, 2);
x_385 = lean_ctor_get(x_143, 3);
x_386 = lean_ctor_get(x_143, 5);
lean_inc(x_386);
lean_inc(x_385);
lean_inc(x_384);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_143);
x_387 = lean_ctor_get(x_144, 0);
lean_inc(x_387);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 x_388 = x_144;
} else {
 lean_dec_ref(x_144);
 x_388 = lean_box(0);
}
x_389 = 0;
if (lean_is_scalar(x_388)) {
 x_390 = lean_alloc_ctor(0, 1, 1);
} else {
 x_390 = x_388;
}
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set_uint8(x_390, sizeof(void*)*1, x_389);
x_416 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_416, 0, x_382);
lean_ctor_set(x_416, 1, x_1);
lean_ctor_set(x_416, 2, x_384);
lean_ctor_set(x_416, 3, x_385);
lean_ctor_set(x_416, 4, x_390);
lean_ctor_set(x_416, 5, x_386);
x_417 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_416);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 0);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_ctor_get(x_418, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_418, 2);
lean_inc(x_421);
x_422 = lean_ctor_get(x_418, 3);
lean_inc(x_422);
x_423 = lean_ctor_get(x_418, 4);
lean_inc(x_423);
x_424 = lean_ctor_get(x_418, 5);
lean_inc(x_424);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 lean_ctor_release(x_418, 2);
 lean_ctor_release(x_418, 3);
 lean_ctor_release(x_418, 4);
 lean_ctor_release(x_418, 5);
 x_425 = x_418;
} else {
 lean_dec_ref(x_418);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(0, 6, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_420);
lean_ctor_set(x_426, 1, x_383);
lean_ctor_set(x_426, 2, x_421);
lean_ctor_set(x_426, 3, x_422);
lean_ctor_set(x_426, 4, x_423);
lean_ctor_set(x_426, 5, x_424);
lean_ctor_set(x_142, 0, x_426);
x_427 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_142);
x_428 = lean_ctor_get(x_427, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_429 = x_427;
} else {
 lean_dec_ref(x_427);
 x_429 = lean_box(0);
}
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_430, 4);
lean_inc(x_431);
x_432 = lean_ctor_get(x_428, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_428, 2);
lean_inc(x_433);
x_434 = lean_ctor_get(x_428, 3);
lean_inc(x_434);
x_435 = lean_ctor_get(x_428, 4);
lean_inc(x_435);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 lean_ctor_release(x_428, 4);
 x_436 = x_428;
} else {
 lean_dec_ref(x_428);
 x_436 = lean_box(0);
}
x_437 = lean_ctor_get(x_430, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_430, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_430, 2);
lean_inc(x_439);
x_440 = lean_ctor_get(x_430, 3);
lean_inc(x_440);
x_441 = lean_ctor_get(x_430, 5);
lean_inc(x_441);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 lean_ctor_release(x_430, 4);
 lean_ctor_release(x_430, 5);
 x_442 = x_430;
} else {
 lean_dec_ref(x_430);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_431, 0);
lean_inc(x_443);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 x_444 = x_431;
} else {
 lean_dec_ref(x_431);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(0, 1, 1);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set_uint8(x_445, sizeof(void*)*1, x_145);
if (lean_is_scalar(x_442)) {
 x_446 = lean_alloc_ctor(0, 6, 0);
} else {
 x_446 = x_442;
}
lean_ctor_set(x_446, 0, x_437);
lean_ctor_set(x_446, 1, x_438);
lean_ctor_set(x_446, 2, x_439);
lean_ctor_set(x_446, 3, x_440);
lean_ctor_set(x_446, 4, x_445);
lean_ctor_set(x_446, 5, x_441);
if (lean_is_scalar(x_436)) {
 x_447 = lean_alloc_ctor(0, 5, 0);
} else {
 x_447 = x_436;
}
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_432);
lean_ctor_set(x_447, 2, x_433);
lean_ctor_set(x_447, 3, x_434);
lean_ctor_set(x_447, 4, x_435);
if (lean_is_scalar(x_429)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_429;
}
lean_ctor_set(x_448, 0, x_419);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_449 = lean_ctor_get(x_417, 1);
lean_inc(x_449);
x_450 = lean_ctor_get(x_417, 0);
lean_inc(x_450);
lean_dec(x_417);
x_451 = lean_ctor_get(x_449, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_449, 2);
lean_inc(x_452);
x_453 = lean_ctor_get(x_449, 3);
lean_inc(x_453);
x_454 = lean_ctor_get(x_449, 4);
lean_inc(x_454);
x_455 = lean_ctor_get(x_449, 5);
lean_inc(x_455);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 lean_ctor_release(x_449, 2);
 lean_ctor_release(x_449, 3);
 lean_ctor_release(x_449, 4);
 lean_ctor_release(x_449, 5);
 x_456 = x_449;
} else {
 lean_dec_ref(x_449);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(0, 6, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_451);
lean_ctor_set(x_457, 1, x_383);
lean_ctor_set(x_457, 2, x_452);
lean_ctor_set(x_457, 3, x_453);
lean_ctor_set(x_457, 4, x_454);
lean_ctor_set(x_457, 5, x_455);
lean_ctor_set(x_142, 0, x_457);
x_391 = x_450;
x_392 = x_142;
goto block_415;
}
block_415:
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_393 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_392);
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_395 = x_393;
} else {
 lean_dec_ref(x_393);
 x_395 = lean_box(0);
}
x_396 = lean_ctor_get(x_394, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_396, 4);
lean_inc(x_397);
x_398 = lean_ctor_get(x_394, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_394, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_394, 3);
lean_inc(x_400);
x_401 = lean_ctor_get(x_394, 4);
lean_inc(x_401);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 lean_ctor_release(x_394, 2);
 lean_ctor_release(x_394, 3);
 lean_ctor_release(x_394, 4);
 x_402 = x_394;
} else {
 lean_dec_ref(x_394);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_396, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_396, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_396, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_396, 3);
lean_inc(x_406);
x_407 = lean_ctor_get(x_396, 5);
lean_inc(x_407);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 lean_ctor_release(x_396, 2);
 lean_ctor_release(x_396, 3);
 lean_ctor_release(x_396, 4);
 lean_ctor_release(x_396, 5);
 x_408 = x_396;
} else {
 lean_dec_ref(x_396);
 x_408 = lean_box(0);
}
x_409 = lean_ctor_get(x_397, 0);
lean_inc(x_409);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 x_410 = x_397;
} else {
 lean_dec_ref(x_397);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(0, 1, 1);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set_uint8(x_411, sizeof(void*)*1, x_145);
if (lean_is_scalar(x_408)) {
 x_412 = lean_alloc_ctor(0, 6, 0);
} else {
 x_412 = x_408;
}
lean_ctor_set(x_412, 0, x_403);
lean_ctor_set(x_412, 1, x_404);
lean_ctor_set(x_412, 2, x_405);
lean_ctor_set(x_412, 3, x_406);
lean_ctor_set(x_412, 4, x_411);
lean_ctor_set(x_412, 5, x_407);
if (lean_is_scalar(x_402)) {
 x_413 = lean_alloc_ctor(0, 5, 0);
} else {
 x_413 = x_402;
}
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_398);
lean_ctor_set(x_413, 2, x_399);
lean_ctor_set(x_413, 3, x_400);
lean_ctor_set(x_413, 4, x_401);
if (lean_is_scalar(x_395)) {
 x_414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_414 = x_395;
 lean_ctor_set_tag(x_414, 1);
}
lean_ctor_set(x_414, 0, x_391);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_497; lean_object* x_498; 
x_458 = lean_ctor_get(x_142, 1);
x_459 = lean_ctor_get(x_142, 2);
x_460 = lean_ctor_get(x_142, 3);
x_461 = lean_ctor_get(x_142, 4);
lean_inc(x_461);
lean_inc(x_460);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_142);
x_462 = lean_ctor_get(x_143, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_143, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_143, 2);
lean_inc(x_464);
x_465 = lean_ctor_get(x_143, 3);
lean_inc(x_465);
x_466 = lean_ctor_get(x_143, 5);
lean_inc(x_466);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 lean_ctor_release(x_143, 5);
 x_467 = x_143;
} else {
 lean_dec_ref(x_143);
 x_467 = lean_box(0);
}
x_468 = lean_ctor_get(x_144, 0);
lean_inc(x_468);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 x_469 = x_144;
} else {
 lean_dec_ref(x_144);
 x_469 = lean_box(0);
}
x_470 = 0;
if (lean_is_scalar(x_469)) {
 x_471 = lean_alloc_ctor(0, 1, 1);
} else {
 x_471 = x_469;
}
lean_ctor_set(x_471, 0, x_468);
lean_ctor_set_uint8(x_471, sizeof(void*)*1, x_470);
if (lean_is_scalar(x_467)) {
 x_497 = lean_alloc_ctor(0, 6, 0);
} else {
 x_497 = x_467;
}
lean_ctor_set(x_497, 0, x_462);
lean_ctor_set(x_497, 1, x_1);
lean_ctor_set(x_497, 2, x_464);
lean_ctor_set(x_497, 3, x_465);
lean_ctor_set(x_497, 4, x_471);
lean_ctor_set(x_497, 5, x_466);
x_498 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_497);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 0);
lean_inc(x_500);
lean_dec(x_498);
x_501 = lean_ctor_get(x_499, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_499, 2);
lean_inc(x_502);
x_503 = lean_ctor_get(x_499, 3);
lean_inc(x_503);
x_504 = lean_ctor_get(x_499, 4);
lean_inc(x_504);
x_505 = lean_ctor_get(x_499, 5);
lean_inc(x_505);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 lean_ctor_release(x_499, 2);
 lean_ctor_release(x_499, 3);
 lean_ctor_release(x_499, 4);
 lean_ctor_release(x_499, 5);
 x_506 = x_499;
} else {
 lean_dec_ref(x_499);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(0, 6, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_501);
lean_ctor_set(x_507, 1, x_463);
lean_ctor_set(x_507, 2, x_502);
lean_ctor_set(x_507, 3, x_503);
lean_ctor_set(x_507, 4, x_504);
lean_ctor_set(x_507, 5, x_505);
x_508 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_458);
lean_ctor_set(x_508, 2, x_459);
lean_ctor_set(x_508, 3, x_460);
lean_ctor_set(x_508, 4, x_461);
x_509 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_508);
x_510 = lean_ctor_get(x_509, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_511 = x_509;
} else {
 lean_dec_ref(x_509);
 x_511 = lean_box(0);
}
x_512 = lean_ctor_get(x_510, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_512, 4);
lean_inc(x_513);
x_514 = lean_ctor_get(x_510, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_510, 2);
lean_inc(x_515);
x_516 = lean_ctor_get(x_510, 3);
lean_inc(x_516);
x_517 = lean_ctor_get(x_510, 4);
lean_inc(x_517);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 lean_ctor_release(x_510, 1);
 lean_ctor_release(x_510, 2);
 lean_ctor_release(x_510, 3);
 lean_ctor_release(x_510, 4);
 x_518 = x_510;
} else {
 lean_dec_ref(x_510);
 x_518 = lean_box(0);
}
x_519 = lean_ctor_get(x_512, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_512, 1);
lean_inc(x_520);
x_521 = lean_ctor_get(x_512, 2);
lean_inc(x_521);
x_522 = lean_ctor_get(x_512, 3);
lean_inc(x_522);
x_523 = lean_ctor_get(x_512, 5);
lean_inc(x_523);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 lean_ctor_release(x_512, 2);
 lean_ctor_release(x_512, 3);
 lean_ctor_release(x_512, 4);
 lean_ctor_release(x_512, 5);
 x_524 = x_512;
} else {
 lean_dec_ref(x_512);
 x_524 = lean_box(0);
}
x_525 = lean_ctor_get(x_513, 0);
lean_inc(x_525);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 x_526 = x_513;
} else {
 lean_dec_ref(x_513);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(0, 1, 1);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_525);
lean_ctor_set_uint8(x_527, sizeof(void*)*1, x_145);
if (lean_is_scalar(x_524)) {
 x_528 = lean_alloc_ctor(0, 6, 0);
} else {
 x_528 = x_524;
}
lean_ctor_set(x_528, 0, x_519);
lean_ctor_set(x_528, 1, x_520);
lean_ctor_set(x_528, 2, x_521);
lean_ctor_set(x_528, 3, x_522);
lean_ctor_set(x_528, 4, x_527);
lean_ctor_set(x_528, 5, x_523);
if (lean_is_scalar(x_518)) {
 x_529 = lean_alloc_ctor(0, 5, 0);
} else {
 x_529 = x_518;
}
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_514);
lean_ctor_set(x_529, 2, x_515);
lean_ctor_set(x_529, 3, x_516);
lean_ctor_set(x_529, 4, x_517);
if (lean_is_scalar(x_511)) {
 x_530 = lean_alloc_ctor(0, 2, 0);
} else {
 x_530 = x_511;
}
lean_ctor_set(x_530, 0, x_500);
lean_ctor_set(x_530, 1, x_529);
return x_530;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_531 = lean_ctor_get(x_498, 1);
lean_inc(x_531);
x_532 = lean_ctor_get(x_498, 0);
lean_inc(x_532);
lean_dec(x_498);
x_533 = lean_ctor_get(x_531, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_531, 2);
lean_inc(x_534);
x_535 = lean_ctor_get(x_531, 3);
lean_inc(x_535);
x_536 = lean_ctor_get(x_531, 4);
lean_inc(x_536);
x_537 = lean_ctor_get(x_531, 5);
lean_inc(x_537);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 lean_ctor_release(x_531, 2);
 lean_ctor_release(x_531, 3);
 lean_ctor_release(x_531, 4);
 lean_ctor_release(x_531, 5);
 x_538 = x_531;
} else {
 lean_dec_ref(x_531);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(0, 6, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_533);
lean_ctor_set(x_539, 1, x_463);
lean_ctor_set(x_539, 2, x_534);
lean_ctor_set(x_539, 3, x_535);
lean_ctor_set(x_539, 4, x_536);
lean_ctor_set(x_539, 5, x_537);
x_540 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_458);
lean_ctor_set(x_540, 2, x_459);
lean_ctor_set(x_540, 3, x_460);
lean_ctor_set(x_540, 4, x_461);
x_472 = x_532;
x_473 = x_540;
goto block_496;
}
block_496:
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_474 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_473);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_476 = x_474;
} else {
 lean_dec_ref(x_474);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_475, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_477, 4);
lean_inc(x_478);
x_479 = lean_ctor_get(x_475, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_475, 2);
lean_inc(x_480);
x_481 = lean_ctor_get(x_475, 3);
lean_inc(x_481);
x_482 = lean_ctor_get(x_475, 4);
lean_inc(x_482);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 lean_ctor_release(x_475, 2);
 lean_ctor_release(x_475, 3);
 lean_ctor_release(x_475, 4);
 x_483 = x_475;
} else {
 lean_dec_ref(x_475);
 x_483 = lean_box(0);
}
x_484 = lean_ctor_get(x_477, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_477, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_477, 2);
lean_inc(x_486);
x_487 = lean_ctor_get(x_477, 3);
lean_inc(x_487);
x_488 = lean_ctor_get(x_477, 5);
lean_inc(x_488);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 lean_ctor_release(x_477, 2);
 lean_ctor_release(x_477, 3);
 lean_ctor_release(x_477, 4);
 lean_ctor_release(x_477, 5);
 x_489 = x_477;
} else {
 lean_dec_ref(x_477);
 x_489 = lean_box(0);
}
x_490 = lean_ctor_get(x_478, 0);
lean_inc(x_490);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 x_491 = x_478;
} else {
 lean_dec_ref(x_478);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(0, 1, 1);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set_uint8(x_492, sizeof(void*)*1, x_145);
if (lean_is_scalar(x_489)) {
 x_493 = lean_alloc_ctor(0, 6, 0);
} else {
 x_493 = x_489;
}
lean_ctor_set(x_493, 0, x_484);
lean_ctor_set(x_493, 1, x_485);
lean_ctor_set(x_493, 2, x_486);
lean_ctor_set(x_493, 3, x_487);
lean_ctor_set(x_493, 4, x_492);
lean_ctor_set(x_493, 5, x_488);
if (lean_is_scalar(x_483)) {
 x_494 = lean_alloc_ctor(0, 5, 0);
} else {
 x_494 = x_483;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_479);
lean_ctor_set(x_494, 2, x_480);
lean_ctor_set(x_494, 3, x_481);
lean_ctor_set(x_494, 4, x_482);
if (lean_is_scalar(x_476)) {
 x_495 = lean_alloc_ctor(1, 2, 0);
} else {
 x_495 = x_476;
 lean_ctor_set_tag(x_495, 1);
}
lean_ctor_set(x_495, 0, x_472);
lean_ctor_set(x_495, 1, x_494);
return x_495;
}
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_41; lean_object* x_42; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_11 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_6, 1, x_1);
lean_inc(x_4);
x_70 = l_Lean_Meta_openAbstractMVarsResult(x_7, x_4, x_6);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Meta_isExprDefEq(x_2, x_74, x_4, x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
lean_ctor_set(x_5, 0, x_78);
x_79 = lean_box(0);
x_12 = x_79;
x_13 = x_5;
goto block_40;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_dec(x_75);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_ctor_set(x_5, 0, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_12 = x_82;
x_13 = x_5;
goto block_40;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_75, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_dec(x_75);
lean_ctor_set(x_5, 0, x_84);
x_41 = x_83;
x_42 = x_5;
goto block_69;
}
block_40:
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
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
lean_dec(x_17);
lean_ctor_set(x_15, 1, x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 2);
x_21 = lean_ctor_get(x_15, 3);
x_22 = lean_ctor_get(x_15, 4);
x_23 = lean_ctor_get(x_15, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_23);
lean_ctor_set(x_13, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_13);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
x_28 = lean_ctor_get(x_13, 2);
x_29 = lean_ctor_get(x_13, 3);
x_30 = lean_ctor_get(x_13, 4);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_26, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 5);
lean_inc(x_35);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 x_36 = x_26;
} else {
 lean_dec_ref(x_26);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 6, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_11);
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
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
block_69:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 1);
lean_dec(x_46);
lean_ctor_set(x_44, 1, x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 2);
x_50 = lean_ctor_get(x_44, 3);
x_51 = lean_ctor_get(x_44, 4);
x_52 = lean_ctor_get(x_44, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_11);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_51);
lean_ctor_set(x_53, 5, x_52);
lean_ctor_set(x_42, 0, x_53);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_42);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_ctor_get(x_42, 0);
x_56 = lean_ctor_get(x_42, 1);
x_57 = lean_ctor_get(x_42, 2);
x_58 = lean_ctor_get(x_42, 3);
x_59 = lean_ctor_get(x_42, 4);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_42);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_55, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_55, 5);
lean_inc(x_64);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 x_65 = x_55;
} else {
 lean_dec_ref(x_55);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 6, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_11);
lean_ctor_set(x_66, 2, x_61);
lean_ctor_set(x_66, 3, x_62);
lean_ctor_set(x_66, 4, x_63);
lean_ctor_set(x_66, 5, x_64);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_56);
lean_ctor_set(x_67, 2, x_57);
lean_ctor_set(x_67, 3, x_58);
lean_ctor_set(x_67, 4, x_59);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_41);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_109; lean_object* x_110; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_85 = lean_ctor_get(x_6, 0);
x_86 = lean_ctor_get(x_6, 1);
x_87 = lean_ctor_get(x_6, 2);
x_88 = lean_ctor_get(x_6, 3);
x_89 = lean_ctor_get(x_6, 4);
x_90 = lean_ctor_get(x_6, 5);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_6);
x_127 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_127, 0, x_85);
lean_ctor_set(x_127, 1, x_1);
lean_ctor_set(x_127, 2, x_87);
lean_ctor_set(x_127, 3, x_88);
lean_ctor_set(x_127, 4, x_89);
lean_ctor_set(x_127, 5, x_90);
lean_inc(x_4);
x_128 = l_Lean_Meta_openAbstractMVarsResult(x_7, x_4, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_Meta_isExprDefEq(x_2, x_132, x_4, x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_unbox(x_134);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
lean_ctor_set(x_5, 0, x_136);
x_137 = lean_box(0);
x_91 = x_137;
x_92 = x_5;
goto block_108;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_dec(x_133);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_ctor_set(x_5, 0, x_138);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_91 = x_140;
x_92 = x_5;
goto block_108;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_133, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_133, 1);
lean_inc(x_142);
lean_dec(x_133);
lean_ctor_set(x_5, 0, x_142);
x_109 = x_141;
x_110 = x_5;
goto block_126;
}
block_108:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 4);
lean_inc(x_97);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 lean_ctor_release(x_92, 3);
 lean_ctor_release(x_92, 4);
 x_98 = x_92;
} else {
 lean_dec_ref(x_92);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_93, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_93, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_93, 5);
lean_inc(x_103);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 lean_ctor_release(x_93, 2);
 lean_ctor_release(x_93, 3);
 lean_ctor_release(x_93, 4);
 lean_ctor_release(x_93, 5);
 x_104 = x_93;
} else {
 lean_dec_ref(x_93);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 6, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_86);
lean_ctor_set(x_105, 2, x_100);
lean_ctor_set(x_105, 3, x_101);
lean_ctor_set(x_105, 4, x_102);
lean_ctor_set(x_105, 5, x_103);
if (lean_is_scalar(x_98)) {
 x_106 = lean_alloc_ctor(0, 5, 0);
} else {
 x_106 = x_98;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_94);
lean_ctor_set(x_106, 2, x_95);
lean_ctor_set(x_106, 3, x_96);
lean_ctor_set(x_106, 4, x_97);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_91);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
block_126:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 4);
lean_inc(x_115);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 x_116 = x_110;
} else {
 lean_dec_ref(x_110);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_111, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_111, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_111, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_111, 4);
lean_inc(x_120);
x_121 = lean_ctor_get(x_111, 5);
lean_inc(x_121);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 lean_ctor_release(x_111, 5);
 x_122 = x_111;
} else {
 lean_dec_ref(x_111);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 6, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_117);
lean_ctor_set(x_123, 1, x_86);
lean_ctor_set(x_123, 2, x_118);
lean_ctor_set(x_123, 3, x_119);
lean_ctor_set(x_123, 4, x_120);
lean_ctor_set(x_123, 5, x_121);
if (lean_is_scalar(x_116)) {
 x_124 = lean_alloc_ctor(0, 5, 0);
} else {
 x_124 = x_116;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_112);
lean_ctor_set(x_124, 2, x_113);
lean_ctor_set(x_124, 3, x_114);
lean_ctor_set(x_124, 4, x_115);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_109);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_172; lean_object* x_173; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_143 = lean_ctor_get(x_5, 1);
x_144 = lean_ctor_get(x_5, 2);
x_145 = lean_ctor_get(x_5, 3);
x_146 = lean_ctor_get(x_5, 4);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_5);
x_147 = lean_ctor_get(x_6, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_6, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_6, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_6, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_6, 4);
lean_inc(x_151);
x_152 = lean_ctor_get(x_6, 5);
lean_inc(x_152);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 x_153 = x_6;
} else {
 lean_dec_ref(x_6);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_190 = lean_alloc_ctor(0, 6, 0);
} else {
 x_190 = x_153;
}
lean_ctor_set(x_190, 0, x_147);
lean_ctor_set(x_190, 1, x_1);
lean_ctor_set(x_190, 2, x_149);
lean_ctor_set(x_190, 3, x_150);
lean_ctor_set(x_190, 4, x_151);
lean_ctor_set(x_190, 5, x_152);
lean_inc(x_4);
x_191 = l_Lean_Meta_openAbstractMVarsResult(x_7, x_4, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_dec(x_191);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Lean_Meta_isExprDefEq(x_2, x_195, x_4, x_194);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; uint8_t x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_unbox(x_197);
lean_dec(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_143);
lean_ctor_set(x_200, 2, x_144);
lean_ctor_set(x_200, 3, x_145);
lean_ctor_set(x_200, 4, x_146);
x_201 = lean_box(0);
x_154 = x_201;
x_155 = x_200;
goto block_171;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_196, 1);
lean_inc(x_202);
lean_dec(x_196);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
x_204 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_143);
lean_ctor_set(x_204, 2, x_144);
lean_ctor_set(x_204, 3, x_145);
lean_ctor_set(x_204, 4, x_146);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_203);
x_154 = x_205;
x_155 = x_204;
goto block_171;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_196, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_196, 1);
lean_inc(x_207);
lean_dec(x_196);
x_208 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_143);
lean_ctor_set(x_208, 2, x_144);
lean_ctor_set(x_208, 3, x_145);
lean_ctor_set(x_208, 4, x_146);
x_172 = x_206;
x_173 = x_208;
goto block_189;
}
block_171:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 4);
lean_inc(x_160);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 lean_ctor_release(x_155, 3);
 lean_ctor_release(x_155, 4);
 x_161 = x_155;
} else {
 lean_dec_ref(x_155);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_156, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_156, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_156, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_156, 4);
lean_inc(x_165);
x_166 = lean_ctor_get(x_156, 5);
lean_inc(x_166);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 lean_ctor_release(x_156, 2);
 lean_ctor_release(x_156, 3);
 lean_ctor_release(x_156, 4);
 lean_ctor_release(x_156, 5);
 x_167 = x_156;
} else {
 lean_dec_ref(x_156);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 6, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_148);
lean_ctor_set(x_168, 2, x_163);
lean_ctor_set(x_168, 3, x_164);
lean_ctor_set(x_168, 4, x_165);
lean_ctor_set(x_168, 5, x_166);
if (lean_is_scalar(x_161)) {
 x_169 = lean_alloc_ctor(0, 5, 0);
} else {
 x_169 = x_161;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_157);
lean_ctor_set(x_169, 2, x_158);
lean_ctor_set(x_169, 3, x_159);
lean_ctor_set(x_169, 4, x_160);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_154);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
block_189:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_173, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_173, 3);
lean_inc(x_177);
x_178 = lean_ctor_get(x_173, 4);
lean_inc(x_178);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 lean_ctor_release(x_173, 2);
 lean_ctor_release(x_173, 3);
 lean_ctor_release(x_173, 4);
 x_179 = x_173;
} else {
 lean_dec_ref(x_173);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_174, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_174, 2);
lean_inc(x_181);
x_182 = lean_ctor_get(x_174, 3);
lean_inc(x_182);
x_183 = lean_ctor_get(x_174, 4);
lean_inc(x_183);
x_184 = lean_ctor_get(x_174, 5);
lean_inc(x_184);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 lean_ctor_release(x_174, 2);
 lean_ctor_release(x_174, 3);
 lean_ctor_release(x_174, 4);
 lean_ctor_release(x_174, 5);
 x_185 = x_174;
} else {
 lean_dec_ref(x_174);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 6, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_180);
lean_ctor_set(x_186, 1, x_148);
lean_ctor_set(x_186, 2, x_181);
lean_ctor_set(x_186, 3, x_182);
lean_ctor_set(x_186, 4, x_183);
lean_ctor_set(x_186, 5, x_184);
if (lean_is_scalar(x_179)) {
 x_187 = lean_alloc_ctor(0, 5, 0);
} else {
 x_187 = x_179;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_175);
lean_ctor_set(x_187, 2, x_176);
lean_ctor_set(x_187, 3, x_177);
lean_ctor_set(x_187, 4, x_178);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_172);
lean_ctor_set(x_188, 1, x_187);
return x_188;
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
lean_object* x_23; uint8_t x_24; lean_object* x_130; uint8_t x_131; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_130 = lean_ctor_get(x_23, 0);
lean_inc(x_130);
x_131 = l_Array_isEmpty___rarg(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
uint8_t x_132; 
x_132 = 0;
x_24 = x_132;
goto block_129;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_23, 1);
lean_inc(x_133);
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_nat_dec_eq(x_133, x_134);
lean_dec(x_133);
x_24 = x_135;
goto block_129;
}
block_129:
{
uint8_t x_25; 
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_3);
x_28 = l_Lean_Meta_openAbstractMVarsResult(x_23, x_3, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
lean_ctor_set(x_4, 0, x_30);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_50 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_4);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_51, sizeof(void*)*1);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l_String_posOfAux___main___closed__2;
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_56 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_55, x_3, x_53);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unbox(x_57);
lean_dec(x_57);
x_34 = x_59;
x_35 = x_58;
goto block_49;
}
else
{
uint8_t x_60; 
x_60 = 0;
x_34 = x_60;
x_35 = x_53;
goto block_49;
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_50, 1);
lean_inc(x_61);
lean_dec(x_50);
x_62 = l_String_posOfAux___main___closed__1;
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_64 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_63, x_3, x_61);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_34 = x_67;
x_35 = x_66;
goto block_49;
}
else
{
uint8_t x_68; 
x_68 = 0;
x_34 = x_68;
x_35 = x_61;
goto block_49;
}
}
block_49:
{
if (x_34 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_3);
x_36 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_31;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_31);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_39 = l_Lean_Meta_SynthInstance_wakeUp___closed__3;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_42 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_41, x_40, x_3, x_35);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_69 = lean_ctor_get(x_4, 0);
x_70 = lean_ctor_get(x_4, 1);
x_71 = lean_ctor_get(x_4, 2);
x_72 = lean_ctor_get(x_4, 3);
x_73 = lean_ctor_get(x_4, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_4);
lean_inc(x_3);
x_74 = l_Lean_Meta_openAbstractMVarsResult(x_23, x_3, x_69);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set(x_78, 4, x_73);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_95 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_78);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_96, sizeof(void*)*1);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = l_String_posOfAux___main___closed__2;
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_100 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_101 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_100, x_3, x_98);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_unbox(x_102);
lean_dec(x_102);
x_81 = x_104;
x_82 = x_103;
goto block_94;
}
else
{
uint8_t x_105; 
x_105 = 0;
x_81 = x_105;
x_82 = x_98;
goto block_94;
}
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_95, 1);
lean_inc(x_106);
lean_dec(x_95);
x_107 = l_String_posOfAux___main___closed__1;
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_109 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_108, x_3, x_106);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_unbox(x_110);
lean_dec(x_110);
x_81 = x_112;
x_82 = x_111;
goto block_94;
}
else
{
uint8_t x_113; 
x_113 = 0;
x_81 = x_113;
x_82 = x_106;
goto block_94;
}
}
block_94:
{
if (x_81 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_80);
lean_dec(x_3);
x_83 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_77;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_77);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_80);
x_86 = l_Lean_Meta_SynthInstance_wakeUp___closed__3;
x_87 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_89 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_88, x_87, x_3, x_82);
lean_dec(x_3);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
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
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_4);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_4, 1);
lean_dec(x_115);
x_116 = lean_ctor_get(x_23, 2);
lean_inc(x_116);
lean_dec(x_23);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_4, 1, x_117);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_4);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_ctor_get(x_4, 0);
x_121 = lean_ctor_get(x_4, 2);
x_122 = lean_ctor_get(x_4, 3);
x_123 = lean_ctor_get(x_4, 4);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_4);
x_124 = lean_ctor_get(x_23, 2);
lean_inc(x_124);
lean_dec(x_23);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_120);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_121);
lean_ctor_set(x_126, 3, x_122);
lean_ctor_set(x_126, 4, x_123);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
return x_128;
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
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_fget(x_3, x_4);
lean_inc(x_5);
x_13 = l_Lean_Meta_SynthInstance_wakeUp(x_7, x_12, x_5, x_6);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_4 = x_16;
x_6 = x_14;
goto _start;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_40; uint8_t x_217; lean_object* x_218; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_10 = lean_ctor_get(x_4, 1);
lean_ctor_set(x_4, 1, x_5);
x_247 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_3);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get_uint8(x_248, sizeof(void*)*1);
lean_dec(x_248);
if (x_249 == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_dec(x_247);
x_251 = l_String_posOfAux___main___closed__2;
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_252 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_253 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_252, x_2, x_250);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_unbox(x_254);
lean_dec(x_254);
x_217 = x_256;
x_218 = x_255;
goto block_246;
}
else
{
uint8_t x_257; 
x_257 = 0;
x_217 = x_257;
x_218 = x_250;
goto block_246;
}
}
else
{
lean_object* x_258; uint8_t x_259; 
x_258 = lean_ctor_get(x_247, 1);
lean_inc(x_258);
lean_dec(x_247);
x_259 = l_String_posOfAux___main___closed__1;
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_260 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_261 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_260, x_2, x_258);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_unbox(x_262);
lean_dec(x_262);
x_217 = x_264;
x_218 = x_263;
goto block_246;
}
else
{
uint8_t x_265; 
x_265 = 0;
x_217 = x_265;
x_218 = x_258;
goto block_246;
}
}
block_39:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_dec(x_16);
lean_ctor_set(x_14, 1, x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 2);
x_20 = lean_ctor_get(x_14, 3);
x_21 = lean_ctor_get(x_14, 4);
x_22 = lean_ctor_get(x_14, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_10);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
lean_ctor_set(x_12, 0, x_23);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
x_27 = lean_ctor_get(x_12, 2);
x_28 = lean_ctor_get(x_12, 3);
x_29 = lean_ctor_get(x_12, 4);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_25, 5);
lean_inc(x_34);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 x_35 = x_25;
} else {
 lean_dec_ref(x_25);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 6, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_10);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_34);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_27);
lean_ctor_set(x_37, 3, x_28);
lean_ctor_set(x_37, 4, x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
block_216:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = l_Lean_Meta_instantiateMVars(x_6, x_2, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_abstractMVars(x_44, x_2, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 2);
lean_inc(x_49);
lean_inc(x_2);
x_50 = l_Lean_Meta_inferType(x_49, x_2, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_51);
lean_inc(x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_51);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 1);
lean_dec(x_55);
lean_ctor_set(x_52, 1, x_10);
lean_ctor_set(x_40, 0, x_52);
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
lean_dec(x_1);
lean_inc(x_2);
x_57 = l_Lean_Meta_SynthInstance_getEntry(x_56, x_2, x_40);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_57, 1);
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_59, 1);
x_64 = l_Lean_Meta_SynthInstance_isNewAnswer(x_63, x_53);
x_65 = l_coeDecidableEq(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_free_object(x_59);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_2);
x_66 = lean_box(0);
lean_ctor_set(x_57, 0, x_66);
return x_57;
}
else
{
lean_object* x_67; uint8_t x_68; 
lean_free_object(x_57);
x_67 = lean_array_push(x_63, x_53);
lean_inc(x_62);
lean_ctor_set(x_59, 1, x_67);
x_68 = !lean_is_exclusive(x_61);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_61, 4);
x_70 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_69, x_56, x_59);
lean_ctor_set(x_61, 4, x_70);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_47, x_51, x_62, x_71, x_2, x_61);
lean_dec(x_62);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_61, 0);
x_74 = lean_ctor_get(x_61, 1);
x_75 = lean_ctor_get(x_61, 2);
x_76 = lean_ctor_get(x_61, 3);
x_77 = lean_ctor_get(x_61, 4);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_61);
x_78 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_77, x_56, x_59);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_74);
lean_ctor_set(x_79, 2, x_75);
lean_ctor_set(x_79, 3, x_76);
lean_ctor_set(x_79, 4, x_78);
x_80 = lean_unsigned_to_nat(0u);
x_81 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_47, x_51, x_62, x_80, x_2, x_79);
lean_dec(x_62);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_57, 1);
x_83 = lean_ctor_get(x_59, 0);
x_84 = lean_ctor_get(x_59, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_59);
x_85 = l_Lean_Meta_SynthInstance_isNewAnswer(x_84, x_53);
x_86 = l_coeDecidableEq(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_2);
x_87 = lean_box(0);
lean_ctor_set(x_57, 0, x_87);
return x_57;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_free_object(x_57);
x_88 = lean_array_push(x_84, x_53);
lean_inc(x_83);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_ctor_get(x_82, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_82, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_82, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_82, 4);
lean_inc(x_94);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 lean_ctor_release(x_82, 3);
 lean_ctor_release(x_82, 4);
 x_95 = x_82;
} else {
 lean_dec_ref(x_82);
 x_95 = lean_box(0);
}
x_96 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_94, x_56, x_89);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 5, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_91);
lean_ctor_set(x_97, 2, x_92);
lean_ctor_set(x_97, 3, x_93);
lean_ctor_set(x_97, 4, x_96);
x_98 = lean_unsigned_to_nat(0u);
x_99 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_47, x_51, x_83, x_98, x_2, x_97);
lean_dec(x_83);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; 
x_100 = lean_ctor_get(x_57, 0);
x_101 = lean_ctor_get(x_57, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_57);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
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
x_105 = l_Lean_Meta_SynthInstance_isNewAnswer(x_103, x_53);
x_106 = l_coeDecidableEq(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_2);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_101);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_109 = lean_array_push(x_103, x_53);
lean_inc(x_102);
if (lean_is_scalar(x_104)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_104;
}
lean_ctor_set(x_110, 0, x_102);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_ctor_get(x_101, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_101, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_101, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_101, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_101, 4);
lean_inc(x_115);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 lean_ctor_release(x_101, 4);
 x_116 = x_101;
} else {
 lean_dec_ref(x_101);
 x_116 = lean_box(0);
}
x_117 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_115, x_56, x_110);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 5, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_111);
lean_ctor_set(x_118, 1, x_112);
lean_ctor_set(x_118, 2, x_113);
lean_ctor_set(x_118, 3, x_114);
lean_ctor_set(x_118, 4, x_117);
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_47, x_51, x_102, x_119, x_2, x_118);
lean_dec(x_102);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_57);
if (x_121 == 0)
{
return x_57;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_57, 0);
x_123 = lean_ctor_get(x_57, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_57);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_52, 0);
x_126 = lean_ctor_get(x_52, 2);
x_127 = lean_ctor_get(x_52, 3);
x_128 = lean_ctor_get(x_52, 4);
x_129 = lean_ctor_get(x_52, 5);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_52);
x_130 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_10);
lean_ctor_set(x_130, 2, x_126);
lean_ctor_set(x_130, 3, x_127);
lean_ctor_set(x_130, 4, x_128);
lean_ctor_set(x_130, 5, x_129);
lean_ctor_set(x_40, 0, x_130);
x_131 = lean_ctor_get(x_1, 1);
lean_inc(x_131);
lean_dec(x_1);
lean_inc(x_2);
x_132 = l_Lean_Meta_SynthInstance_getEntry(x_131, x_2, x_40);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_140; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_133, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_138 = x_133;
} else {
 lean_dec_ref(x_133);
 x_138 = lean_box(0);
}
x_139 = l_Lean_Meta_SynthInstance_isNewAnswer(x_137, x_53);
x_140 = l_coeDecidableEq(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_131);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_2);
x_141 = lean_box(0);
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_135;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_134);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_135);
x_143 = lean_array_push(x_137, x_53);
lean_inc(x_136);
if (lean_is_scalar(x_138)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_138;
}
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_ctor_get(x_134, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_134, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_134, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_134, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_134, 4);
lean_inc(x_149);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 lean_ctor_release(x_134, 2);
 lean_ctor_release(x_134, 3);
 lean_ctor_release(x_134, 4);
 x_150 = x_134;
} else {
 lean_dec_ref(x_134);
 x_150 = lean_box(0);
}
x_151 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_149, x_131, x_144);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 5, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_145);
lean_ctor_set(x_152, 1, x_146);
lean_ctor_set(x_152, 2, x_147);
lean_ctor_set(x_152, 3, x_148);
lean_ctor_set(x_152, 4, x_151);
x_153 = lean_unsigned_to_nat(0u);
x_154 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_47, x_51, x_136, x_153, x_2, x_152);
lean_dec(x_136);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_131);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_2);
x_155 = lean_ctor_get(x_132, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_132, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_157 = x_132;
} else {
 lean_dec_ref(x_132);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_47);
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_ctor_get(x_50, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_50, 1);
lean_inc(x_160);
lean_dec(x_50);
lean_ctor_set(x_40, 0, x_160);
x_11 = x_159;
x_12 = x_40;
goto block_39;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_161 = lean_ctor_get(x_40, 0);
x_162 = lean_ctor_get(x_40, 1);
x_163 = lean_ctor_get(x_40, 2);
x_164 = lean_ctor_get(x_40, 3);
x_165 = lean_ctor_get(x_40, 4);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_40);
x_166 = l_Lean_Meta_instantiateMVars(x_6, x_2, x_161);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_Meta_abstractMVars(x_167, x_2, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 2);
lean_inc(x_172);
lean_inc(x_2);
x_173 = l_Lean_Meta_inferType(x_172, x_2, x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
lean_inc(x_174);
lean_inc(x_170);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_170);
lean_ctor_set(x_176, 1, x_174);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_175, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_175, 3);
lean_inc(x_179);
x_180 = lean_ctor_get(x_175, 4);
lean_inc(x_180);
x_181 = lean_ctor_get(x_175, 5);
lean_inc(x_181);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 lean_ctor_release(x_175, 2);
 lean_ctor_release(x_175, 3);
 lean_ctor_release(x_175, 4);
 lean_ctor_release(x_175, 5);
 x_182 = x_175;
} else {
 lean_dec_ref(x_175);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(0, 6, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_177);
lean_ctor_set(x_183, 1, x_10);
lean_ctor_set(x_183, 2, x_178);
lean_ctor_set(x_183, 3, x_179);
lean_ctor_set(x_183, 4, x_180);
lean_ctor_set(x_183, 5, x_181);
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_162);
lean_ctor_set(x_184, 2, x_163);
lean_ctor_set(x_184, 3, x_164);
lean_ctor_set(x_184, 4, x_165);
x_185 = lean_ctor_get(x_1, 1);
lean_inc(x_185);
lean_dec(x_1);
lean_inc(x_2);
x_186 = l_Lean_Meta_SynthInstance_getEntry(x_185, x_2, x_184);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_189 = x_186;
} else {
 lean_dec_ref(x_186);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_192 = x_187;
} else {
 lean_dec_ref(x_187);
 x_192 = lean_box(0);
}
x_193 = l_Lean_Meta_SynthInstance_isNewAnswer(x_191, x_176);
x_194 = l_coeDecidableEq(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_174);
lean_dec(x_170);
lean_dec(x_2);
x_195 = lean_box(0);
if (lean_is_scalar(x_189)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_189;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_188);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_189);
x_197 = lean_array_push(x_191, x_176);
lean_inc(x_190);
if (lean_is_scalar(x_192)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_192;
}
lean_ctor_set(x_198, 0, x_190);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_ctor_get(x_188, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_188, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_188, 2);
lean_inc(x_201);
x_202 = lean_ctor_get(x_188, 3);
lean_inc(x_202);
x_203 = lean_ctor_get(x_188, 4);
lean_inc(x_203);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 x_204 = x_188;
} else {
 lean_dec_ref(x_188);
 x_204 = lean_box(0);
}
x_205 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_203, x_185, x_198);
if (lean_is_scalar(x_204)) {
 x_206 = lean_alloc_ctor(0, 5, 0);
} else {
 x_206 = x_204;
}
lean_ctor_set(x_206, 0, x_199);
lean_ctor_set(x_206, 1, x_200);
lean_ctor_set(x_206, 2, x_201);
lean_ctor_set(x_206, 3, x_202);
lean_ctor_set(x_206, 4, x_205);
x_207 = lean_unsigned_to_nat(0u);
x_208 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_170, x_174, x_190, x_207, x_2, x_206);
lean_dec(x_190);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_174);
lean_dec(x_170);
lean_dec(x_2);
x_209 = lean_ctor_get(x_186, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_186, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_211 = x_186;
} else {
 lean_dec_ref(x_186);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_170);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_173, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_173, 1);
lean_inc(x_214);
lean_dec(x_173);
x_215 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_162);
lean_ctor_set(x_215, 2, x_163);
lean_ctor_set(x_215, 3, x_164);
lean_ctor_set(x_215, 4, x_165);
x_11 = x_213;
x_12 = x_215;
goto block_39;
}
}
}
block_246:
{
if (x_217 == 0)
{
x_40 = x_218;
goto block_216;
}
else
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_2);
lean_inc(x_6);
x_221 = l_Lean_Meta_inferType(x_6, x_2, x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
lean_ctor_set(x_218, 0, x_223);
x_224 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_224, 0, x_222);
x_225 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_226 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_225, x_224, x_2, x_218);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_40 = x_227;
goto block_216;
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_228 = lean_ctor_get(x_221, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_221, 1);
lean_inc(x_229);
lean_dec(x_221);
lean_ctor_set(x_218, 0, x_229);
x_11 = x_228;
x_12 = x_218;
goto block_39;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_230 = lean_ctor_get(x_218, 0);
x_231 = lean_ctor_get(x_218, 1);
x_232 = lean_ctor_get(x_218, 2);
x_233 = lean_ctor_get(x_218, 3);
x_234 = lean_ctor_get(x_218, 4);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_218);
lean_inc(x_2);
lean_inc(x_6);
x_235 = l_Lean_Meta_inferType(x_6, x_2, x_230);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_231);
lean_ctor_set(x_238, 2, x_232);
lean_ctor_set(x_238, 3, x_233);
lean_ctor_set(x_238, 4, x_234);
x_239 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_239, 0, x_236);
x_240 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_241 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_240, x_239, x_2, x_238);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
x_40 = x_242;
goto block_216;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_243 = lean_ctor_get(x_235, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_235, 1);
lean_inc(x_244);
lean_dec(x_235);
x_245 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_231);
lean_ctor_set(x_245, 2, x_232);
lean_ctor_set(x_245, 3, x_233);
lean_ctor_set(x_245, 4, x_234);
x_11 = x_243;
x_12 = x_245;
goto block_39;
}
}
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_290; uint8_t x_348; lean_object* x_349; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_266 = lean_ctor_get(x_4, 0);
x_267 = lean_ctor_get(x_4, 1);
x_268 = lean_ctor_get(x_4, 2);
x_269 = lean_ctor_get(x_4, 3);
x_270 = lean_ctor_get(x_4, 4);
x_271 = lean_ctor_get(x_4, 5);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_4);
x_368 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_368, 0, x_266);
lean_ctor_set(x_368, 1, x_5);
lean_ctor_set(x_368, 2, x_268);
lean_ctor_set(x_368, 3, x_269);
lean_ctor_set(x_368, 4, x_270);
lean_ctor_set(x_368, 5, x_271);
lean_ctor_set(x_3, 0, x_368);
x_369 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_3);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get_uint8(x_370, sizeof(void*)*1);
lean_dec(x_370);
if (x_371 == 0)
{
lean_object* x_372; uint8_t x_373; 
x_372 = lean_ctor_get(x_369, 1);
lean_inc(x_372);
lean_dec(x_369);
x_373 = l_String_posOfAux___main___closed__2;
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; 
x_374 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_375 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_374, x_2, x_372);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
x_378 = lean_unbox(x_376);
lean_dec(x_376);
x_348 = x_378;
x_349 = x_377;
goto block_367;
}
else
{
uint8_t x_379; 
x_379 = 0;
x_348 = x_379;
x_349 = x_372;
goto block_367;
}
}
else
{
lean_object* x_380; uint8_t x_381; 
x_380 = lean_ctor_get(x_369, 1);
lean_inc(x_380);
lean_dec(x_369);
x_381 = l_String_posOfAux___main___closed__1;
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; 
x_382 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_383 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_382, x_2, x_380);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_386 = lean_unbox(x_384);
lean_dec(x_384);
x_348 = x_386;
x_349 = x_385;
goto block_367;
}
else
{
uint8_t x_387; 
x_387 = 0;
x_348 = x_387;
x_349 = x_380;
goto block_367;
}
}
block_289:
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
x_276 = lean_ctor_get(x_273, 2);
lean_inc(x_276);
x_277 = lean_ctor_get(x_273, 3);
lean_inc(x_277);
x_278 = lean_ctor_get(x_273, 4);
lean_inc(x_278);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 lean_ctor_release(x_273, 2);
 lean_ctor_release(x_273, 3);
 lean_ctor_release(x_273, 4);
 x_279 = x_273;
} else {
 lean_dec_ref(x_273);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_274, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_274, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_274, 3);
lean_inc(x_282);
x_283 = lean_ctor_get(x_274, 4);
lean_inc(x_283);
x_284 = lean_ctor_get(x_274, 5);
lean_inc(x_284);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 lean_ctor_release(x_274, 2);
 lean_ctor_release(x_274, 3);
 lean_ctor_release(x_274, 4);
 lean_ctor_release(x_274, 5);
 x_285 = x_274;
} else {
 lean_dec_ref(x_274);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(0, 6, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_280);
lean_ctor_set(x_286, 1, x_267);
lean_ctor_set(x_286, 2, x_281);
lean_ctor_set(x_286, 3, x_282);
lean_ctor_set(x_286, 4, x_283);
lean_ctor_set(x_286, 5, x_284);
if (lean_is_scalar(x_279)) {
 x_287 = lean_alloc_ctor(0, 5, 0);
} else {
 x_287 = x_279;
}
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_275);
lean_ctor_set(x_287, 2, x_276);
lean_ctor_set(x_287, 3, x_277);
lean_ctor_set(x_287, 4, x_278);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_272);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
block_347:
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
x_293 = lean_ctor_get(x_290, 2);
lean_inc(x_293);
x_294 = lean_ctor_get(x_290, 3);
lean_inc(x_294);
x_295 = lean_ctor_get(x_290, 4);
lean_inc(x_295);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 lean_ctor_release(x_290, 2);
 lean_ctor_release(x_290, 3);
 lean_ctor_release(x_290, 4);
 x_296 = x_290;
} else {
 lean_dec_ref(x_290);
 x_296 = lean_box(0);
}
x_297 = l_Lean_Meta_instantiateMVars(x_6, x_2, x_291);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = l_Lean_Meta_abstractMVars(x_298, x_2, x_299);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_ctor_get(x_301, 2);
lean_inc(x_303);
lean_inc(x_2);
x_304 = l_Lean_Meta_inferType(x_303, x_2, x_302);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
lean_inc(x_305);
lean_inc(x_301);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_301);
lean_ctor_set(x_307, 1, x_305);
x_308 = lean_ctor_get(x_306, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_306, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_306, 3);
lean_inc(x_310);
x_311 = lean_ctor_get(x_306, 4);
lean_inc(x_311);
x_312 = lean_ctor_get(x_306, 5);
lean_inc(x_312);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 lean_ctor_release(x_306, 2);
 lean_ctor_release(x_306, 3);
 lean_ctor_release(x_306, 4);
 lean_ctor_release(x_306, 5);
 x_313 = x_306;
} else {
 lean_dec_ref(x_306);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(0, 6, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_308);
lean_ctor_set(x_314, 1, x_267);
lean_ctor_set(x_314, 2, x_309);
lean_ctor_set(x_314, 3, x_310);
lean_ctor_set(x_314, 4, x_311);
lean_ctor_set(x_314, 5, x_312);
if (lean_is_scalar(x_296)) {
 x_315 = lean_alloc_ctor(0, 5, 0);
} else {
 x_315 = x_296;
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_292);
lean_ctor_set(x_315, 2, x_293);
lean_ctor_set(x_315, 3, x_294);
lean_ctor_set(x_315, 4, x_295);
x_316 = lean_ctor_get(x_1, 1);
lean_inc(x_316);
lean_dec(x_1);
lean_inc(x_2);
x_317 = l_Lean_Meta_SynthInstance_getEntry(x_316, x_2, x_315);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; uint8_t x_325; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_320 = x_317;
} else {
 lean_dec_ref(x_317);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_318, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_323 = x_318;
} else {
 lean_dec_ref(x_318);
 x_323 = lean_box(0);
}
x_324 = l_Lean_Meta_SynthInstance_isNewAnswer(x_322, x_307);
x_325 = l_coeDecidableEq(x_324);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; 
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_316);
lean_dec(x_307);
lean_dec(x_305);
lean_dec(x_301);
lean_dec(x_2);
x_326 = lean_box(0);
if (lean_is_scalar(x_320)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_320;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_319);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_320);
x_328 = lean_array_push(x_322, x_307);
lean_inc(x_321);
if (lean_is_scalar(x_323)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_323;
}
lean_ctor_set(x_329, 0, x_321);
lean_ctor_set(x_329, 1, x_328);
x_330 = lean_ctor_get(x_319, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_319, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_319, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_319, 3);
lean_inc(x_333);
x_334 = lean_ctor_get(x_319, 4);
lean_inc(x_334);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 lean_ctor_release(x_319, 2);
 lean_ctor_release(x_319, 3);
 lean_ctor_release(x_319, 4);
 x_335 = x_319;
} else {
 lean_dec_ref(x_319);
 x_335 = lean_box(0);
}
x_336 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_334, x_316, x_329);
if (lean_is_scalar(x_335)) {
 x_337 = lean_alloc_ctor(0, 5, 0);
} else {
 x_337 = x_335;
}
lean_ctor_set(x_337, 0, x_330);
lean_ctor_set(x_337, 1, x_331);
lean_ctor_set(x_337, 2, x_332);
lean_ctor_set(x_337, 3, x_333);
lean_ctor_set(x_337, 4, x_336);
x_338 = lean_unsigned_to_nat(0u);
x_339 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_301, x_305, x_321, x_338, x_2, x_337);
lean_dec(x_321);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_316);
lean_dec(x_307);
lean_dec(x_305);
lean_dec(x_301);
lean_dec(x_2);
x_340 = lean_ctor_get(x_317, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_317, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_342 = x_317;
} else {
 lean_dec_ref(x_317);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(1, 2, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_341);
return x_343;
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_301);
lean_dec(x_2);
lean_dec(x_1);
x_344 = lean_ctor_get(x_304, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_304, 1);
lean_inc(x_345);
lean_dec(x_304);
if (lean_is_scalar(x_296)) {
 x_346 = lean_alloc_ctor(0, 5, 0);
} else {
 x_346 = x_296;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_292);
lean_ctor_set(x_346, 2, x_293);
lean_ctor_set(x_346, 3, x_294);
lean_ctor_set(x_346, 4, x_295);
x_272 = x_344;
x_273 = x_346;
goto block_289;
}
}
block_367:
{
if (x_348 == 0)
{
x_290 = x_349;
goto block_347;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_349, 2);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 3);
lean_inc(x_353);
x_354 = lean_ctor_get(x_349, 4);
lean_inc(x_354);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 lean_ctor_release(x_349, 4);
 x_355 = x_349;
} else {
 lean_dec_ref(x_349);
 x_355 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_6);
x_356 = l_Lean_Meta_inferType(x_6, x_2, x_350);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
if (lean_is_scalar(x_355)) {
 x_359 = lean_alloc_ctor(0, 5, 0);
} else {
 x_359 = x_355;
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_351);
lean_ctor_set(x_359, 2, x_352);
lean_ctor_set(x_359, 3, x_353);
lean_ctor_set(x_359, 4, x_354);
x_360 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_360, 0, x_357);
x_361 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_362 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_361, x_360, x_2, x_359);
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
lean_dec(x_362);
x_290 = x_363;
goto block_347;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_364 = lean_ctor_get(x_356, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_356, 1);
lean_inc(x_365);
lean_dec(x_356);
if (lean_is_scalar(x_355)) {
 x_366 = lean_alloc_ctor(0, 5, 0);
} else {
 x_366 = x_355;
}
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_351);
lean_ctor_set(x_366, 2, x_352);
lean_ctor_set(x_366, 3, x_353);
lean_ctor_set(x_366, 4, x_354);
x_272 = x_364;
x_273 = x_366;
goto block_289;
}
}
}
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_417; uint8_t x_475; lean_object* x_476; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; 
x_388 = lean_ctor_get(x_3, 1);
x_389 = lean_ctor_get(x_3, 2);
x_390 = lean_ctor_get(x_3, 3);
x_391 = lean_ctor_get(x_3, 4);
lean_inc(x_391);
lean_inc(x_390);
lean_inc(x_389);
lean_inc(x_388);
lean_dec(x_3);
x_392 = lean_ctor_get(x_4, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_4, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_4, 2);
lean_inc(x_394);
x_395 = lean_ctor_get(x_4, 3);
lean_inc(x_395);
x_396 = lean_ctor_get(x_4, 4);
lean_inc(x_396);
x_397 = lean_ctor_get(x_4, 5);
lean_inc(x_397);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_398 = x_4;
} else {
 lean_dec_ref(x_4);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_495 = lean_alloc_ctor(0, 6, 0);
} else {
 x_495 = x_398;
}
lean_ctor_set(x_495, 0, x_392);
lean_ctor_set(x_495, 1, x_5);
lean_ctor_set(x_495, 2, x_394);
lean_ctor_set(x_495, 3, x_395);
lean_ctor_set(x_495, 4, x_396);
lean_ctor_set(x_495, 5, x_397);
x_496 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_388);
lean_ctor_set(x_496, 2, x_389);
lean_ctor_set(x_496, 3, x_390);
lean_ctor_set(x_496, 4, x_391);
x_497 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_496);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get_uint8(x_498, sizeof(void*)*1);
lean_dec(x_498);
if (x_499 == 0)
{
lean_object* x_500; uint8_t x_501; 
x_500 = lean_ctor_get(x_497, 1);
lean_inc(x_500);
lean_dec(x_497);
x_501 = l_String_posOfAux___main___closed__2;
if (x_501 == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; 
x_502 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_503 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_502, x_2, x_500);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_506 = lean_unbox(x_504);
lean_dec(x_504);
x_475 = x_506;
x_476 = x_505;
goto block_494;
}
else
{
uint8_t x_507; 
x_507 = 0;
x_475 = x_507;
x_476 = x_500;
goto block_494;
}
}
else
{
lean_object* x_508; uint8_t x_509; 
x_508 = lean_ctor_get(x_497, 1);
lean_inc(x_508);
lean_dec(x_497);
x_509 = l_String_posOfAux___main___closed__1;
if (x_509 == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_514; 
x_510 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_511 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_510, x_2, x_508);
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_514 = lean_unbox(x_512);
lean_dec(x_512);
x_475 = x_514;
x_476 = x_513;
goto block_494;
}
else
{
uint8_t x_515; 
x_515 = 0;
x_475 = x_515;
x_476 = x_508;
goto block_494;
}
}
block_416:
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_400, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_400, 3);
lean_inc(x_404);
x_405 = lean_ctor_get(x_400, 4);
lean_inc(x_405);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 lean_ctor_release(x_400, 2);
 lean_ctor_release(x_400, 3);
 lean_ctor_release(x_400, 4);
 x_406 = x_400;
} else {
 lean_dec_ref(x_400);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_401, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_401, 2);
lean_inc(x_408);
x_409 = lean_ctor_get(x_401, 3);
lean_inc(x_409);
x_410 = lean_ctor_get(x_401, 4);
lean_inc(x_410);
x_411 = lean_ctor_get(x_401, 5);
lean_inc(x_411);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 lean_ctor_release(x_401, 2);
 lean_ctor_release(x_401, 3);
 lean_ctor_release(x_401, 4);
 lean_ctor_release(x_401, 5);
 x_412 = x_401;
} else {
 lean_dec_ref(x_401);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(0, 6, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_393);
lean_ctor_set(x_413, 2, x_408);
lean_ctor_set(x_413, 3, x_409);
lean_ctor_set(x_413, 4, x_410);
lean_ctor_set(x_413, 5, x_411);
if (lean_is_scalar(x_406)) {
 x_414 = lean_alloc_ctor(0, 5, 0);
} else {
 x_414 = x_406;
}
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_402);
lean_ctor_set(x_414, 2, x_403);
lean_ctor_set(x_414, 3, x_404);
lean_ctor_set(x_414, 4, x_405);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_399);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
block_474:
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_417, 2);
lean_inc(x_420);
x_421 = lean_ctor_get(x_417, 3);
lean_inc(x_421);
x_422 = lean_ctor_get(x_417, 4);
lean_inc(x_422);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 lean_ctor_release(x_417, 4);
 x_423 = x_417;
} else {
 lean_dec_ref(x_417);
 x_423 = lean_box(0);
}
x_424 = l_Lean_Meta_instantiateMVars(x_6, x_2, x_418);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = l_Lean_Meta_abstractMVars(x_425, x_2, x_426);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = lean_ctor_get(x_428, 2);
lean_inc(x_430);
lean_inc(x_2);
x_431 = l_Lean_Meta_inferType(x_430, x_2, x_429);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
lean_inc(x_432);
lean_inc(x_428);
x_434 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_434, 0, x_428);
lean_ctor_set(x_434, 1, x_432);
x_435 = lean_ctor_get(x_433, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_433, 2);
lean_inc(x_436);
x_437 = lean_ctor_get(x_433, 3);
lean_inc(x_437);
x_438 = lean_ctor_get(x_433, 4);
lean_inc(x_438);
x_439 = lean_ctor_get(x_433, 5);
lean_inc(x_439);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 lean_ctor_release(x_433, 4);
 lean_ctor_release(x_433, 5);
 x_440 = x_433;
} else {
 lean_dec_ref(x_433);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(0, 6, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_435);
lean_ctor_set(x_441, 1, x_393);
lean_ctor_set(x_441, 2, x_436);
lean_ctor_set(x_441, 3, x_437);
lean_ctor_set(x_441, 4, x_438);
lean_ctor_set(x_441, 5, x_439);
if (lean_is_scalar(x_423)) {
 x_442 = lean_alloc_ctor(0, 5, 0);
} else {
 x_442 = x_423;
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_419);
lean_ctor_set(x_442, 2, x_420);
lean_ctor_set(x_442, 3, x_421);
lean_ctor_set(x_442, 4, x_422);
x_443 = lean_ctor_get(x_1, 1);
lean_inc(x_443);
lean_dec(x_1);
lean_inc(x_2);
x_444 = l_Lean_Meta_SynthInstance_getEntry(x_443, x_2, x_442);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; uint8_t x_452; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_447 = x_444;
} else {
 lean_dec_ref(x_444);
 x_447 = lean_box(0);
}
x_448 = lean_ctor_get(x_445, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_445, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_450 = x_445;
} else {
 lean_dec_ref(x_445);
 x_450 = lean_box(0);
}
x_451 = l_Lean_Meta_SynthInstance_isNewAnswer(x_449, x_434);
x_452 = l_coeDecidableEq(x_451);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; 
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_443);
lean_dec(x_434);
lean_dec(x_432);
lean_dec(x_428);
lean_dec(x_2);
x_453 = lean_box(0);
if (lean_is_scalar(x_447)) {
 x_454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_454 = x_447;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_446);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_dec(x_447);
x_455 = lean_array_push(x_449, x_434);
lean_inc(x_448);
if (lean_is_scalar(x_450)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_450;
}
lean_ctor_set(x_456, 0, x_448);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_ctor_get(x_446, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_446, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_446, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_446, 3);
lean_inc(x_460);
x_461 = lean_ctor_get(x_446, 4);
lean_inc(x_461);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 lean_ctor_release(x_446, 2);
 lean_ctor_release(x_446, 3);
 lean_ctor_release(x_446, 4);
 x_462 = x_446;
} else {
 lean_dec_ref(x_446);
 x_462 = lean_box(0);
}
x_463 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_461, x_443, x_456);
if (lean_is_scalar(x_462)) {
 x_464 = lean_alloc_ctor(0, 5, 0);
} else {
 x_464 = x_462;
}
lean_ctor_set(x_464, 0, x_457);
lean_ctor_set(x_464, 1, x_458);
lean_ctor_set(x_464, 2, x_459);
lean_ctor_set(x_464, 3, x_460);
lean_ctor_set(x_464, 4, x_463);
x_465 = lean_unsigned_to_nat(0u);
x_466 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_428, x_432, x_448, x_465, x_2, x_464);
lean_dec(x_448);
return x_466;
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_443);
lean_dec(x_434);
lean_dec(x_432);
lean_dec(x_428);
lean_dec(x_2);
x_467 = lean_ctor_get(x_444, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_444, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_469 = x_444;
} else {
 lean_dec_ref(x_444);
 x_469 = lean_box(0);
}
if (lean_is_scalar(x_469)) {
 x_470 = lean_alloc_ctor(1, 2, 0);
} else {
 x_470 = x_469;
}
lean_ctor_set(x_470, 0, x_467);
lean_ctor_set(x_470, 1, x_468);
return x_470;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_428);
lean_dec(x_2);
lean_dec(x_1);
x_471 = lean_ctor_get(x_431, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_431, 1);
lean_inc(x_472);
lean_dec(x_431);
if (lean_is_scalar(x_423)) {
 x_473 = lean_alloc_ctor(0, 5, 0);
} else {
 x_473 = x_423;
}
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_419);
lean_ctor_set(x_473, 2, x_420);
lean_ctor_set(x_473, 3, x_421);
lean_ctor_set(x_473, 4, x_422);
x_399 = x_471;
x_400 = x_473;
goto block_416;
}
}
block_494:
{
if (x_475 == 0)
{
x_417 = x_476;
goto block_474;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_476, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_476, 3);
lean_inc(x_480);
x_481 = lean_ctor_get(x_476, 4);
lean_inc(x_481);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 lean_ctor_release(x_476, 4);
 x_482 = x_476;
} else {
 lean_dec_ref(x_476);
 x_482 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_6);
x_483 = l_Lean_Meta_inferType(x_6, x_2, x_477);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_483, 1);
lean_inc(x_485);
lean_dec(x_483);
if (lean_is_scalar(x_482)) {
 x_486 = lean_alloc_ctor(0, 5, 0);
} else {
 x_486 = x_482;
}
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_478);
lean_ctor_set(x_486, 2, x_479);
lean_ctor_set(x_486, 3, x_480);
lean_ctor_set(x_486, 4, x_481);
x_487 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_487, 0, x_484);
x_488 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_489 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_488, x_487, x_2, x_486);
x_490 = lean_ctor_get(x_489, 1);
lean_inc(x_490);
lean_dec(x_489);
x_417 = x_490;
goto block_474;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_491 = lean_ctor_get(x_483, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_483, 1);
lean_inc(x_492);
lean_dec(x_483);
if (lean_is_scalar(x_482)) {
 x_493 = lean_alloc_ctor(0, 5, 0);
} else {
 x_493 = x_482;
}
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_478);
lean_ctor_set(x_493, 2, x_479);
lean_ctor_set(x_493, 3, x_480);
lean_ctor_set(x_493, 4, x_481);
x_399 = x_491;
x_400 = x_493;
goto block_416;
}
}
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
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
x_31 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_22, x_10, x_19);
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
x_35 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_22, x_10, x_34);
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
x_49 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_41, x_10, x_48);
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
x_67 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_58, x_10, x_66);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
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
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_142; lean_object* x_143; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_free_object(x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_11, x_15);
lean_dec(x_11);
x_17 = l_Lean_Expr_Inhabited;
x_18 = lean_array_get(x_17, x_10, x_16);
lean_dec(x_10);
x_151 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_6);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get_uint8(x_152, sizeof(void*)*1);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; 
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = l_String_posOfAux___main___closed__2;
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_156 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_157 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_156, x_1, x_154);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_unbox(x_158);
lean_dec(x_158);
x_142 = x_160;
x_143 = x_159;
goto block_150;
}
else
{
uint8_t x_161; 
x_161 = 0;
x_142 = x_161;
x_143 = x_154;
goto block_150;
}
}
else
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_ctor_get(x_151, 1);
lean_inc(x_162);
lean_dec(x_151);
x_163 = l_String_posOfAux___main___closed__1;
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_164 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_165 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_164, x_1, x_162);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_unbox(x_166);
lean_dec(x_166);
x_142 = x_168;
x_143 = x_167;
goto block_150;
}
else
{
uint8_t x_169; 
x_169 = 0;
x_142 = x_169;
x_143 = x_162;
goto block_150;
}
}
block_141:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 2);
x_22 = lean_array_get_size(x_21);
x_23 = lean_nat_sub(x_22, x_15);
x_24 = lean_nat_dec_lt(x_23, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_16);
lean_inc(x_1);
lean_inc(x_7);
x_25 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_18, x_1, x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_8);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
x_38 = l_Lean_Meta_SynthInstance_consume(x_37, x_1, x_34);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_25);
if (x_39 == 0)
{
return x_25;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_25, 0);
x_41 = lean_ctor_get(x_25, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_25);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_array_fget(x_21, x_23);
x_44 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_45 = lean_array_fset(x_21, x_23, x_44);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 4);
lean_dec(x_47);
lean_ctor_set(x_43, 4, x_16);
x_48 = lean_array_fset(x_45, x_23, x_43);
lean_dec(x_23);
lean_ctor_set(x_19, 2, x_48);
lean_inc(x_1);
lean_inc(x_7);
x_49 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_18, x_1, x_19);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_dec(x_49);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_7);
lean_ctor_set(x_61, 1, x_8);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
x_62 = l_Lean_Meta_SynthInstance_consume(x_61, x_1, x_58);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_49);
if (x_63 == 0)
{
return x_49;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_49, 0);
x_65 = lean_ctor_get(x_49, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_49);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_43, 0);
x_68 = lean_ctor_get(x_43, 1);
x_69 = lean_ctor_get(x_43, 2);
x_70 = lean_ctor_get(x_43, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_43);
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set(x_71, 4, x_16);
x_72 = lean_array_fset(x_45, x_23, x_71);
lean_dec(x_23);
lean_ctor_set(x_19, 2, x_72);
lean_inc(x_1);
lean_inc(x_7);
x_73 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_18, x_1, x_19);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
lean_dec(x_74);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
lean_dec(x_73);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_7);
lean_ctor_set(x_83, 1, x_8);
lean_ctor_set(x_83, 2, x_81);
lean_ctor_set(x_83, 3, x_82);
x_84 = l_Lean_Meta_SynthInstance_consume(x_83, x_1, x_80);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_85 = lean_ctor_get(x_73, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_87 = x_73;
} else {
 lean_dec_ref(x_73);
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
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_89 = lean_ctor_get(x_19, 0);
x_90 = lean_ctor_get(x_19, 1);
x_91 = lean_ctor_get(x_19, 2);
x_92 = lean_ctor_get(x_19, 3);
x_93 = lean_ctor_get(x_19, 4);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_19);
x_94 = lean_array_get_size(x_91);
x_95 = lean_nat_sub(x_94, x_15);
x_96 = lean_nat_dec_lt(x_95, x_94);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_16);
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_89);
lean_ctor_set(x_97, 1, x_90);
lean_ctor_set(x_97, 2, x_91);
lean_ctor_set(x_97, 3, x_92);
lean_ctor_set(x_97, 4, x_93);
lean_inc(x_1);
lean_inc(x_7);
x_98 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_18, x_1, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
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
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
lean_dec(x_99);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_108, 0, x_7);
lean_ctor_set(x_108, 1, x_8);
lean_ctor_set(x_108, 2, x_106);
lean_ctor_set(x_108, 3, x_107);
x_109 = l_Lean_Meta_SynthInstance_consume(x_108, x_1, x_105);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_110 = lean_ctor_get(x_98, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_98, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_112 = x_98;
} else {
 lean_dec_ref(x_98);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_114 = lean_array_fget(x_91, x_95);
x_115 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_116 = lean_array_fset(x_91, x_95, x_115);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 3);
lean_inc(x_120);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 x_121 = x_114;
} else {
 lean_dec_ref(x_114);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 5, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set(x_122, 1, x_118);
lean_ctor_set(x_122, 2, x_119);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_16);
x_123 = lean_array_fset(x_116, x_95, x_122);
lean_dec(x_95);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_89);
lean_ctor_set(x_124, 1, x_90);
lean_ctor_set(x_124, 2, x_123);
lean_ctor_set(x_124, 3, x_92);
lean_ctor_set(x_124, 4, x_93);
lean_inc(x_1);
lean_inc(x_7);
x_125 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_18, x_1, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = lean_box(0);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_127);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_126, 0);
lean_inc(x_131);
lean_dec(x_126);
x_132 = lean_ctor_get(x_125, 1);
lean_inc(x_132);
lean_dec(x_125);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_135, 0, x_7);
lean_ctor_set(x_135, 1, x_8);
lean_ctor_set(x_135, 2, x_133);
lean_ctor_set(x_135, 3, x_134);
x_136 = l_Lean_Meta_SynthInstance_consume(x_135, x_1, x_132);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_137 = lean_ctor_get(x_125, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_125, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_139 = x_125;
} else {
 lean_dec_ref(x_125);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
}
block_150:
{
if (x_142 == 0)
{
x_19 = x_143;
goto block_141;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_inc(x_18);
x_144 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_144, 0, x_18);
x_145 = l_Lean_Meta_SynthInstance_generate___closed__5;
x_146 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_148 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_147, x_146, x_1, x_143);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_19 = x_149;
goto block_141;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_6);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_6, 2);
x_172 = lean_array_pop(x_171);
lean_ctor_set(x_6, 2, x_172);
x_173 = lean_box(0);
lean_ctor_set(x_3, 0, x_173);
return x_3;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_174 = lean_ctor_get(x_6, 0);
x_175 = lean_ctor_get(x_6, 1);
x_176 = lean_ctor_get(x_6, 2);
x_177 = lean_ctor_get(x_6, 3);
x_178 = lean_ctor_get(x_6, 4);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_6);
x_179 = lean_array_pop(x_176);
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_174);
lean_ctor_set(x_180, 1, x_175);
lean_ctor_set(x_180, 2, x_179);
lean_ctor_set(x_180, 3, x_177);
lean_ctor_set(x_180, 4, x_178);
x_181 = lean_box(0);
lean_ctor_set(x_3, 1, x_180);
lean_ctor_set(x_3, 0, x_181);
return x_3;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
x_182 = lean_ctor_get(x_3, 0);
x_183 = lean_ctor_get(x_3, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_3);
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_182, 3);
lean_inc(x_187);
x_188 = lean_ctor_get(x_182, 4);
lean_inc(x_188);
lean_dec(x_182);
x_189 = lean_unsigned_to_nat(0u);
x_190 = lean_nat_dec_eq(x_188, x_189);
x_191 = l_coeDecidableEq(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_251; lean_object* x_252; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_192 = lean_unsigned_to_nat(1u);
x_193 = lean_nat_sub(x_188, x_192);
lean_dec(x_188);
x_194 = l_Lean_Expr_Inhabited;
x_195 = lean_array_get(x_194, x_187, x_193);
lean_dec(x_187);
x_260 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_183);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get_uint8(x_261, sizeof(void*)*1);
lean_dec(x_261);
if (x_262 == 0)
{
lean_object* x_263; uint8_t x_264; 
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
lean_dec(x_260);
x_264 = l_String_posOfAux___main___closed__2;
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_265 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_266 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_265, x_1, x_263);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_unbox(x_267);
lean_dec(x_267);
x_251 = x_269;
x_252 = x_268;
goto block_259;
}
else
{
uint8_t x_270; 
x_270 = 0;
x_251 = x_270;
x_252 = x_263;
goto block_259;
}
}
else
{
lean_object* x_271; uint8_t x_272; 
x_271 = lean_ctor_get(x_260, 1);
lean_inc(x_271);
lean_dec(x_260);
x_272 = l_String_posOfAux___main___closed__1;
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_274 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_273, x_1, x_271);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = lean_unbox(x_275);
lean_dec(x_275);
x_251 = x_277;
x_252 = x_276;
goto block_259;
}
else
{
uint8_t x_278; 
x_278 = 0;
x_251 = x_278;
x_252 = x_271;
goto block_259;
}
}
block_250:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 4);
lean_inc(x_201);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 x_202 = x_196;
} else {
 lean_dec_ref(x_196);
 x_202 = lean_box(0);
}
x_203 = lean_array_get_size(x_199);
x_204 = lean_nat_sub(x_203, x_192);
x_205 = lean_nat_dec_lt(x_204, x_203);
lean_dec(x_203);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_204);
lean_dec(x_193);
if (lean_is_scalar(x_202)) {
 x_206 = lean_alloc_ctor(0, 5, 0);
} else {
 x_206 = x_202;
}
lean_ctor_set(x_206, 0, x_197);
lean_ctor_set(x_206, 1, x_198);
lean_ctor_set(x_206, 2, x_199);
lean_ctor_set(x_206, 3, x_200);
lean_ctor_set(x_206, 4, x_201);
lean_inc(x_1);
lean_inc(x_184);
x_207 = l_Lean_Meta_SynthInstance_tryResolve(x_186, x_184, x_195, x_1, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_1);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_210 = x_207;
} else {
 lean_dec_ref(x_207);
 x_210 = lean_box(0);
}
x_211 = lean_box(0);
if (lean_is_scalar(x_210)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_210;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_209);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_208, 0);
lean_inc(x_213);
lean_dec(x_208);
x_214 = lean_ctor_get(x_207, 1);
lean_inc(x_214);
lean_dec(x_207);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_213, 1);
lean_inc(x_216);
lean_dec(x_213);
x_217 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_217, 0, x_184);
lean_ctor_set(x_217, 1, x_185);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_216);
x_218 = l_Lean_Meta_SynthInstance_consume(x_217, x_1, x_214);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_1);
x_219 = lean_ctor_get(x_207, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_207, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_221 = x_207;
} else {
 lean_dec_ref(x_207);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_223 = lean_array_fget(x_199, x_204);
x_224 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_225 = lean_array_fset(x_199, x_204, x_224);
x_226 = lean_ctor_get(x_223, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_223, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_223, 3);
lean_inc(x_229);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 lean_ctor_release(x_223, 2);
 lean_ctor_release(x_223, 3);
 lean_ctor_release(x_223, 4);
 x_230 = x_223;
} else {
 lean_dec_ref(x_223);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(0, 5, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_226);
lean_ctor_set(x_231, 1, x_227);
lean_ctor_set(x_231, 2, x_228);
lean_ctor_set(x_231, 3, x_229);
lean_ctor_set(x_231, 4, x_193);
x_232 = lean_array_fset(x_225, x_204, x_231);
lean_dec(x_204);
if (lean_is_scalar(x_202)) {
 x_233 = lean_alloc_ctor(0, 5, 0);
} else {
 x_233 = x_202;
}
lean_ctor_set(x_233, 0, x_197);
lean_ctor_set(x_233, 1, x_198);
lean_ctor_set(x_233, 2, x_232);
lean_ctor_set(x_233, 3, x_200);
lean_ctor_set(x_233, 4, x_201);
lean_inc(x_1);
lean_inc(x_184);
x_234 = l_Lean_Meta_SynthInstance_tryResolve(x_186, x_184, x_195, x_1, x_233);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_1);
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
x_238 = lean_box(0);
if (lean_is_scalar(x_237)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_237;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_236);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_240 = lean_ctor_get(x_235, 0);
lean_inc(x_240);
lean_dec(x_235);
x_241 = lean_ctor_get(x_234, 1);
lean_inc(x_241);
lean_dec(x_234);
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
lean_dec(x_240);
x_244 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_244, 0, x_184);
lean_ctor_set(x_244, 1, x_185);
lean_ctor_set(x_244, 2, x_242);
lean_ctor_set(x_244, 3, x_243);
x_245 = l_Lean_Meta_SynthInstance_consume(x_244, x_1, x_241);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_1);
x_246 = lean_ctor_get(x_234, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_234, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_248 = x_234;
} else {
 lean_dec_ref(x_234);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
}
block_259:
{
if (x_251 == 0)
{
x_196 = x_252;
goto block_250;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_inc(x_195);
x_253 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_253, 0, x_195);
x_254 = l_Lean_Meta_SynthInstance_generate___closed__5;
x_255 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
x_256 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_257 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_256, x_255, x_1, x_252);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec(x_257);
x_196 = x_258;
goto block_250;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_1);
x_279 = lean_ctor_get(x_183, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_183, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_183, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_183, 3);
lean_inc(x_282);
x_283 = lean_ctor_get(x_183, 4);
lean_inc(x_283);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 lean_ctor_release(x_183, 4);
 x_284 = x_183;
} else {
 lean_dec_ref(x_183);
 x_284 = lean_box(0);
}
x_285 = lean_array_pop(x_281);
if (lean_is_scalar(x_284)) {
 x_286 = lean_alloc_ctor(0, 5, 0);
} else {
 x_286 = x_284;
}
lean_ctor_set(x_286, 0, x_279);
lean_ctor_set(x_286, 1, x_280);
lean_ctor_set(x_286, 2, x_285);
lean_ctor_set(x_286, 3, x_282);
lean_ctor_set(x_286, 4, x_283);
x_287 = lean_box(0);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
return x_288;
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
x_2 = lean_unsigned_to_nat(416u);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 2);
lean_inc(x_16);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_17 = x_5;
} else {
 lean_dec_ref(x_5);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
lean_inc(x_1);
lean_inc(x_18);
x_20 = l_Lean_Meta_SynthInstance_tryAnswer(x_16, x_18, x_13, x_1, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_29 = x_20;
} else {
 lean_dec_ref(x_20);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_28, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_67; lean_object* x_68; uint8_t x_96; lean_object* x_97; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_ctor_set(x_30, 1, x_31);
x_145 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_28);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_146, sizeof(void*)*1);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = l_String_posOfAux___main___closed__2;
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_151 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_150, x_1, x_148);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_unbox(x_152);
lean_dec(x_152);
x_96 = x_154;
x_97 = x_153;
goto block_144;
}
else
{
uint8_t x_155; 
x_155 = 0;
x_96 = x_155;
x_97 = x_148;
goto block_144;
}
}
else
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_145, 1);
lean_inc(x_156);
lean_dec(x_145);
x_157 = l_String_posOfAux___main___closed__1;
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_158 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_159 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_158, x_1, x_156);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_unbox(x_160);
lean_dec(x_160);
x_96 = x_162;
x_97 = x_161;
goto block_144;
}
else
{
uint8_t x_163; 
x_163 = 0;
x_96 = x_163;
x_97 = x_156;
goto block_144;
}
}
block_66:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_dec(x_40);
lean_ctor_set(x_38, 1, x_35);
if (lean_is_scalar(x_17)) {
 x_41 = lean_alloc_ctor(0, 4, 0);
} else {
 x_41 = x_17;
}
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_15);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 3, x_19);
x_42 = l_Lean_Meta_SynthInstance_consume(x_41, x_1, x_36);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 2);
x_45 = lean_ctor_get(x_38, 3);
x_46 = lean_ctor_get(x_38, 4);
x_47 = lean_ctor_get(x_38, 5);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_48 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_35);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set(x_48, 3, x_45);
lean_ctor_set(x_48, 4, x_46);
lean_ctor_set(x_48, 5, x_47);
lean_ctor_set(x_36, 0, x_48);
if (lean_is_scalar(x_17)) {
 x_49 = lean_alloc_ctor(0, 4, 0);
} else {
 x_49 = x_17;
}
lean_ctor_set(x_49, 0, x_14);
lean_ctor_set(x_49, 1, x_15);
lean_ctor_set(x_49, 2, x_31);
lean_ctor_set(x_49, 3, x_19);
x_50 = l_Lean_Meta_SynthInstance_consume(x_49, x_1, x_36);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get(x_36, 0);
x_52 = lean_ctor_get(x_36, 1);
x_53 = lean_ctor_get(x_36, 2);
x_54 = lean_ctor_get(x_36, 3);
x_55 = lean_ctor_get(x_36, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_36);
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_51, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 3);
lean_inc(x_58);
x_59 = lean_ctor_get(x_51, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_51, 5);
lean_inc(x_60);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 lean_ctor_release(x_51, 4);
 lean_ctor_release(x_51, 5);
 x_61 = x_51;
} else {
 lean_dec_ref(x_51);
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
if (lean_is_scalar(x_17)) {
 x_64 = lean_alloc_ctor(0, 4, 0);
} else {
 x_64 = x_17;
}
lean_ctor_set(x_64, 0, x_14);
lean_ctor_set(x_64, 1, x_15);
lean_ctor_set(x_64, 2, x_31);
lean_ctor_set(x_64, 3, x_19);
x_65 = l_Lean_Meta_SynthInstance_consume(x_64, x_1, x_63);
return x_65;
}
}
block_95:
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 1);
lean_dec(x_72);
lean_ctor_set(x_70, 1, x_35);
if (lean_is_scalar(x_29)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_29;
 lean_ctor_set_tag(x_73, 1);
}
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_68);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 2);
x_76 = lean_ctor_get(x_70, 3);
x_77 = lean_ctor_get(x_70, 4);
x_78 = lean_ctor_get(x_70, 5);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_79 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_35);
lean_ctor_set(x_79, 2, x_75);
lean_ctor_set(x_79, 3, x_76);
lean_ctor_set(x_79, 4, x_77);
lean_ctor_set(x_79, 5, x_78);
lean_ctor_set(x_68, 0, x_79);
if (lean_is_scalar(x_29)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_29;
 lean_ctor_set_tag(x_80, 1);
}
lean_ctor_set(x_80, 0, x_67);
lean_ctor_set(x_80, 1, x_68);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_81 = lean_ctor_get(x_68, 0);
x_82 = lean_ctor_get(x_68, 1);
x_83 = lean_ctor_get(x_68, 2);
x_84 = lean_ctor_get(x_68, 3);
x_85 = lean_ctor_get(x_68, 4);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_68);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_81, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_81, 5);
lean_inc(x_90);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 lean_ctor_release(x_81, 5);
 x_91 = x_81;
} else {
 lean_dec_ref(x_81);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 6, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_86);
lean_ctor_set(x_92, 1, x_35);
lean_ctor_set(x_92, 2, x_87);
lean_ctor_set(x_92, 3, x_88);
lean_ctor_set(x_92, 4, x_89);
lean_ctor_set(x_92, 5, x_90);
x_93 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_82);
lean_ctor_set(x_93, 2, x_83);
lean_ctor_set(x_93, 3, x_84);
lean_ctor_set(x_93, 4, x_85);
if (lean_is_scalar(x_29)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_29;
 lean_ctor_set_tag(x_94, 1);
}
lean_ctor_set(x_94, 0, x_67);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
block_144:
{
if (x_96 == 0)
{
lean_dec(x_29);
lean_dec(x_18);
x_36 = x_97;
goto block_66;
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_1);
lean_inc(x_14);
x_100 = l_Lean_Meta_inferType(x_14, x_1, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_1);
x_103 = l_Lean_Meta_inferType(x_18, x_1, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_29);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_ctor_set(x_97, 0, x_105);
x_106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_107 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_108 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_109, 0, x_104);
x_110 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_112 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_111, x_110, x_1, x_97);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_36 = x_113;
goto block_66;
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_101);
lean_dec(x_31);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_114 = lean_ctor_get(x_103, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_103, 1);
lean_inc(x_115);
lean_dec(x_103);
lean_ctor_set(x_97, 0, x_115);
x_67 = x_114;
x_68 = x_97;
goto block_95;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_31);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_116 = lean_ctor_get(x_100, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_100, 1);
lean_inc(x_117);
lean_dec(x_100);
lean_ctor_set(x_97, 0, x_117);
x_67 = x_116;
x_68 = x_97;
goto block_95;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_97, 0);
x_119 = lean_ctor_get(x_97, 1);
x_120 = lean_ctor_get(x_97, 2);
x_121 = lean_ctor_get(x_97, 3);
x_122 = lean_ctor_get(x_97, 4);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_97);
lean_inc(x_1);
lean_inc(x_14);
x_123 = l_Lean_Meta_inferType(x_14, x_1, x_118);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_1);
x_126 = l_Lean_Meta_inferType(x_18, x_1, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_29);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_119);
lean_ctor_set(x_129, 2, x_120);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set(x_129, 4, x_122);
x_130 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_130, 0, x_124);
x_131 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_132 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_133, 0, x_127);
x_134 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_136 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_135, x_134, x_1, x_129);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_36 = x_137;
goto block_66;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_124);
lean_dec(x_31);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_138 = lean_ctor_get(x_126, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_126, 1);
lean_inc(x_139);
lean_dec(x_126);
x_140 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_119);
lean_ctor_set(x_140, 2, x_120);
lean_ctor_set(x_140, 3, x_121);
lean_ctor_set(x_140, 4, x_122);
x_67 = x_138;
x_68 = x_140;
goto block_95;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_31);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_141 = lean_ctor_get(x_123, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_123, 1);
lean_inc(x_142);
lean_dec(x_123);
x_143 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_119);
lean_ctor_set(x_143, 2, x_120);
lean_ctor_set(x_143, 3, x_121);
lean_ctor_set(x_143, 4, x_122);
x_67 = x_141;
x_68 = x_143;
goto block_95;
}
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_188; lean_object* x_189; uint8_t x_206; lean_object* x_207; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_164 = lean_ctor_get(x_30, 0);
x_165 = lean_ctor_get(x_30, 1);
x_166 = lean_ctor_get(x_30, 2);
x_167 = lean_ctor_get(x_30, 3);
x_168 = lean_ctor_get(x_30, 4);
x_169 = lean_ctor_get(x_30, 5);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_30);
lean_inc(x_31);
x_236 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_236, 0, x_164);
lean_ctor_set(x_236, 1, x_31);
lean_ctor_set(x_236, 2, x_166);
lean_ctor_set(x_236, 3, x_167);
lean_ctor_set(x_236, 4, x_168);
lean_ctor_set(x_236, 5, x_169);
lean_ctor_set(x_28, 0, x_236);
x_237 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_28);
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
x_241 = l_String_posOfAux___main___closed__2;
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_242 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_243 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_242, x_1, x_240);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_unbox(x_244);
lean_dec(x_244);
x_206 = x_246;
x_207 = x_245;
goto block_235;
}
else
{
uint8_t x_247; 
x_247 = 0;
x_206 = x_247;
x_207 = x_240;
goto block_235;
}
}
else
{
lean_object* x_248; uint8_t x_249; 
x_248 = lean_ctor_get(x_237, 1);
lean_inc(x_248);
lean_dec(x_237);
x_249 = l_String_posOfAux___main___closed__1;
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_250 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_251 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_250, x_1, x_248);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_unbox(x_252);
lean_dec(x_252);
x_206 = x_254;
x_207 = x_253;
goto block_235;
}
else
{
uint8_t x_255; 
x_255 = 0;
x_206 = x_255;
x_207 = x_248;
goto block_235;
}
}
block_187:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_170, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_170, 4);
lean_inc(x_175);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 x_176 = x_170;
} else {
 lean_dec_ref(x_170);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_171, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_171, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_171, 3);
lean_inc(x_179);
x_180 = lean_ctor_get(x_171, 4);
lean_inc(x_180);
x_181 = lean_ctor_get(x_171, 5);
lean_inc(x_181);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 lean_ctor_release(x_171, 3);
 lean_ctor_release(x_171, 4);
 lean_ctor_release(x_171, 5);
 x_182 = x_171;
} else {
 lean_dec_ref(x_171);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(0, 6, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_177);
lean_ctor_set(x_183, 1, x_165);
lean_ctor_set(x_183, 2, x_178);
lean_ctor_set(x_183, 3, x_179);
lean_ctor_set(x_183, 4, x_180);
lean_ctor_set(x_183, 5, x_181);
if (lean_is_scalar(x_176)) {
 x_184 = lean_alloc_ctor(0, 5, 0);
} else {
 x_184 = x_176;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_172);
lean_ctor_set(x_184, 2, x_173);
lean_ctor_set(x_184, 3, x_174);
lean_ctor_set(x_184, 4, x_175);
if (lean_is_scalar(x_17)) {
 x_185 = lean_alloc_ctor(0, 4, 0);
} else {
 x_185 = x_17;
}
lean_ctor_set(x_185, 0, x_14);
lean_ctor_set(x_185, 1, x_15);
lean_ctor_set(x_185, 2, x_31);
lean_ctor_set(x_185, 3, x_19);
x_186 = l_Lean_Meta_SynthInstance_consume(x_185, x_1, x_184);
return x_186;
}
block_205:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_189, 3);
lean_inc(x_193);
x_194 = lean_ctor_get(x_189, 4);
lean_inc(x_194);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 x_195 = x_189;
} else {
 lean_dec_ref(x_189);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_190, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_190, 2);
lean_inc(x_197);
x_198 = lean_ctor_get(x_190, 3);
lean_inc(x_198);
x_199 = lean_ctor_get(x_190, 4);
lean_inc(x_199);
x_200 = lean_ctor_get(x_190, 5);
lean_inc(x_200);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 lean_ctor_release(x_190, 2);
 lean_ctor_release(x_190, 3);
 lean_ctor_release(x_190, 4);
 lean_ctor_release(x_190, 5);
 x_201 = x_190;
} else {
 lean_dec_ref(x_190);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 6, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_196);
lean_ctor_set(x_202, 1, x_165);
lean_ctor_set(x_202, 2, x_197);
lean_ctor_set(x_202, 3, x_198);
lean_ctor_set(x_202, 4, x_199);
lean_ctor_set(x_202, 5, x_200);
if (lean_is_scalar(x_195)) {
 x_203 = lean_alloc_ctor(0, 5, 0);
} else {
 x_203 = x_195;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_191);
lean_ctor_set(x_203, 2, x_192);
lean_ctor_set(x_203, 3, x_193);
lean_ctor_set(x_203, 4, x_194);
if (lean_is_scalar(x_29)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_29;
 lean_ctor_set_tag(x_204, 1);
}
lean_ctor_set(x_204, 0, x_188);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
block_235:
{
if (x_206 == 0)
{
lean_dec(x_29);
lean_dec(x_18);
x_170 = x_207;
goto block_187;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_207, 2);
lean_inc(x_210);
x_211 = lean_ctor_get(x_207, 3);
lean_inc(x_211);
x_212 = lean_ctor_get(x_207, 4);
lean_inc(x_212);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 lean_ctor_release(x_207, 4);
 x_213 = x_207;
} else {
 lean_dec_ref(x_207);
 x_213 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_14);
x_214 = l_Lean_Meta_inferType(x_14, x_1, x_208);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
lean_inc(x_1);
x_217 = l_Lean_Meta_inferType(x_18, x_1, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_29);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
if (lean_is_scalar(x_213)) {
 x_220 = lean_alloc_ctor(0, 5, 0);
} else {
 x_220 = x_213;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_209);
lean_ctor_set(x_220, 2, x_210);
lean_ctor_set(x_220, 3, x_211);
lean_ctor_set(x_220, 4, x_212);
x_221 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_221, 0, x_215);
x_222 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_223 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_224, 0, x_218);
x_225 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_227 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_226, x_225, x_1, x_220);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_170 = x_228;
goto block_187;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_215);
lean_dec(x_31);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_229 = lean_ctor_get(x_217, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_217, 1);
lean_inc(x_230);
lean_dec(x_217);
if (lean_is_scalar(x_213)) {
 x_231 = lean_alloc_ctor(0, 5, 0);
} else {
 x_231 = x_213;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_209);
lean_ctor_set(x_231, 2, x_210);
lean_ctor_set(x_231, 3, x_211);
lean_ctor_set(x_231, 4, x_212);
x_188 = x_229;
x_189 = x_231;
goto block_205;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_31);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_232 = lean_ctor_get(x_214, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_214, 1);
lean_inc(x_233);
lean_dec(x_214);
if (lean_is_scalar(x_213)) {
 x_234 = lean_alloc_ctor(0, 5, 0);
} else {
 x_234 = x_213;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_209);
lean_ctor_set(x_234, 2, x_210);
lean_ctor_set(x_234, 3, x_211);
lean_ctor_set(x_234, 4, x_212);
x_188 = x_232;
x_189 = x_234;
goto block_205;
}
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_285; lean_object* x_286; uint8_t x_303; lean_object* x_304; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_256 = lean_ctor_get(x_28, 1);
x_257 = lean_ctor_get(x_28, 2);
x_258 = lean_ctor_get(x_28, 3);
x_259 = lean_ctor_get(x_28, 4);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_28);
x_260 = lean_ctor_get(x_30, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_30, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_30, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_30, 3);
lean_inc(x_263);
x_264 = lean_ctor_get(x_30, 4);
lean_inc(x_264);
x_265 = lean_ctor_get(x_30, 5);
lean_inc(x_265);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 lean_ctor_release(x_30, 4);
 lean_ctor_release(x_30, 5);
 x_266 = x_30;
} else {
 lean_dec_ref(x_30);
 x_266 = lean_box(0);
}
lean_inc(x_31);
if (lean_is_scalar(x_266)) {
 x_333 = lean_alloc_ctor(0, 6, 0);
} else {
 x_333 = x_266;
}
lean_ctor_set(x_333, 0, x_260);
lean_ctor_set(x_333, 1, x_31);
lean_ctor_set(x_333, 2, x_262);
lean_ctor_set(x_333, 3, x_263);
lean_ctor_set(x_333, 4, x_264);
lean_ctor_set(x_333, 5, x_265);
x_334 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_256);
lean_ctor_set(x_334, 2, x_257);
lean_ctor_set(x_334, 3, x_258);
lean_ctor_set(x_334, 4, x_259);
x_335 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_334);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get_uint8(x_336, sizeof(void*)*1);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; uint8_t x_339; 
x_338 = lean_ctor_get(x_335, 1);
lean_inc(x_338);
lean_dec(x_335);
x_339 = l_String_posOfAux___main___closed__2;
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_340 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_341 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_340, x_1, x_338);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = lean_unbox(x_342);
lean_dec(x_342);
x_303 = x_344;
x_304 = x_343;
goto block_332;
}
else
{
uint8_t x_345; 
x_345 = 0;
x_303 = x_345;
x_304 = x_338;
goto block_332;
}
}
else
{
lean_object* x_346; uint8_t x_347; 
x_346 = lean_ctor_get(x_335, 1);
lean_inc(x_346);
lean_dec(x_335);
x_347 = l_String_posOfAux___main___closed__1;
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; 
x_348 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_349 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_348, x_1, x_346);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = lean_unbox(x_350);
lean_dec(x_350);
x_303 = x_352;
x_304 = x_351;
goto block_332;
}
else
{
uint8_t x_353; 
x_353 = 0;
x_303 = x_353;
x_304 = x_346;
goto block_332;
}
}
block_284:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_267, 2);
lean_inc(x_270);
x_271 = lean_ctor_get(x_267, 3);
lean_inc(x_271);
x_272 = lean_ctor_get(x_267, 4);
lean_inc(x_272);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 lean_ctor_release(x_267, 2);
 lean_ctor_release(x_267, 3);
 lean_ctor_release(x_267, 4);
 x_273 = x_267;
} else {
 lean_dec_ref(x_267);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_268, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_268, 2);
lean_inc(x_275);
x_276 = lean_ctor_get(x_268, 3);
lean_inc(x_276);
x_277 = lean_ctor_get(x_268, 4);
lean_inc(x_277);
x_278 = lean_ctor_get(x_268, 5);
lean_inc(x_278);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 lean_ctor_release(x_268, 2);
 lean_ctor_release(x_268, 3);
 lean_ctor_release(x_268, 4);
 lean_ctor_release(x_268, 5);
 x_279 = x_268;
} else {
 lean_dec_ref(x_268);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(0, 6, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_274);
lean_ctor_set(x_280, 1, x_261);
lean_ctor_set(x_280, 2, x_275);
lean_ctor_set(x_280, 3, x_276);
lean_ctor_set(x_280, 4, x_277);
lean_ctor_set(x_280, 5, x_278);
if (lean_is_scalar(x_273)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_273;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_269);
lean_ctor_set(x_281, 2, x_270);
lean_ctor_set(x_281, 3, x_271);
lean_ctor_set(x_281, 4, x_272);
if (lean_is_scalar(x_17)) {
 x_282 = lean_alloc_ctor(0, 4, 0);
} else {
 x_282 = x_17;
}
lean_ctor_set(x_282, 0, x_14);
lean_ctor_set(x_282, 1, x_15);
lean_ctor_set(x_282, 2, x_31);
lean_ctor_set(x_282, 3, x_19);
x_283 = l_Lean_Meta_SynthInstance_consume(x_282, x_1, x_281);
return x_283;
}
block_302:
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
x_289 = lean_ctor_get(x_286, 2);
lean_inc(x_289);
x_290 = lean_ctor_get(x_286, 3);
lean_inc(x_290);
x_291 = lean_ctor_get(x_286, 4);
lean_inc(x_291);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 lean_ctor_release(x_286, 2);
 lean_ctor_release(x_286, 3);
 lean_ctor_release(x_286, 4);
 x_292 = x_286;
} else {
 lean_dec_ref(x_286);
 x_292 = lean_box(0);
}
x_293 = lean_ctor_get(x_287, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_287, 2);
lean_inc(x_294);
x_295 = lean_ctor_get(x_287, 3);
lean_inc(x_295);
x_296 = lean_ctor_get(x_287, 4);
lean_inc(x_296);
x_297 = lean_ctor_get(x_287, 5);
lean_inc(x_297);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 lean_ctor_release(x_287, 4);
 lean_ctor_release(x_287, 5);
 x_298 = x_287;
} else {
 lean_dec_ref(x_287);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(0, 6, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_293);
lean_ctor_set(x_299, 1, x_261);
lean_ctor_set(x_299, 2, x_294);
lean_ctor_set(x_299, 3, x_295);
lean_ctor_set(x_299, 4, x_296);
lean_ctor_set(x_299, 5, x_297);
if (lean_is_scalar(x_292)) {
 x_300 = lean_alloc_ctor(0, 5, 0);
} else {
 x_300 = x_292;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_288);
lean_ctor_set(x_300, 2, x_289);
lean_ctor_set(x_300, 3, x_290);
lean_ctor_set(x_300, 4, x_291);
if (lean_is_scalar(x_29)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_29;
 lean_ctor_set_tag(x_301, 1);
}
lean_ctor_set(x_301, 0, x_285);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
block_332:
{
if (x_303 == 0)
{
lean_dec(x_29);
lean_dec(x_18);
x_267 = x_304;
goto block_284;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
x_307 = lean_ctor_get(x_304, 2);
lean_inc(x_307);
x_308 = lean_ctor_get(x_304, 3);
lean_inc(x_308);
x_309 = lean_ctor_get(x_304, 4);
lean_inc(x_309);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 lean_ctor_release(x_304, 2);
 lean_ctor_release(x_304, 3);
 lean_ctor_release(x_304, 4);
 x_310 = x_304;
} else {
 lean_dec_ref(x_304);
 x_310 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_14);
x_311 = l_Lean_Meta_inferType(x_14, x_1, x_305);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
lean_inc(x_1);
x_314 = l_Lean_Meta_inferType(x_18, x_1, x_313);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_29);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
if (lean_is_scalar(x_310)) {
 x_317 = lean_alloc_ctor(0, 5, 0);
} else {
 x_317 = x_310;
}
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_306);
lean_ctor_set(x_317, 2, x_307);
lean_ctor_set(x_317, 3, x_308);
lean_ctor_set(x_317, 4, x_309);
x_318 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_318, 0, x_312);
x_319 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_320 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
x_321 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_321, 0, x_315);
x_322 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_324 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_323, x_322, x_1, x_317);
x_325 = lean_ctor_get(x_324, 1);
lean_inc(x_325);
lean_dec(x_324);
x_267 = x_325;
goto block_284;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_312);
lean_dec(x_31);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_326 = lean_ctor_get(x_314, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_314, 1);
lean_inc(x_327);
lean_dec(x_314);
if (lean_is_scalar(x_310)) {
 x_328 = lean_alloc_ctor(0, 5, 0);
} else {
 x_328 = x_310;
}
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_306);
lean_ctor_set(x_328, 2, x_307);
lean_ctor_set(x_328, 3, x_308);
lean_ctor_set(x_328, 4, x_309);
x_285 = x_326;
x_286 = x_328;
goto block_302;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_31);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_329 = lean_ctor_get(x_311, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_311, 1);
lean_inc(x_330);
lean_dec(x_311);
if (lean_is_scalar(x_310)) {
 x_331 = lean_alloc_ctor(0, 5, 0);
} else {
 x_331 = x_310;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_306);
lean_ctor_set(x_331, 2, x_307);
lean_ctor_set(x_331, 3, x_308);
lean_ctor_set(x_331, 4, x_309);
x_285 = x_329;
x_286 = x_331;
goto block_302;
}
}
}
}
}
}
else
{
uint8_t x_354; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_354 = !lean_is_exclusive(x_20);
if (x_354 == 0)
{
return x_20;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_20, 0);
x_356 = lean_ctor_get(x_20, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_20);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_step(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_2, 3);
lean_inc(x_55);
x_56 = l_Array_isEmpty___rarg(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = 1;
x_3 = x_57;
goto block_54;
}
else
{
uint8_t x_58; 
x_58 = 0;
x_3 = x_58;
goto block_54;
}
block_54:
{
uint8_t x_4; 
x_4 = l_coeDecidableEq(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Array_isEmpty___rarg(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_String_posOfAux___main___closed__2;
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Meta_SynthInstance_generate(x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = 1;
x_15 = lean_box(x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
else
{
uint8_t x_24; 
x_24 = l_String_posOfAux___main___closed__1;
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_2);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Meta_SynthInstance_generate(x_1, x_2);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = 1;
x_32 = lean_box(x_31);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Meta_SynthInstance_resume(x_1, x_2);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = 1;
x_45 = lean_box(x_44);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = 1;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_41, 0);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_41);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_22; uint8_t x_66; lean_object* x_67; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_77 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_3);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_78, sizeof(void*)*1);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l_String_posOfAux___main___closed__2;
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_83 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_82, x_2, x_80);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_unbox(x_84);
lean_dec(x_84);
x_66 = x_86;
x_67 = x_85;
goto block_76;
}
else
{
uint8_t x_87; 
x_87 = 0;
x_66 = x_87;
x_67 = x_80;
goto block_76;
}
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_77, 1);
lean_inc(x_88);
lean_dec(x_77);
x_89 = l_String_posOfAux___main___closed__1;
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_91 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_90, x_2, x_88);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_unbox(x_92);
lean_dec(x_92);
x_66 = x_94;
x_67 = x_93;
goto block_76;
}
else
{
uint8_t x_95; 
x_95 = 0;
x_66 = x_95;
x_67 = x_88;
goto block_76;
}
}
block_21:
{
if (x_8 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_13 = l_Lean_Meta_SynthInstance_synth___main___closed__3;
x_14 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_12, x_13, x_2, x_9);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
block_65:
{
lean_object* x_23; 
lean_inc(x_2);
x_23 = l_Lean_Meta_SynthInstance_step(x_2, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_7);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_String_posOfAux___main___closed__2;
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_33 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_32, x_2, x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unbox(x_34);
lean_dec(x_34);
x_8 = x_36;
x_9 = x_35;
goto block_21;
}
else
{
uint8_t x_37; 
x_37 = 0;
x_8 = x_37;
x_9 = x_30;
goto block_21;
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = l_String_posOfAux___main___closed__1;
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_41 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_40, x_2, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unbox(x_42);
lean_dec(x_42);
x_8 = x_44;
x_9 = x_43;
goto block_21;
}
else
{
uint8_t x_45; 
x_45 = 0;
x_8 = x_45;
x_9 = x_38;
goto block_21;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_dec(x_23);
x_47 = l_Lean_Meta_SynthInstance_getResult___rarg(x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_1 = x_7;
x_3 = x_49;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_7);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_47, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_47, 0, x_55);
return x_47;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_57 = lean_ctor_get(x_48, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_7);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_23);
if (x_61 == 0)
{
return x_23;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_23, 0);
x_63 = lean_ctor_get(x_23, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_23);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
block_76:
{
if (x_66 == 0)
{
x_22 = x_67;
goto block_65;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_inc(x_7);
x_68 = l_Nat_repr(x_7);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_Meta_SynthInstance_synth___main___closed__6;
x_72 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_74 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_73, x_72, x_2, x_67);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_22 = x_75;
goto block_65;
}
}
}
else
{
uint8_t x_96; lean_object* x_97; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_1);
x_110 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_3);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get_uint8(x_111, sizeof(void*)*1);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = l_String_posOfAux___main___closed__2;
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_115 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_116 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_115, x_2, x_113);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_unbox(x_117);
lean_dec(x_117);
x_96 = x_119;
x_97 = x_118;
goto block_109;
}
else
{
uint8_t x_120; 
x_120 = 0;
x_96 = x_120;
x_97 = x_113;
goto block_109;
}
}
else
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_110, 1);
lean_inc(x_121);
lean_dec(x_110);
x_122 = l_String_posOfAux___main___closed__1;
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_123 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_124 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_123, x_2, x_121);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_unbox(x_125);
lean_dec(x_125);
x_96 = x_127;
x_97 = x_126;
goto block_109;
}
else
{
uint8_t x_128; 
x_128 = 0;
x_96 = x_128;
x_97 = x_121;
goto block_109;
}
}
block_109:
{
if (x_96 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_2);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_101 = l_Lean_Meta_SynthInstance_synth___main___closed__9;
x_102 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_100, x_101, x_2, x_97);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
x_105 = lean_box(0);
lean_ctor_set(x_102, 0, x_105);
return x_102;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
lean_dec(x_102);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
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
lean_object* l_mkHashMap___at_Lean_Meta_SynthInstance_main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
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
uint8_t x_5; lean_object* x_6; lean_object* x_428; uint8_t x_429; 
x_428 = lean_ctor_get(x_4, 4);
lean_inc(x_428);
x_429 = lean_ctor_get_uint8(x_428, sizeof(void*)*1);
lean_dec(x_428);
if (x_429 == 0)
{
uint8_t x_430; 
x_430 = l_String_posOfAux___main___closed__2;
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_431 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_432 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_431, x_3, x_4);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
x_435 = lean_unbox(x_433);
lean_dec(x_433);
x_5 = x_435;
x_6 = x_434;
goto block_427;
}
else
{
uint8_t x_436; 
x_436 = 0;
x_5 = x_436;
x_6 = x_4;
goto block_427;
}
}
else
{
uint8_t x_437; 
x_437 = l_String_posOfAux___main___closed__1;
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
x_438 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_439 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_438, x_3, x_4);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_442 = lean_unbox(x_440);
lean_dec(x_440);
x_5 = x_442;
x_6 = x_441;
goto block_427;
}
else
{
uint8_t x_443; 
x_443 = 0;
x_5 = x_443;
x_6 = x_4;
goto block_427;
}
}
block_427:
{
uint8_t x_7; 
if (x_5 == 0)
{
uint8_t x_425; 
x_425 = 1;
x_7 = x_425;
goto block_424;
}
else
{
uint8_t x_426; 
x_426 = 0;
x_7 = x_426;
goto block_424;
}
block_424:
{
uint8_t x_8; 
x_8 = l_coeDecidableEq(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_97; lean_object* x_98; lean_object* x_106; uint8_t x_107; 
x_9 = l___private_Init_Lean_Util_Trace_3__getResetTraces___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__1___rarg(x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_106 = lean_ctor_get(x_11, 4);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_106, sizeof(void*)*1);
lean_dec(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = l_String_posOfAux___main___closed__2;
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_109 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_110 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_109, x_3, x_11);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_unbox(x_111);
lean_dec(x_111);
x_97 = x_113;
x_98 = x_112;
goto block_105;
}
else
{
uint8_t x_114; 
x_114 = 0;
x_97 = x_114;
x_98 = x_11;
goto block_105;
}
}
else
{
uint8_t x_115; 
x_115 = l_String_posOfAux___main___closed__1;
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_117 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_116, x_3, x_11);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_unbox(x_118);
lean_dec(x_118);
x_97 = x_120;
x_98 = x_119;
goto block_105;
}
else
{
uint8_t x_121; 
x_121 = 0;
x_97 = x_121;
x_98 = x_11;
goto block_105;
}
}
block_96:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_box(0);
x_14 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_15 = l_Lean_Meta_mkFreshExprMVar(x_1, x_13, x_14, x_3, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = l_Lean_Meta_SynthInstance_mkTableKey(x_19, x_1);
lean_inc(x_19);
x_21 = lean_box(0);
x_22 = l_Array_empty___closed__1;
x_23 = l_Lean_Meta_SynthInstance_main___closed__1;
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
x_25 = lean_box(1);
lean_inc(x_3);
x_26 = l_Lean_Meta_SynthInstance_newSubgoal(x_19, x_20, x_17, x_25, x_3, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_3);
x_28 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_33 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_10, x_32, x_3, x_31);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_29);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_42 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_10, x_41, x_3, x_40);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_38);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_2);
x_47 = lean_ctor_get(x_26, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_26, 1);
lean_inc(x_48);
lean_dec(x_26);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_51 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_10, x_50, x_3, x_49);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_47);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_56 = lean_ctor_get(x_16, 0);
x_57 = lean_ctor_get(x_16, 1);
x_58 = lean_ctor_get(x_16, 2);
x_59 = lean_ctor_get(x_16, 3);
x_60 = lean_ctor_get(x_16, 4);
x_61 = lean_ctor_get(x_16, 5);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_16);
lean_inc(x_57);
x_62 = l_Lean_Meta_SynthInstance_mkTableKey(x_57, x_1);
lean_inc(x_57);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_57);
lean_ctor_set(x_63, 2, x_58);
lean_ctor_set(x_63, 3, x_59);
lean_ctor_set(x_63, 4, x_60);
lean_ctor_set(x_63, 5, x_61);
x_64 = lean_box(0);
x_65 = l_Array_empty___closed__1;
x_66 = l_Lean_Meta_SynthInstance_main___closed__1;
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_65);
lean_ctor_set(x_67, 4, x_66);
x_68 = lean_box(1);
lean_inc(x_3);
x_69 = l_Lean_Meta_SynthInstance_newSubgoal(x_57, x_62, x_17, x_68, x_3, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
lean_inc(x_3);
x_71 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_76 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_10, x_75, x_3, x_74);
lean_dec(x_3);
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
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_ctor_get(x_71, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_71, 1);
lean_inc(x_81);
lean_dec(x_71);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_84 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_10, x_83, x_3, x_82);
lean_dec(x_3);
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
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
 lean_ctor_set_tag(x_87, 1);
}
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_2);
x_88 = lean_ctor_get(x_69, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_69, 1);
lean_inc(x_89);
lean_dec(x_69);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_92 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_10, x_91, x_3, x_90);
lean_dec(x_3);
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
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
block_105:
{
if (x_97 == 0)
{
x_12 = x_98;
goto block_96;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_inc(x_1);
x_99 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_99, 0, x_1);
x_100 = l_Lean_Meta_SynthInstance_main___closed__4;
x_101 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_103 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_102, x_101, x_3, x_98);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_12 = x_104;
goto block_96;
}
}
}
else
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_6);
if (x_122 == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_6, 4);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
uint8_t x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_148; uint8_t x_241; lean_object* x_242; uint8_t x_250; 
x_125 = lean_ctor_get_uint8(x_123, sizeof(void*)*1);
x_126 = 0;
lean_ctor_set_uint8(x_123, sizeof(void*)*1, x_126);
x_250 = l_String_posOfAux___main___closed__2;
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_251 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_252 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_251, x_3, x_6);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_unbox(x_253);
lean_dec(x_253);
x_241 = x_255;
x_242 = x_254;
goto block_249;
}
else
{
x_241 = x_126;
x_242 = x_6;
goto block_249;
}
block_147:
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_128, 4);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; 
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_125);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_128);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_125);
lean_ctor_set(x_128, 4, x_134);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_127);
lean_ctor_set(x_135, 1, x_128);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_136 = lean_ctor_get(x_128, 4);
x_137 = lean_ctor_get(x_128, 0);
x_138 = lean_ctor_get(x_128, 1);
x_139 = lean_ctor_get(x_128, 2);
x_140 = lean_ctor_get(x_128, 3);
x_141 = lean_ctor_get(x_128, 5);
lean_inc(x_141);
lean_inc(x_136);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_128);
x_142 = lean_ctor_get(x_136, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 1, 1);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_125);
x_145 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_145, 0, x_137);
lean_ctor_set(x_145, 1, x_138);
lean_ctor_set(x_145, 2, x_139);
lean_ctor_set(x_145, 3, x_140);
lean_ctor_set(x_145, 4, x_144);
lean_ctor_set(x_145, 5, x_141);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_127);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
block_240:
{
lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_149 = lean_box(0);
x_150 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_151 = l_Lean_Meta_mkFreshExprMVar(x_1, x_149, x_150, x_3, x_148);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
lean_dec(x_151);
x_154 = !lean_is_exclusive(x_152);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
x_156 = l_Lean_Meta_SynthInstance_mkTableKey(x_155, x_1);
lean_inc(x_155);
x_157 = lean_box(0);
x_158 = l_Array_empty___closed__1;
x_159 = l_Lean_Meta_SynthInstance_main___closed__1;
x_160 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_160, 0, x_152);
lean_ctor_set(x_160, 1, x_157);
lean_ctor_set(x_160, 2, x_158);
lean_ctor_set(x_160, 3, x_158);
lean_ctor_set(x_160, 4, x_159);
x_161 = lean_box(1);
lean_inc(x_3);
x_162 = l_Lean_Meta_SynthInstance_newSubgoal(x_155, x_156, x_153, x_161, x_3, x_160);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_ctor_get(x_166, 4);
lean_inc(x_167);
x_168 = !lean_is_exclusive(x_164);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_164, 1);
lean_dec(x_169);
x_170 = !lean_is_exclusive(x_166);
if (x_170 == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_166, 4);
lean_dec(x_171);
x_172 = !lean_is_exclusive(x_167);
if (x_172 == 0)
{
lean_ctor_set_uint8(x_167, sizeof(void*)*1, x_125);
lean_ctor_set(x_164, 1, x_166);
return x_164;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_167, 0);
lean_inc(x_173);
lean_dec(x_167);
x_174 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_125);
lean_ctor_set(x_166, 4, x_174);
lean_ctor_set(x_164, 1, x_166);
return x_164;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_175 = lean_ctor_get(x_166, 0);
x_176 = lean_ctor_get(x_166, 1);
x_177 = lean_ctor_get(x_166, 2);
x_178 = lean_ctor_get(x_166, 3);
x_179 = lean_ctor_get(x_166, 5);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_166);
x_180 = lean_ctor_get(x_167, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_181 = x_167;
} else {
 lean_dec_ref(x_167);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 1, 1);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set_uint8(x_182, sizeof(void*)*1, x_125);
x_183 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_183, 0, x_175);
lean_ctor_set(x_183, 1, x_176);
lean_ctor_set(x_183, 2, x_177);
lean_ctor_set(x_183, 3, x_178);
lean_ctor_set(x_183, 4, x_182);
lean_ctor_set(x_183, 5, x_179);
lean_ctor_set(x_164, 1, x_183);
return x_164;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_184 = lean_ctor_get(x_164, 0);
lean_inc(x_184);
lean_dec(x_164);
x_185 = lean_ctor_get(x_166, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_166, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_166, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_166, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_166, 5);
lean_inc(x_189);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 lean_ctor_release(x_166, 4);
 lean_ctor_release(x_166, 5);
 x_190 = x_166;
} else {
 lean_dec_ref(x_166);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_167, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_192 = x_167;
} else {
 lean_dec_ref(x_167);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 1, 1);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*1, x_125);
if (lean_is_scalar(x_190)) {
 x_194 = lean_alloc_ctor(0, 6, 0);
} else {
 x_194 = x_190;
}
lean_ctor_set(x_194, 0, x_185);
lean_ctor_set(x_194, 1, x_186);
lean_ctor_set(x_194, 2, x_187);
lean_ctor_set(x_194, 3, x_188);
lean_ctor_set(x_194, 4, x_193);
lean_ctor_set(x_194, 5, x_189);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_184);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_164, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_164, 1);
lean_inc(x_197);
lean_dec(x_164);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec(x_197);
x_127 = x_196;
x_128 = x_198;
goto block_147;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_3);
lean_dec(x_2);
x_199 = lean_ctor_get(x_162, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_162, 1);
lean_inc(x_200);
lean_dec(x_162);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec(x_200);
x_127 = x_199;
x_128 = x_201;
goto block_147;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_202 = lean_ctor_get(x_152, 0);
x_203 = lean_ctor_get(x_152, 1);
x_204 = lean_ctor_get(x_152, 2);
x_205 = lean_ctor_get(x_152, 3);
x_206 = lean_ctor_get(x_152, 4);
x_207 = lean_ctor_get(x_152, 5);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_152);
lean_inc(x_203);
x_208 = l_Lean_Meta_SynthInstance_mkTableKey(x_203, x_1);
lean_inc(x_203);
x_209 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_209, 0, x_202);
lean_ctor_set(x_209, 1, x_203);
lean_ctor_set(x_209, 2, x_204);
lean_ctor_set(x_209, 3, x_205);
lean_ctor_set(x_209, 4, x_206);
lean_ctor_set(x_209, 5, x_207);
x_210 = lean_box(0);
x_211 = l_Array_empty___closed__1;
x_212 = l_Lean_Meta_SynthInstance_main___closed__1;
x_213 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_210);
lean_ctor_set(x_213, 2, x_211);
lean_ctor_set(x_213, 3, x_211);
lean_ctor_set(x_213, 4, x_212);
x_214 = lean_box(1);
lean_inc(x_3);
x_215 = l_Lean_Meta_SynthInstance_newSubgoal(x_203, x_208, x_153, x_214, x_3, x_213);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec(x_218);
x_220 = lean_ctor_get(x_219, 4);
lean_inc(x_220);
x_221 = lean_ctor_get(x_217, 0);
lean_inc(x_221);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_222 = x_217;
} else {
 lean_dec_ref(x_217);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_219, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_219, 2);
lean_inc(x_225);
x_226 = lean_ctor_get(x_219, 3);
lean_inc(x_226);
x_227 = lean_ctor_get(x_219, 5);
lean_inc(x_227);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 lean_ctor_release(x_219, 2);
 lean_ctor_release(x_219, 3);
 lean_ctor_release(x_219, 4);
 lean_ctor_release(x_219, 5);
 x_228 = x_219;
} else {
 lean_dec_ref(x_219);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_220, 0);
lean_inc(x_229);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_230 = x_220;
} else {
 lean_dec_ref(x_220);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(0, 1, 1);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set_uint8(x_231, sizeof(void*)*1, x_125);
if (lean_is_scalar(x_228)) {
 x_232 = lean_alloc_ctor(0, 6, 0);
} else {
 x_232 = x_228;
}
lean_ctor_set(x_232, 0, x_223);
lean_ctor_set(x_232, 1, x_224);
lean_ctor_set(x_232, 2, x_225);
lean_ctor_set(x_232, 3, x_226);
lean_ctor_set(x_232, 4, x_231);
lean_ctor_set(x_232, 5, x_227);
if (lean_is_scalar(x_222)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_222;
}
lean_ctor_set(x_233, 0, x_221);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_217, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_217, 1);
lean_inc(x_235);
lean_dec(x_217);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec(x_235);
x_127 = x_234;
x_128 = x_236;
goto block_147;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_3);
lean_dec(x_2);
x_237 = lean_ctor_get(x_215, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_215, 1);
lean_inc(x_238);
lean_dec(x_215);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec(x_238);
x_127 = x_237;
x_128 = x_239;
goto block_147;
}
}
}
block_249:
{
if (x_241 == 0)
{
x_148 = x_242;
goto block_240;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_inc(x_1);
x_243 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_243, 0, x_1);
x_244 = l_Lean_Meta_SynthInstance_main___closed__4;
x_245 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
x_246 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_247 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_246, x_245, x_3, x_242);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec(x_247);
x_148 = x_248;
goto block_240;
}
}
}
else
{
uint8_t x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_275; uint8_t x_321; lean_object* x_322; uint8_t x_330; 
x_256 = lean_ctor_get_uint8(x_123, sizeof(void*)*1);
x_257 = lean_ctor_get(x_123, 0);
lean_inc(x_257);
lean_dec(x_123);
x_258 = 0;
x_259 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set_uint8(x_259, sizeof(void*)*1, x_258);
lean_ctor_set(x_6, 4, x_259);
x_330 = l_String_posOfAux___main___closed__2;
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_331 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_332 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_331, x_3, x_6);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_unbox(x_333);
lean_dec(x_333);
x_321 = x_335;
x_322 = x_334;
goto block_329;
}
else
{
x_321 = x_258;
x_322 = x_6;
goto block_329;
}
block_274:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_262 = lean_ctor_get(x_261, 4);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_261, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_261, 3);
lean_inc(x_266);
x_267 = lean_ctor_get(x_261, 5);
lean_inc(x_267);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 lean_ctor_release(x_261, 4);
 lean_ctor_release(x_261, 5);
 x_268 = x_261;
} else {
 lean_dec_ref(x_261);
 x_268 = lean_box(0);
}
x_269 = lean_ctor_get(x_262, 0);
lean_inc(x_269);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 x_270 = x_262;
} else {
 lean_dec_ref(x_262);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(0, 1, 1);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set_uint8(x_271, sizeof(void*)*1, x_256);
if (lean_is_scalar(x_268)) {
 x_272 = lean_alloc_ctor(0, 6, 0);
} else {
 x_272 = x_268;
}
lean_ctor_set(x_272, 0, x_263);
lean_ctor_set(x_272, 1, x_264);
lean_ctor_set(x_272, 2, x_265);
lean_ctor_set(x_272, 3, x_266);
lean_ctor_set(x_272, 4, x_271);
lean_ctor_set(x_272, 5, x_267);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_260);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
block_320:
{
lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_276 = lean_box(0);
x_277 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_278 = l_Lean_Meta_mkFreshExprMVar(x_1, x_276, x_277, x_3, x_275);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 0);
lean_inc(x_280);
lean_dec(x_278);
x_281 = lean_ctor_get(x_279, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_279, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_279, 2);
lean_inc(x_283);
x_284 = lean_ctor_get(x_279, 3);
lean_inc(x_284);
x_285 = lean_ctor_get(x_279, 4);
lean_inc(x_285);
x_286 = lean_ctor_get(x_279, 5);
lean_inc(x_286);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 lean_ctor_release(x_279, 3);
 lean_ctor_release(x_279, 4);
 lean_ctor_release(x_279, 5);
 x_287 = x_279;
} else {
 lean_dec_ref(x_279);
 x_287 = lean_box(0);
}
lean_inc(x_282);
x_288 = l_Lean_Meta_SynthInstance_mkTableKey(x_282, x_1);
lean_inc(x_282);
if (lean_is_scalar(x_287)) {
 x_289 = lean_alloc_ctor(0, 6, 0);
} else {
 x_289 = x_287;
}
lean_ctor_set(x_289, 0, x_281);
lean_ctor_set(x_289, 1, x_282);
lean_ctor_set(x_289, 2, x_283);
lean_ctor_set(x_289, 3, x_284);
lean_ctor_set(x_289, 4, x_285);
lean_ctor_set(x_289, 5, x_286);
x_290 = lean_box(0);
x_291 = l_Array_empty___closed__1;
x_292 = l_Lean_Meta_SynthInstance_main___closed__1;
x_293 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_293, 0, x_289);
lean_ctor_set(x_293, 1, x_290);
lean_ctor_set(x_293, 2, x_291);
lean_ctor_set(x_293, 3, x_291);
lean_ctor_set(x_293, 4, x_292);
x_294 = lean_box(1);
lean_inc(x_3);
x_295 = l_Lean_Meta_SynthInstance_newSubgoal(x_282, x_288, x_280, x_294, x_3, x_293);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
lean_dec(x_295);
x_297 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_296);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
lean_dec(x_298);
x_300 = lean_ctor_get(x_299, 4);
lean_inc(x_300);
x_301 = lean_ctor_get(x_297, 0);
lean_inc(x_301);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_302 = x_297;
} else {
 lean_dec_ref(x_297);
 x_302 = lean_box(0);
}
x_303 = lean_ctor_get(x_299, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_299, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_299, 2);
lean_inc(x_305);
x_306 = lean_ctor_get(x_299, 3);
lean_inc(x_306);
x_307 = lean_ctor_get(x_299, 5);
lean_inc(x_307);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 lean_ctor_release(x_299, 2);
 lean_ctor_release(x_299, 3);
 lean_ctor_release(x_299, 4);
 lean_ctor_release(x_299, 5);
 x_308 = x_299;
} else {
 lean_dec_ref(x_299);
 x_308 = lean_box(0);
}
x_309 = lean_ctor_get(x_300, 0);
lean_inc(x_309);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 x_310 = x_300;
} else {
 lean_dec_ref(x_300);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(0, 1, 1);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set_uint8(x_311, sizeof(void*)*1, x_256);
if (lean_is_scalar(x_308)) {
 x_312 = lean_alloc_ctor(0, 6, 0);
} else {
 x_312 = x_308;
}
lean_ctor_set(x_312, 0, x_303);
lean_ctor_set(x_312, 1, x_304);
lean_ctor_set(x_312, 2, x_305);
lean_ctor_set(x_312, 3, x_306);
lean_ctor_set(x_312, 4, x_311);
lean_ctor_set(x_312, 5, x_307);
if (lean_is_scalar(x_302)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_302;
}
lean_ctor_set(x_313, 0, x_301);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_297, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_297, 1);
lean_inc(x_315);
lean_dec(x_297);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec(x_315);
x_260 = x_314;
x_261 = x_316;
goto block_274;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_3);
lean_dec(x_2);
x_317 = lean_ctor_get(x_295, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_295, 1);
lean_inc(x_318);
lean_dec(x_295);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
lean_dec(x_318);
x_260 = x_317;
x_261 = x_319;
goto block_274;
}
}
block_329:
{
if (x_321 == 0)
{
x_275 = x_322;
goto block_320;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_inc(x_1);
x_323 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_323, 0, x_1);
x_324 = l_Lean_Meta_SynthInstance_main___closed__4;
x_325 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
x_326 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_327 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_326, x_325, x_3, x_322);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
lean_dec(x_327);
x_275 = x_328;
goto block_320;
}
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_363; uint8_t x_409; lean_object* x_410; uint8_t x_418; 
x_336 = lean_ctor_get(x_6, 4);
x_337 = lean_ctor_get(x_6, 0);
x_338 = lean_ctor_get(x_6, 1);
x_339 = lean_ctor_get(x_6, 2);
x_340 = lean_ctor_get(x_6, 3);
x_341 = lean_ctor_get(x_6, 5);
lean_inc(x_341);
lean_inc(x_336);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_6);
x_342 = lean_ctor_get_uint8(x_336, sizeof(void*)*1);
x_343 = lean_ctor_get(x_336, 0);
lean_inc(x_343);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_344 = x_336;
} else {
 lean_dec_ref(x_336);
 x_344 = lean_box(0);
}
x_345 = 0;
if (lean_is_scalar(x_344)) {
 x_346 = lean_alloc_ctor(0, 1, 1);
} else {
 x_346 = x_344;
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set_uint8(x_346, sizeof(void*)*1, x_345);
x_347 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_347, 0, x_337);
lean_ctor_set(x_347, 1, x_338);
lean_ctor_set(x_347, 2, x_339);
lean_ctor_set(x_347, 3, x_340);
lean_ctor_set(x_347, 4, x_346);
lean_ctor_set(x_347, 5, x_341);
x_418 = l_String_posOfAux___main___closed__2;
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_419 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_420 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_419, x_3, x_347);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_unbox(x_421);
lean_dec(x_421);
x_409 = x_423;
x_410 = x_422;
goto block_417;
}
else
{
x_409 = x_345;
x_410 = x_347;
goto block_417;
}
block_362:
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_350 = lean_ctor_get(x_349, 4);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 2);
lean_inc(x_353);
x_354 = lean_ctor_get(x_349, 3);
lean_inc(x_354);
x_355 = lean_ctor_get(x_349, 5);
lean_inc(x_355);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 lean_ctor_release(x_349, 4);
 lean_ctor_release(x_349, 5);
 x_356 = x_349;
} else {
 lean_dec_ref(x_349);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_350, 0);
lean_inc(x_357);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 x_358 = x_350;
} else {
 lean_dec_ref(x_350);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(0, 1, 1);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set_uint8(x_359, sizeof(void*)*1, x_342);
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
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_348);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
block_408:
{
lean_object* x_364; uint8_t x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_364 = lean_box(0);
x_365 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_366 = l_Lean_Meta_mkFreshExprMVar(x_1, x_364, x_365, x_3, x_363);
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 0);
lean_inc(x_368);
lean_dec(x_366);
x_369 = lean_ctor_get(x_367, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_367, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_367, 2);
lean_inc(x_371);
x_372 = lean_ctor_get(x_367, 3);
lean_inc(x_372);
x_373 = lean_ctor_get(x_367, 4);
lean_inc(x_373);
x_374 = lean_ctor_get(x_367, 5);
lean_inc(x_374);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 lean_ctor_release(x_367, 4);
 lean_ctor_release(x_367, 5);
 x_375 = x_367;
} else {
 lean_dec_ref(x_367);
 x_375 = lean_box(0);
}
lean_inc(x_370);
x_376 = l_Lean_Meta_SynthInstance_mkTableKey(x_370, x_1);
lean_inc(x_370);
if (lean_is_scalar(x_375)) {
 x_377 = lean_alloc_ctor(0, 6, 0);
} else {
 x_377 = x_375;
}
lean_ctor_set(x_377, 0, x_369);
lean_ctor_set(x_377, 1, x_370);
lean_ctor_set(x_377, 2, x_371);
lean_ctor_set(x_377, 3, x_372);
lean_ctor_set(x_377, 4, x_373);
lean_ctor_set(x_377, 5, x_374);
x_378 = lean_box(0);
x_379 = l_Array_empty___closed__1;
x_380 = l_Lean_Meta_SynthInstance_main___closed__1;
x_381 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_381, 0, x_377);
lean_ctor_set(x_381, 1, x_378);
lean_ctor_set(x_381, 2, x_379);
lean_ctor_set(x_381, 3, x_379);
lean_ctor_set(x_381, 4, x_380);
x_382 = lean_box(1);
lean_inc(x_3);
x_383 = l_Lean_Meta_SynthInstance_newSubgoal(x_370, x_376, x_368, x_382, x_3, x_381);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; 
x_384 = lean_ctor_get(x_383, 1);
lean_inc(x_384);
lean_dec(x_383);
x_385 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_384);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
lean_dec(x_386);
x_388 = lean_ctor_get(x_387, 4);
lean_inc(x_388);
x_389 = lean_ctor_get(x_385, 0);
lean_inc(x_389);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_390 = x_385;
} else {
 lean_dec_ref(x_385);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_387, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_387, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_387, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_387, 3);
lean_inc(x_394);
x_395 = lean_ctor_get(x_387, 5);
lean_inc(x_395);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 lean_ctor_release(x_387, 2);
 lean_ctor_release(x_387, 3);
 lean_ctor_release(x_387, 4);
 lean_ctor_release(x_387, 5);
 x_396 = x_387;
} else {
 lean_dec_ref(x_387);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_388, 0);
lean_inc(x_397);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 x_398 = x_388;
} else {
 lean_dec_ref(x_388);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(0, 1, 1);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set_uint8(x_399, sizeof(void*)*1, x_342);
if (lean_is_scalar(x_396)) {
 x_400 = lean_alloc_ctor(0, 6, 0);
} else {
 x_400 = x_396;
}
lean_ctor_set(x_400, 0, x_391);
lean_ctor_set(x_400, 1, x_392);
lean_ctor_set(x_400, 2, x_393);
lean_ctor_set(x_400, 3, x_394);
lean_ctor_set(x_400, 4, x_399);
lean_ctor_set(x_400, 5, x_395);
if (lean_is_scalar(x_390)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_390;
}
lean_ctor_set(x_401, 0, x_389);
lean_ctor_set(x_401, 1, x_400);
return x_401;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_385, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_385, 1);
lean_inc(x_403);
lean_dec(x_385);
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
lean_dec(x_403);
x_348 = x_402;
x_349 = x_404;
goto block_362;
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
lean_dec(x_3);
lean_dec(x_2);
x_405 = lean_ctor_get(x_383, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_383, 1);
lean_inc(x_406);
lean_dec(x_383);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
lean_dec(x_406);
x_348 = x_405;
x_349 = x_407;
goto block_362;
}
}
block_417:
{
if (x_409 == 0)
{
x_363 = x_410;
goto block_408;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_inc(x_1);
x_411 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_411, 0, x_1);
x_412 = l_Lean_Meta_SynthInstance_main___closed__4;
x_413 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_411);
x_414 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_415 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_414, x_413, x_3, x_410);
x_416 = lean_ctor_get(x_415, 1);
lean_inc(x_416);
lean_dec(x_415);
x_363 = x_416;
goto block_408;
}
}
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_SynthInstance_2__preprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* _init_l___private_Init_Lean_Meta_SynthInstance_2__preprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_SynthInstance_2__preprocess___lambda__1), 4, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_SynthInstance_2__preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Meta_SynthInstance_2__preprocess___closed__1;
x_5 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Meta_instantiateLevelMVars(x_7, x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Level_hasMVar(x_10);
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_15 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_16);
x_1 = x_2;
x_2 = x_8;
x_4 = x_17;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_21 = l_Lean_Meta_instantiateLevelMVars(x_19, x_3, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Level_hasMVar(x_22);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_1);
x_1 = x_26;
x_2 = x_20;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
x_28 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_1);
x_1 = x_31;
x_2 = x_20;
x_4 = x_30;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(0);
x_5 = l_List_foldlM___main___at___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1(x_4, x_1, x_2, x_3);
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
lean_object* l_List_foldlM___main___at___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldlM___main___at___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type class resolution failed, insufficient number of arguments");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1;
x_2 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
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
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_inc(x_14);
x_17 = lean_array_fset(x_3, x_2, x_14);
x_18 = lean_expr_instantiate1(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
x_3 = x_17;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = 0;
lean_inc(x_4);
x_24 = l_Lean_Meta_mkFreshExprMVar(x_12, x_22, x_23, x_4, x_11);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = lean_array_fset(x_3, x_2, x_25);
x_28 = lean_expr_instantiate1(x_13, x_25);
lean_dec(x_25);
lean_dec(x_13);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
x_3 = x_27;
x_5 = x_26;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_9, 0);
lean_dec(x_33);
x_34 = l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2;
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_34);
return x_9;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_dec(x_9);
x_36 = l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
return x_9;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_SynthInstance_5__preprocessOutParam___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_11; 
x_11 = l_String_posOfAux___main___closed__2;
if (x_11 == 0)
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
x_18 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_3, x_15, x_17);
x_19 = l___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels(x_8, x_4, x_5);
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
x_26 = l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main(x_24, x_12, x_18, x_4, x_25);
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
else
{
lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_5);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = l_String_posOfAux___main___closed__1;
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_41);
x_43 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_42);
x_44 = lean_mk_array(x_42, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_42, x_45);
lean_dec(x_42);
x_47 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_3, x_44, x_46);
x_48 = l___private_Init_Lean_Meta_SynthInstance_3__preprocessLevels(x_8, x_4, x_5);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_mkConst(x_7, x_49);
lean_inc(x_4);
lean_inc(x_51);
x_52 = l_Lean_Meta_inferType(x_51, x_4, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_4);
x_55 = l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main(x_53, x_41, x_47, x_4, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_56, x_56, x_41, x_51);
lean_dec(x_56);
x_59 = l_Lean_Meta_mkForall(x_2, x_58, x_4, x_57);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_51);
lean_dec(x_4);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_4);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_52);
if (x_64 == 0)
{
return x_52;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_52, 0);
x_66 = lean_ctor_get(x_52, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_52);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_5);
return x_68;
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_5);
return x_69;
}
}
}
lean_object* l___private_Init_Lean_Meta_SynthInstance_5__preprocessOutParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_SynthInstance_5__preprocessOutParam___lambda__1), 5, 1);
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
lean_object* l___private_Init_Lean_Meta_SynthInstance_6__getMaxSteps(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_maxStepsOption___closed__2;
x_3 = lean_unsigned_to_nat(10000u);
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_SynthInstance_6__getMaxSteps___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Meta_SynthInstance_6__getMaxSteps(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_synthInstance_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_expr_eqv(x_3, x_17);
lean_dec(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_2 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_26 = lean_array_fset(x_5, x_2, x_3);
x_27 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_28 = lean_array_fset(x_5, x_2, x_3);
x_29 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
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
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_expr_eqv(x_4, x_19);
x_22 = l_coeDecidableEq(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_15);
x_23 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_array_fset(x_17, x_12, x_24);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_26 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_expr_eqv(x_4, x_27);
x_30 = l_coeDecidableEq(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_PersistentHashMap_mkCollisionNode___rarg(x_27, x_28, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_35 = lean_array_fset(x_17, x_12, x_34);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
}
}
case 1:
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = x_2 >> x_9;
x_39 = x_3 + x_8;
x_40 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_37, x_38, x_39, x_4, x_5);
lean_ctor_set(x_15, 0, x_40);
x_41 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_41);
return x_1;
}
else
{
lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
lean_dec(x_15);
x_43 = x_2 >> x_9;
x_44 = x_3 + x_8;
x_45 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_42, x_43, x_44, x_4, x_5);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_49 = lean_array_fset(x_17, x_12, x_48);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_49);
return x_1;
}
}
}
}
else
{
lean_object* x_50; size_t x_51; size_t x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
lean_dec(x_1);
x_51 = 1;
x_52 = 5;
x_53 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_54 = x_2 & x_53;
x_55 = lean_usize_to_nat(x_54);
x_56 = lean_array_get_size(x_50);
x_57 = lean_nat_dec_lt(x_55, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_4);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_50);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_array_fget(x_50, x_55);
x_60 = lean_box(2);
x_61 = lean_array_fset(x_50, x_55, x_60);
switch (lean_obj_tag(x_59)) {
case 0:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_64 = x_59;
} else {
 lean_dec_ref(x_59);
 x_64 = lean_box(0);
}
x_65 = lean_expr_eqv(x_4, x_62);
x_66 = l_coeDecidableEq(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_64);
x_67 = l_PersistentHashMap_mkCollisionNode___rarg(x_62, x_63, x_4, x_5);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_array_fset(x_61, x_55, x_68);
lean_dec(x_55);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
lean_dec(x_62);
if (lean_is_scalar(x_64)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_64;
}
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_71, 1, x_5);
x_72 = lean_array_fset(x_61, x_55, x_71);
lean_dec(x_55);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
case 1:
{
lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_59, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_75 = x_59;
} else {
 lean_dec_ref(x_59);
 x_75 = lean_box(0);
}
x_76 = x_2 >> x_52;
x_77 = x_3 + x_51;
x_78 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_74, x_76, x_77, x_4, x_5);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_array_fset(x_61, x_55, x_79);
lean_dec(x_55);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
default: 
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_4);
lean_ctor_set(x_82, 1, x_5);
x_83 = lean_array_fset(x_61, x_55, x_82);
lean_dec(x_55);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; size_t x_94; uint8_t x_95; 
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_synthInstance_x3f___spec__3(x_1, x_85, x_4, x_5);
x_94 = 7;
x_95 = x_94 <= x_3;
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_86);
x_97 = lean_unsigned_to_nat(4u);
x_98 = lean_nat_dec_lt(x_96, x_97);
lean_dec(x_96);
x_87 = x_98;
goto block_93;
}
else
{
uint8_t x_99; 
x_99 = 1;
x_87 = x_99;
goto block_93;
}
block_93:
{
uint8_t x_88; 
x_88 = l_coeDecidableEq(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4(x_3, x_89, x_90, x_89, x_85, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_86;
}
}
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_5, x_7, x_8, x_2, x_3);
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
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_12, x_14, x_15, x_2, x_3);
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
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_expr_eqv(x_5, x_9);
lean_dec(x_9);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_expr_eqv(x_3, x_11);
lean_dec(x_11);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = x_2 >> x_5;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7(x_21, x_22, lean_box(0), x_23, x_3);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6(x_3, x_4, x_2);
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
x_15 = l___private_Init_Lean_Meta_SynthInstance_6__getMaxSteps(x_10);
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
x_23 = l___private_Init_Lean_Meta_SynthInstance_2__preprocess___closed__1;
lean_inc(x_2);
x_24 = l_Lean_Meta_forallTelescopeReducing___rarg(x_20, x_23, x_2, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
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
x_60 = lean_ctor_get(x_26, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_26, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_26, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_26, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_26, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_26, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 2);
lean_inc(x_66);
x_67 = l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(x_66, x_25);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_26);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_187; lean_object* x_188; lean_object* x_200; lean_object* x_201; 
x_69 = lean_ctor_get(x_26, 5);
lean_dec(x_69);
x_70 = lean_ctor_get(x_26, 4);
lean_dec(x_70);
x_71 = lean_ctor_get(x_26, 3);
lean_dec(x_71);
x_72 = lean_ctor_get(x_26, 2);
lean_dec(x_72);
x_73 = lean_ctor_get(x_26, 1);
lean_dec(x_73);
x_74 = lean_ctor_get(x_26, 0);
lean_dec(x_74);
lean_inc(x_61);
x_200 = l_Lean_MetavarContext_incDepth(x_61);
lean_ctor_set(x_26, 1, x_200);
lean_inc(x_2);
lean_inc(x_25);
x_201 = l___private_Init_Lean_Meta_SynthInstance_5__preprocessOutParam(x_25, x_2, x_26);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_251; lean_object* x_252; lean_object* x_262; uint8_t x_263; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_262 = lean_ctor_get(x_203, 4);
lean_inc(x_262);
x_263 = lean_ctor_get_uint8(x_262, sizeof(void*)*1);
lean_dec(x_262);
if (x_263 == 0)
{
uint8_t x_264; 
x_264 = l_String_posOfAux___main___closed__2;
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_265 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_266 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_265, x_2, x_203);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_unbox(x_267);
lean_dec(x_267);
x_251 = x_269;
x_252 = x_268;
goto block_261;
}
else
{
uint8_t x_270; 
x_270 = 0;
x_251 = x_270;
x_252 = x_203;
goto block_261;
}
}
else
{
uint8_t x_271; 
x_271 = l_String_posOfAux___main___closed__1;
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_272 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_273 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_272, x_2, x_203);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = lean_unbox(x_274);
lean_dec(x_274);
x_251 = x_276;
x_252 = x_275;
goto block_261;
}
else
{
uint8_t x_277; 
x_277 = 0;
x_251 = x_277;
x_252 = x_203;
goto block_261;
}
}
block_250:
{
lean_object* x_205; 
lean_inc(x_2);
x_205 = l_Lean_Meta_SynthInstance_main(x_202, x_15, x_2, x_204);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
lean_dec(x_22);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_75 = x_206;
x_76 = x_207;
goto block_186;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_223; lean_object* x_224; lean_object* x_232; uint8_t x_233; 
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_dec(x_205);
x_209 = lean_ctor_get(x_206, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_210 = x_206;
} else {
 lean_dec_ref(x_206);
 x_210 = lean_box(0);
}
x_232 = lean_ctor_get(x_208, 4);
lean_inc(x_232);
x_233 = lean_ctor_get_uint8(x_232, sizeof(void*)*1);
lean_dec(x_232);
if (x_233 == 0)
{
uint8_t x_234; 
x_234 = l_String_posOfAux___main___closed__2;
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_236 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_235, x_2, x_208);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_unbox(x_237);
lean_dec(x_237);
x_223 = x_239;
x_224 = x_238;
goto block_231;
}
else
{
uint8_t x_240; 
x_240 = 0;
x_223 = x_240;
x_224 = x_208;
goto block_231;
}
}
else
{
uint8_t x_241; 
x_241 = l_String_posOfAux___main___closed__1;
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_242 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_243 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_242, x_2, x_208);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_unbox(x_244);
lean_dec(x_244);
x_223 = x_246;
x_224 = x_245;
goto block_231;
}
else
{
uint8_t x_247; 
x_247 = 0;
x_223 = x_247;
x_224 = x_208;
goto block_231;
}
}
block_222:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_212 = l_Lean_Meta_instantiateMVars(x_209, x_2, x_211);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = l_Lean_Meta_hasAssignableMVar(x_213, x_2, x_214);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_unbox(x_216);
lean_dec(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_dec(x_215);
if (lean_is_scalar(x_210)) {
 x_219 = lean_alloc_ctor(1, 1, 0);
} else {
 x_219 = x_210;
}
lean_ctor_set(x_219, 0, x_213);
x_75 = x_219;
x_76 = x_218;
goto block_186;
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_213);
lean_dec(x_210);
x_220 = lean_ctor_get(x_215, 1);
lean_inc(x_220);
lean_dec(x_215);
x_221 = lean_box(0);
x_75 = x_221;
x_76 = x_220;
goto block_186;
}
}
block_231:
{
if (x_223 == 0)
{
x_211 = x_224;
goto block_222;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_inc(x_209);
x_225 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_225, 0, x_209);
x_226 = l_Lean_Meta_synthInstance_x3f___closed__6;
x_227 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
x_228 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_229 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_228, x_227, x_2, x_224);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_211 = x_230;
goto block_222;
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_248 = lean_ctor_get(x_205, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_205, 1);
lean_inc(x_249);
lean_dec(x_205);
x_187 = x_248;
x_188 = x_249;
goto block_199;
}
}
block_261:
{
if (x_251 == 0)
{
x_204 = x_252;
goto block_250;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_inc(x_25);
x_253 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_253, 0, x_25);
x_254 = l_Lean_Meta_synthInstance_x3f___closed__9;
x_255 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
lean_inc(x_202);
x_256 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_256, 0, x_202);
x_257 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_259 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_258, x_257, x_2, x_252);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
x_204 = x_260;
goto block_250;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_278 = lean_ctor_get(x_201, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_201, 1);
lean_inc(x_279);
lean_dec(x_201);
x_187 = x_278;
x_188 = x_279;
goto block_199;
}
block_186:
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 4);
x_79 = lean_ctor_get(x_76, 1);
lean_dec(x_79);
lean_inc(x_78);
lean_ctor_set(x_76, 1, x_61);
if (lean_obj_tag(x_75) == 0)
{
lean_dec(x_78);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = x_75;
x_29 = x_76;
goto block_59;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_106; lean_object* x_107; uint8_t x_115; 
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_81 = x_75;
} else {
 lean_dec_ref(x_75);
 x_81 = lean_box(0);
}
x_115 = lean_ctor_get_uint8(x_78, sizeof(void*)*1);
lean_dec(x_78);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = l_String_posOfAux___main___closed__2;
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_117 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_118 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_117, x_2, x_76);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_unbox(x_119);
lean_dec(x_119);
x_106 = x_121;
x_107 = x_120;
goto block_114;
}
else
{
uint8_t x_122; 
x_122 = 0;
x_106 = x_122;
x_107 = x_76;
goto block_114;
}
}
else
{
uint8_t x_123; 
x_123 = l_String_posOfAux___main___closed__1;
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_124 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_125 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_124, x_2, x_76);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_unbox(x_126);
lean_dec(x_126);
x_106 = x_128;
x_107 = x_127;
goto block_114;
}
else
{
uint8_t x_129; 
x_129 = 0;
x_106 = x_129;
x_107 = x_76;
goto block_114;
}
}
block_105:
{
lean_object* x_83; 
lean_inc(x_2);
lean_inc(x_80);
x_83 = l_Lean_Meta_inferType(x_80, x_2, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_86, 0, x_5);
lean_ctor_set(x_86, 1, x_6);
lean_ctor_set(x_86, 2, x_7);
lean_ctor_set(x_86, 3, x_8);
lean_ctor_set(x_86, 4, x_9);
lean_inc(x_25);
x_87 = l_Lean_Meta_isExprDefEq(x_25, x_84, x_86, x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_2);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_box(0);
x_28 = x_91;
x_29 = x_90;
goto block_59;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_dec(x_87);
x_93 = l_Lean_Meta_instantiateMVars(x_80, x_2, x_92);
lean_dec(x_2);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
if (lean_is_scalar(x_81)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_81;
}
lean_ctor_set(x_96, 0, x_94);
x_28 = x_96;
x_29 = x_95;
goto block_59;
}
}
else
{
uint8_t x_97; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_87);
if (x_97 == 0)
{
return x_87;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_87, 0);
x_99 = lean_ctor_get(x_87, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_87);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_101 = !lean_is_exclusive(x_83);
if (x_101 == 0)
{
return x_83;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_83, 0);
x_103 = lean_ctor_get(x_83, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_83);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
block_114:
{
if (x_106 == 0)
{
x_82 = x_107;
goto block_105;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_inc(x_80);
x_108 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_108, 0, x_80);
x_109 = l_Lean_Meta_synthInstance_x3f___closed__3;
x_110 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_112 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_111, x_110, x_2, x_107);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_82 = x_113;
goto block_105;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_76, 0);
x_131 = lean_ctor_get(x_76, 2);
x_132 = lean_ctor_get(x_76, 3);
x_133 = lean_ctor_get(x_76, 4);
x_134 = lean_ctor_get(x_76, 5);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_76);
lean_inc(x_133);
x_135 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_61);
lean_ctor_set(x_135, 2, x_131);
lean_ctor_set(x_135, 3, x_132);
lean_ctor_set(x_135, 4, x_133);
lean_ctor_set(x_135, 5, x_134);
if (lean_obj_tag(x_75) == 0)
{
lean_dec(x_133);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = x_75;
x_29 = x_135;
goto block_59;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_162; lean_object* x_163; uint8_t x_171; 
x_136 = lean_ctor_get(x_75, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_137 = x_75;
} else {
 lean_dec_ref(x_75);
 x_137 = lean_box(0);
}
x_171 = lean_ctor_get_uint8(x_133, sizeof(void*)*1);
lean_dec(x_133);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = l_String_posOfAux___main___closed__2;
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_173 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_174 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_173, x_2, x_135);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_unbox(x_175);
lean_dec(x_175);
x_162 = x_177;
x_163 = x_176;
goto block_170;
}
else
{
uint8_t x_178; 
x_178 = 0;
x_162 = x_178;
x_163 = x_135;
goto block_170;
}
}
else
{
uint8_t x_179; 
x_179 = l_String_posOfAux___main___closed__1;
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_180 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_181 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_180, x_2, x_135);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_unbox(x_182);
lean_dec(x_182);
x_162 = x_184;
x_163 = x_183;
goto block_170;
}
else
{
uint8_t x_185; 
x_185 = 0;
x_162 = x_185;
x_163 = x_135;
goto block_170;
}
}
block_161:
{
lean_object* x_139; 
lean_inc(x_2);
lean_inc(x_136);
x_139 = l_Lean_Meta_inferType(x_136, x_2, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_142, 0, x_5);
lean_ctor_set(x_142, 1, x_6);
lean_ctor_set(x_142, 2, x_7);
lean_ctor_set(x_142, 3, x_8);
lean_ctor_set(x_142, 4, x_9);
lean_inc(x_25);
x_143 = l_Lean_Meta_isExprDefEq(x_25, x_140, x_142, x_141);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_unbox(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_2);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_147 = lean_box(0);
x_28 = x_147;
x_29 = x_146;
goto block_59;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
lean_dec(x_143);
x_149 = l_Lean_Meta_instantiateMVars(x_136, x_2, x_148);
lean_dec(x_2);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
if (lean_is_scalar(x_137)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_137;
}
lean_ctor_set(x_152, 0, x_150);
x_28 = x_152;
x_29 = x_151;
goto block_59;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
x_153 = lean_ctor_get(x_143, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_143, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_155 = x_143;
} else {
 lean_dec_ref(x_143);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_157 = lean_ctor_get(x_139, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_139, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_159 = x_139;
} else {
 lean_dec_ref(x_139);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
block_170:
{
if (x_162 == 0)
{
x_138 = x_163;
goto block_161;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_inc(x_136);
x_164 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_164, 0, x_136);
x_165 = l_Lean_Meta_synthInstance_x3f___closed__3;
x_166 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_168 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_167, x_166, x_2, x_163);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_138 = x_169;
goto block_161;
}
}
}
}
}
block_199:
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_188, 1);
lean_dec(x_190);
lean_ctor_set(x_188, 1, x_61);
if (lean_is_scalar(x_22)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_22;
 lean_ctor_set_tag(x_191, 1);
}
lean_ctor_set(x_191, 0, x_187);
lean_ctor_set(x_191, 1, x_188);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_192 = lean_ctor_get(x_188, 0);
x_193 = lean_ctor_get(x_188, 2);
x_194 = lean_ctor_get(x_188, 3);
x_195 = lean_ctor_get(x_188, 4);
x_196 = lean_ctor_get(x_188, 5);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_188);
x_197 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_61);
lean_ctor_set(x_197, 2, x_193);
lean_ctor_set(x_197, 3, x_194);
lean_ctor_set(x_197, 4, x_195);
lean_ctor_set(x_197, 5, x_196);
if (lean_is_scalar(x_22)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_22;
 lean_ctor_set_tag(x_198, 1);
}
lean_ctor_set(x_198, 0, x_187);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_340; lean_object* x_341; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_26);
lean_inc(x_61);
x_351 = l_Lean_MetavarContext_incDepth(x_61);
x_352 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_352, 0, x_60);
lean_ctor_set(x_352, 1, x_351);
lean_ctor_set(x_352, 2, x_62);
lean_ctor_set(x_352, 3, x_63);
lean_ctor_set(x_352, 4, x_64);
lean_ctor_set(x_352, 5, x_65);
lean_inc(x_2);
lean_inc(x_25);
x_353 = l___private_Init_Lean_Meta_SynthInstance_5__preprocessOutParam(x_25, x_2, x_352);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_403; lean_object* x_404; lean_object* x_414; uint8_t x_415; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_414 = lean_ctor_get(x_355, 4);
lean_inc(x_414);
x_415 = lean_ctor_get_uint8(x_414, sizeof(void*)*1);
lean_dec(x_414);
if (x_415 == 0)
{
uint8_t x_416; 
x_416 = l_String_posOfAux___main___closed__2;
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; 
x_417 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_418 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_417, x_2, x_355);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
x_421 = lean_unbox(x_419);
lean_dec(x_419);
x_403 = x_421;
x_404 = x_420;
goto block_413;
}
else
{
uint8_t x_422; 
x_422 = 0;
x_403 = x_422;
x_404 = x_355;
goto block_413;
}
}
else
{
uint8_t x_423; 
x_423 = l_String_posOfAux___main___closed__1;
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_424 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_425 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_424, x_2, x_355);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
x_428 = lean_unbox(x_426);
lean_dec(x_426);
x_403 = x_428;
x_404 = x_427;
goto block_413;
}
else
{
uint8_t x_429; 
x_429 = 0;
x_403 = x_429;
x_404 = x_355;
goto block_413;
}
}
block_402:
{
lean_object* x_357; 
lean_inc(x_2);
x_357 = l_Lean_Meta_SynthInstance_main(x_354, x_15, x_2, x_356);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
lean_dec(x_22);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; 
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_280 = x_358;
x_281 = x_359;
goto block_339;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_375; lean_object* x_376; lean_object* x_384; uint8_t x_385; 
x_360 = lean_ctor_get(x_357, 1);
lean_inc(x_360);
lean_dec(x_357);
x_361 = lean_ctor_get(x_358, 0);
lean_inc(x_361);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_362 = x_358;
} else {
 lean_dec_ref(x_358);
 x_362 = lean_box(0);
}
x_384 = lean_ctor_get(x_360, 4);
lean_inc(x_384);
x_385 = lean_ctor_get_uint8(x_384, sizeof(void*)*1);
lean_dec(x_384);
if (x_385 == 0)
{
uint8_t x_386; 
x_386 = l_String_posOfAux___main___closed__2;
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; 
x_387 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_388 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_387, x_2, x_360);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = lean_unbox(x_389);
lean_dec(x_389);
x_375 = x_391;
x_376 = x_390;
goto block_383;
}
else
{
uint8_t x_392; 
x_392 = 0;
x_375 = x_392;
x_376 = x_360;
goto block_383;
}
}
else
{
uint8_t x_393; 
x_393 = l_String_posOfAux___main___closed__1;
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_394 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_395 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_394, x_2, x_360);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = lean_unbox(x_396);
lean_dec(x_396);
x_375 = x_398;
x_376 = x_397;
goto block_383;
}
else
{
uint8_t x_399; 
x_399 = 0;
x_375 = x_399;
x_376 = x_360;
goto block_383;
}
}
block_374:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_364 = l_Lean_Meta_instantiateMVars(x_361, x_2, x_363);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = l_Lean_Meta_hasAssignableMVar(x_365, x_2, x_366);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_unbox(x_368);
lean_dec(x_368);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_367, 1);
lean_inc(x_370);
lean_dec(x_367);
if (lean_is_scalar(x_362)) {
 x_371 = lean_alloc_ctor(1, 1, 0);
} else {
 x_371 = x_362;
}
lean_ctor_set(x_371, 0, x_365);
x_280 = x_371;
x_281 = x_370;
goto block_339;
}
else
{
lean_object* x_372; lean_object* x_373; 
lean_dec(x_365);
lean_dec(x_362);
x_372 = lean_ctor_get(x_367, 1);
lean_inc(x_372);
lean_dec(x_367);
x_373 = lean_box(0);
x_280 = x_373;
x_281 = x_372;
goto block_339;
}
}
block_383:
{
if (x_375 == 0)
{
x_363 = x_376;
goto block_374;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_inc(x_361);
x_377 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_377, 0, x_361);
x_378 = l_Lean_Meta_synthInstance_x3f___closed__6;
x_379 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_377);
x_380 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_381 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_380, x_379, x_2, x_376);
x_382 = lean_ctor_get(x_381, 1);
lean_inc(x_382);
lean_dec(x_381);
x_363 = x_382;
goto block_374;
}
}
}
}
else
{
lean_object* x_400; lean_object* x_401; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_400 = lean_ctor_get(x_357, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_357, 1);
lean_inc(x_401);
lean_dec(x_357);
x_340 = x_400;
x_341 = x_401;
goto block_350;
}
}
block_413:
{
if (x_403 == 0)
{
x_356 = x_404;
goto block_402;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_inc(x_25);
x_405 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_405, 0, x_25);
x_406 = l_Lean_Meta_synthInstance_x3f___closed__9;
x_407 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
lean_inc(x_354);
x_408 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_408, 0, x_354);
x_409 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
x_410 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_411 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_410, x_409, x_2, x_404);
x_412 = lean_ctor_get(x_411, 1);
lean_inc(x_412);
lean_dec(x_411);
x_356 = x_412;
goto block_402;
}
}
}
else
{
lean_object* x_430; lean_object* x_431; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_430 = lean_ctor_get(x_353, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_353, 1);
lean_inc(x_431);
lean_dec(x_353);
x_340 = x_430;
x_341 = x_431;
goto block_350;
}
block_339:
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 2);
lean_inc(x_283);
x_284 = lean_ctor_get(x_281, 3);
lean_inc(x_284);
x_285 = lean_ctor_get(x_281, 4);
lean_inc(x_285);
x_286 = lean_ctor_get(x_281, 5);
lean_inc(x_286);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 lean_ctor_release(x_281, 2);
 lean_ctor_release(x_281, 3);
 lean_ctor_release(x_281, 4);
 lean_ctor_release(x_281, 5);
 x_287 = x_281;
} else {
 lean_dec_ref(x_281);
 x_287 = lean_box(0);
}
lean_inc(x_285);
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(0, 6, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_282);
lean_ctor_set(x_288, 1, x_61);
lean_ctor_set(x_288, 2, x_283);
lean_ctor_set(x_288, 3, x_284);
lean_ctor_set(x_288, 4, x_285);
lean_ctor_set(x_288, 5, x_286);
if (lean_obj_tag(x_280) == 0)
{
lean_dec(x_285);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = x_280;
x_29 = x_288;
goto block_59;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_315; lean_object* x_316; uint8_t x_324; 
x_289 = lean_ctor_get(x_280, 0);
lean_inc(x_289);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 x_290 = x_280;
} else {
 lean_dec_ref(x_280);
 x_290 = lean_box(0);
}
x_324 = lean_ctor_get_uint8(x_285, sizeof(void*)*1);
lean_dec(x_285);
if (x_324 == 0)
{
uint8_t x_325; 
x_325 = l_String_posOfAux___main___closed__2;
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_326 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_327 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_326, x_2, x_288);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = lean_unbox(x_328);
lean_dec(x_328);
x_315 = x_330;
x_316 = x_329;
goto block_323;
}
else
{
uint8_t x_331; 
x_331 = 0;
x_315 = x_331;
x_316 = x_288;
goto block_323;
}
}
else
{
uint8_t x_332; 
x_332 = l_String_posOfAux___main___closed__1;
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_333 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_334 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_333, x_2, x_288);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_337 = lean_unbox(x_335);
lean_dec(x_335);
x_315 = x_337;
x_316 = x_336;
goto block_323;
}
else
{
uint8_t x_338; 
x_338 = 0;
x_315 = x_338;
x_316 = x_288;
goto block_323;
}
}
block_314:
{
lean_object* x_292; 
lean_inc(x_2);
lean_inc(x_289);
x_292 = l_Lean_Meta_inferType(x_289, x_2, x_291);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_295, 0, x_5);
lean_ctor_set(x_295, 1, x_6);
lean_ctor_set(x_295, 2, x_7);
lean_ctor_set(x_295, 3, x_8);
lean_ctor_set(x_295, 4, x_9);
lean_inc(x_25);
x_296 = l_Lean_Meta_isExprDefEq(x_25, x_293, x_295, x_294);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; uint8_t x_298; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_unbox(x_297);
lean_dec(x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_2);
x_299 = lean_ctor_get(x_296, 1);
lean_inc(x_299);
lean_dec(x_296);
x_300 = lean_box(0);
x_28 = x_300;
x_29 = x_299;
goto block_59;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_301 = lean_ctor_get(x_296, 1);
lean_inc(x_301);
lean_dec(x_296);
x_302 = l_Lean_Meta_instantiateMVars(x_289, x_2, x_301);
lean_dec(x_2);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
if (lean_is_scalar(x_290)) {
 x_305 = lean_alloc_ctor(1, 1, 0);
} else {
 x_305 = x_290;
}
lean_ctor_set(x_305, 0, x_303);
x_28 = x_305;
x_29 = x_304;
goto block_59;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
x_306 = lean_ctor_get(x_296, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_296, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_308 = x_296;
} else {
 lean_dec_ref(x_296);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_310 = lean_ctor_get(x_292, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_292, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_312 = x_292;
} else {
 lean_dec_ref(x_292);
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
block_323:
{
if (x_315 == 0)
{
x_291 = x_316;
goto block_314;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_inc(x_289);
x_317 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_317, 0, x_289);
x_318 = l_Lean_Meta_synthInstance_x3f___closed__3;
x_319 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_317);
x_320 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_321 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_320, x_319, x_2, x_316);
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
lean_dec(x_321);
x_291 = x_322;
goto block_314;
}
}
}
}
block_350:
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 2);
lean_inc(x_343);
x_344 = lean_ctor_get(x_341, 3);
lean_inc(x_344);
x_345 = lean_ctor_get(x_341, 4);
lean_inc(x_345);
x_346 = lean_ctor_get(x_341, 5);
lean_inc(x_346);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 lean_ctor_release(x_341, 4);
 lean_ctor_release(x_341, 5);
 x_347 = x_341;
} else {
 lean_dec_ref(x_341);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(0, 6, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_342);
lean_ctor_set(x_348, 1, x_61);
lean_ctor_set(x_348, 2, x_343);
lean_ctor_set(x_348, 3, x_344);
lean_ctor_set(x_348, 4, x_345);
lean_ctor_set(x_348, 5, x_346);
if (lean_is_scalar(x_22)) {
 x_349 = lean_alloc_ctor(1, 2, 0);
} else {
 x_349 = x_22;
 lean_ctor_set_tag(x_349, 1);
}
lean_ctor_set(x_349, 0, x_340);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
else
{
lean_object* x_432; lean_object* x_433; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_432 = lean_ctor_get(x_67, 0);
lean_inc(x_432);
lean_dec(x_67);
if (lean_is_scalar(x_22)) {
 x_433 = lean_alloc_ctor(0, 2, 0);
} else {
 x_433 = x_22;
}
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_26);
return x_433;
}
block_59:
{
uint8_t x_30; uint8_t x_31; 
x_30 = l_Lean_Expr_hasMVar(x_25);
x_31 = l_coeDecidableEq(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 2);
lean_inc(x_28);
x_36 = l_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(x_35, x_25, x_28);
lean_ctor_set(x_33, 2, x_36);
if (lean_is_scalar(x_27)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_27;
}
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
x_40 = lean_ctor_get(x_33, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
lean_inc(x_28);
x_41 = l_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(x_40, x_25, x_28);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_29, 2, x_42);
if (lean_is_scalar(x_27)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_27;
}
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_29);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_44 = lean_ctor_get(x_29, 2);
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
x_47 = lean_ctor_get(x_29, 3);
x_48 = lean_ctor_get(x_29, 4);
x_49 = lean_ctor_get(x_29, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_44);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_44, 2);
lean_inc(x_52);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 x_53 = x_44;
} else {
 lean_dec_ref(x_44);
 x_53 = lean_box(0);
}
lean_inc(x_28);
x_54 = l_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(x_52, x_25, x_28);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 3, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_54);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_46);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set(x_56, 4, x_48);
lean_ctor_set(x_56, 5, x_49);
if (lean_is_scalar(x_27)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_27;
}
lean_ctor_set(x_57, 0, x_28);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec(x_25);
if (lean_is_scalar(x_27)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_27;
}
lean_ctor_set(x_58, 0, x_28);
lean_ctor_set(x_58, 1, x_29);
return x_58;
}
}
}
else
{
uint8_t x_434; 
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_434 = !lean_is_exclusive(x_24);
if (x_434 == 0)
{
return x_24;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_24, 0);
x_436 = lean_ctor_get(x_24, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_24);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; uint8_t x_445; uint8_t x_446; uint8_t x_447; lean_object* x_448; uint8_t x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_438 = lean_ctor_get(x_2, 0);
x_439 = lean_ctor_get(x_2, 1);
x_440 = lean_ctor_get(x_2, 2);
x_441 = lean_ctor_get(x_2, 3);
x_442 = lean_ctor_get(x_2, 4);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_2);
x_443 = lean_ctor_get(x_438, 0);
lean_inc(x_443);
x_444 = lean_ctor_get_uint8(x_438, sizeof(void*)*1 + 2);
x_445 = lean_ctor_get_uint8(x_438, sizeof(void*)*1 + 3);
x_446 = lean_ctor_get_uint8(x_438, sizeof(void*)*1 + 4);
x_447 = lean_ctor_get_uint8(x_438, sizeof(void*)*1 + 5);
x_448 = l___private_Init_Lean_Meta_SynthInstance_6__getMaxSteps(x_443);
x_449 = 1;
x_450 = 2;
x_451 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_451, 0, x_443);
lean_ctor_set_uint8(x_451, sizeof(void*)*1, x_449);
lean_ctor_set_uint8(x_451, sizeof(void*)*1 + 1, x_449);
lean_ctor_set_uint8(x_451, sizeof(void*)*1 + 2, x_444);
lean_ctor_set_uint8(x_451, sizeof(void*)*1 + 3, x_445);
lean_ctor_set_uint8(x_451, sizeof(void*)*1 + 4, x_446);
lean_ctor_set_uint8(x_451, sizeof(void*)*1 + 5, x_447);
lean_ctor_set_uint8(x_451, sizeof(void*)*1 + 6, x_450);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
x_452 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_439);
lean_ctor_set(x_452, 2, x_440);
lean_ctor_set(x_452, 3, x_441);
lean_ctor_set(x_452, 4, x_442);
x_453 = l_Lean_Meta_instantiateMVars(x_1, x_452, x_3);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_456 = x_453;
} else {
 lean_dec_ref(x_453);
 x_456 = lean_box(0);
}
x_457 = l___private_Init_Lean_Meta_SynthInstance_2__preprocess___closed__1;
lean_inc(x_452);
x_458 = l_Lean_Meta_forallTelescopeReducing___rarg(x_454, x_457, x_452, x_455);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_461 = x_458;
} else {
 lean_dec_ref(x_458);
 x_461 = lean_box(0);
}
x_483 = lean_ctor_get(x_460, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_460, 1);
lean_inc(x_484);
x_485 = lean_ctor_get(x_460, 2);
lean_inc(x_485);
x_486 = lean_ctor_get(x_460, 3);
lean_inc(x_486);
x_487 = lean_ctor_get(x_460, 4);
lean_inc(x_487);
x_488 = lean_ctor_get(x_460, 5);
lean_inc(x_488);
x_489 = lean_ctor_get(x_485, 2);
lean_inc(x_489);
x_490 = l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(x_489, x_459);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_552; lean_object* x_553; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 lean_ctor_release(x_460, 4);
 lean_ctor_release(x_460, 5);
 x_491 = x_460;
} else {
 lean_dec_ref(x_460);
 x_491 = lean_box(0);
}
lean_inc(x_484);
x_563 = l_Lean_MetavarContext_incDepth(x_484);
if (lean_is_scalar(x_491)) {
 x_564 = lean_alloc_ctor(0, 6, 0);
} else {
 x_564 = x_491;
}
lean_ctor_set(x_564, 0, x_483);
lean_ctor_set(x_564, 1, x_563);
lean_ctor_set(x_564, 2, x_485);
lean_ctor_set(x_564, 3, x_486);
lean_ctor_set(x_564, 4, x_487);
lean_ctor_set(x_564, 5, x_488);
lean_inc(x_452);
lean_inc(x_459);
x_565 = l___private_Init_Lean_Meta_SynthInstance_5__preprocessOutParam(x_459, x_452, x_564);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; uint8_t x_615; lean_object* x_616; lean_object* x_626; uint8_t x_627; 
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_565, 1);
lean_inc(x_567);
lean_dec(x_565);
x_626 = lean_ctor_get(x_567, 4);
lean_inc(x_626);
x_627 = lean_ctor_get_uint8(x_626, sizeof(void*)*1);
lean_dec(x_626);
if (x_627 == 0)
{
uint8_t x_628; 
x_628 = l_String_posOfAux___main___closed__2;
if (x_628 == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint8_t x_633; 
x_629 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_630 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_629, x_452, x_567);
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_630, 1);
lean_inc(x_632);
lean_dec(x_630);
x_633 = lean_unbox(x_631);
lean_dec(x_631);
x_615 = x_633;
x_616 = x_632;
goto block_625;
}
else
{
uint8_t x_634; 
x_634 = 0;
x_615 = x_634;
x_616 = x_567;
goto block_625;
}
}
else
{
uint8_t x_635; 
x_635 = l_String_posOfAux___main___closed__1;
if (x_635 == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; 
x_636 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_637 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_636, x_452, x_567);
x_638 = lean_ctor_get(x_637, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_637, 1);
lean_inc(x_639);
lean_dec(x_637);
x_640 = lean_unbox(x_638);
lean_dec(x_638);
x_615 = x_640;
x_616 = x_639;
goto block_625;
}
else
{
uint8_t x_641; 
x_641 = 0;
x_615 = x_641;
x_616 = x_567;
goto block_625;
}
}
block_614:
{
lean_object* x_569; 
lean_inc(x_452);
x_569 = l_Lean_Meta_SynthInstance_main(x_566, x_448, x_452, x_568);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; 
lean_dec(x_456);
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; 
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec(x_569);
x_492 = x_570;
x_493 = x_571;
goto block_551;
}
else
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_587; lean_object* x_588; lean_object* x_596; uint8_t x_597; 
x_572 = lean_ctor_get(x_569, 1);
lean_inc(x_572);
lean_dec(x_569);
x_573 = lean_ctor_get(x_570, 0);
lean_inc(x_573);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 x_574 = x_570;
} else {
 lean_dec_ref(x_570);
 x_574 = lean_box(0);
}
x_596 = lean_ctor_get(x_572, 4);
lean_inc(x_596);
x_597 = lean_ctor_get_uint8(x_596, sizeof(void*)*1);
lean_dec(x_596);
if (x_597 == 0)
{
uint8_t x_598; 
x_598 = l_String_posOfAux___main___closed__2;
if (x_598 == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; 
x_599 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_600 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_599, x_452, x_572);
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
x_603 = lean_unbox(x_601);
lean_dec(x_601);
x_587 = x_603;
x_588 = x_602;
goto block_595;
}
else
{
uint8_t x_604; 
x_604 = 0;
x_587 = x_604;
x_588 = x_572;
goto block_595;
}
}
else
{
uint8_t x_605; 
x_605 = l_String_posOfAux___main___closed__1;
if (x_605 == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; 
x_606 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_607 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_606, x_452, x_572);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
lean_dec(x_607);
x_610 = lean_unbox(x_608);
lean_dec(x_608);
x_587 = x_610;
x_588 = x_609;
goto block_595;
}
else
{
uint8_t x_611; 
x_611 = 0;
x_587 = x_611;
x_588 = x_572;
goto block_595;
}
}
block_586:
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; 
x_576 = l_Lean_Meta_instantiateMVars(x_573, x_452, x_575);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec(x_576);
x_579 = l_Lean_Meta_hasAssignableMVar(x_577, x_452, x_578);
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_unbox(x_580);
lean_dec(x_580);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; 
x_582 = lean_ctor_get(x_579, 1);
lean_inc(x_582);
lean_dec(x_579);
if (lean_is_scalar(x_574)) {
 x_583 = lean_alloc_ctor(1, 1, 0);
} else {
 x_583 = x_574;
}
lean_ctor_set(x_583, 0, x_577);
x_492 = x_583;
x_493 = x_582;
goto block_551;
}
else
{
lean_object* x_584; lean_object* x_585; 
lean_dec(x_577);
lean_dec(x_574);
x_584 = lean_ctor_get(x_579, 1);
lean_inc(x_584);
lean_dec(x_579);
x_585 = lean_box(0);
x_492 = x_585;
x_493 = x_584;
goto block_551;
}
}
block_595:
{
if (x_587 == 0)
{
x_575 = x_588;
goto block_586;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_inc(x_573);
x_589 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_589, 0, x_573);
x_590 = l_Lean_Meta_synthInstance_x3f___closed__6;
x_591 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_589);
x_592 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_593 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_592, x_591, x_452, x_588);
x_594 = lean_ctor_get(x_593, 1);
lean_inc(x_594);
lean_dec(x_593);
x_575 = x_594;
goto block_586;
}
}
}
}
else
{
lean_object* x_612; lean_object* x_613; 
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_452);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
x_612 = lean_ctor_get(x_569, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_569, 1);
lean_inc(x_613);
lean_dec(x_569);
x_552 = x_612;
x_553 = x_613;
goto block_562;
}
}
block_625:
{
if (x_615 == 0)
{
x_568 = x_616;
goto block_614;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_inc(x_459);
x_617 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_617, 0, x_459);
x_618 = l_Lean_Meta_synthInstance_x3f___closed__9;
x_619 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_619, 0, x_617);
lean_ctor_set(x_619, 1, x_618);
lean_inc(x_566);
x_620 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_620, 0, x_566);
x_621 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_621, 0, x_619);
lean_ctor_set(x_621, 1, x_620);
x_622 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_623 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_622, x_621, x_452, x_616);
x_624 = lean_ctor_get(x_623, 1);
lean_inc(x_624);
lean_dec(x_623);
x_568 = x_624;
goto block_614;
}
}
}
else
{
lean_object* x_642; lean_object* x_643; 
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_452);
lean_dec(x_448);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
x_642 = lean_ctor_get(x_565, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_565, 1);
lean_inc(x_643);
lean_dec(x_565);
x_552 = x_642;
x_553 = x_643;
goto block_562;
}
block_551:
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 2);
lean_inc(x_495);
x_496 = lean_ctor_get(x_493, 3);
lean_inc(x_496);
x_497 = lean_ctor_get(x_493, 4);
lean_inc(x_497);
x_498 = lean_ctor_get(x_493, 5);
lean_inc(x_498);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 lean_ctor_release(x_493, 2);
 lean_ctor_release(x_493, 3);
 lean_ctor_release(x_493, 4);
 lean_ctor_release(x_493, 5);
 x_499 = x_493;
} else {
 lean_dec_ref(x_493);
 x_499 = lean_box(0);
}
lean_inc(x_497);
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(0, 6, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_494);
lean_ctor_set(x_500, 1, x_484);
lean_ctor_set(x_500, 2, x_495);
lean_ctor_set(x_500, 3, x_496);
lean_ctor_set(x_500, 4, x_497);
lean_ctor_set(x_500, 5, x_498);
if (lean_obj_tag(x_492) == 0)
{
lean_dec(x_497);
lean_dec(x_452);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
x_462 = x_492;
x_463 = x_500;
goto block_482;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_527; lean_object* x_528; uint8_t x_536; 
x_501 = lean_ctor_get(x_492, 0);
lean_inc(x_501);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 x_502 = x_492;
} else {
 lean_dec_ref(x_492);
 x_502 = lean_box(0);
}
x_536 = lean_ctor_get_uint8(x_497, sizeof(void*)*1);
lean_dec(x_497);
if (x_536 == 0)
{
uint8_t x_537; 
x_537 = l_String_posOfAux___main___closed__2;
if (x_537 == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; 
x_538 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_539 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_538, x_452, x_500);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
x_542 = lean_unbox(x_540);
lean_dec(x_540);
x_527 = x_542;
x_528 = x_541;
goto block_535;
}
else
{
uint8_t x_543; 
x_543 = 0;
x_527 = x_543;
x_528 = x_500;
goto block_535;
}
}
else
{
uint8_t x_544; 
x_544 = l_String_posOfAux___main___closed__1;
if (x_544 == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
x_545 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_546 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_545, x_452, x_500);
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec(x_546);
x_549 = lean_unbox(x_547);
lean_dec(x_547);
x_527 = x_549;
x_528 = x_548;
goto block_535;
}
else
{
uint8_t x_550; 
x_550 = 0;
x_527 = x_550;
x_528 = x_500;
goto block_535;
}
}
block_526:
{
lean_object* x_504; 
lean_inc(x_452);
lean_inc(x_501);
x_504 = l_Lean_Meta_inferType(x_501, x_452, x_503);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec(x_504);
x_507 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_507, 0, x_438);
lean_ctor_set(x_507, 1, x_439);
lean_ctor_set(x_507, 2, x_440);
lean_ctor_set(x_507, 3, x_441);
lean_ctor_set(x_507, 4, x_442);
lean_inc(x_459);
x_508 = l_Lean_Meta_isExprDefEq(x_459, x_505, x_507, x_506);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; uint8_t x_510; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_unbox(x_509);
lean_dec(x_509);
if (x_510 == 0)
{
lean_object* x_511; lean_object* x_512; 
lean_dec(x_502);
lean_dec(x_501);
lean_dec(x_452);
x_511 = lean_ctor_get(x_508, 1);
lean_inc(x_511);
lean_dec(x_508);
x_512 = lean_box(0);
x_462 = x_512;
x_463 = x_511;
goto block_482;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_513 = lean_ctor_get(x_508, 1);
lean_inc(x_513);
lean_dec(x_508);
x_514 = l_Lean_Meta_instantiateMVars(x_501, x_452, x_513);
lean_dec(x_452);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 1);
lean_inc(x_516);
lean_dec(x_514);
if (lean_is_scalar(x_502)) {
 x_517 = lean_alloc_ctor(1, 1, 0);
} else {
 x_517 = x_502;
}
lean_ctor_set(x_517, 0, x_515);
x_462 = x_517;
x_463 = x_516;
goto block_482;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_502);
lean_dec(x_501);
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_452);
x_518 = lean_ctor_get(x_508, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_508, 1);
lean_inc(x_519);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_520 = x_508;
} else {
 lean_dec_ref(x_508);
 x_520 = lean_box(0);
}
if (lean_is_scalar(x_520)) {
 x_521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_521 = x_520;
}
lean_ctor_set(x_521, 0, x_518);
lean_ctor_set(x_521, 1, x_519);
return x_521;
}
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec(x_502);
lean_dec(x_501);
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_452);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
x_522 = lean_ctor_get(x_504, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_504, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 lean_ctor_release(x_504, 1);
 x_524 = x_504;
} else {
 lean_dec_ref(x_504);
 x_524 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 2, 0);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_522);
lean_ctor_set(x_525, 1, x_523);
return x_525;
}
}
block_535:
{
if (x_527 == 0)
{
x_503 = x_528;
goto block_526;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_inc(x_501);
x_529 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_529, 0, x_501);
x_530 = l_Lean_Meta_synthInstance_x3f___closed__3;
x_531 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_529);
x_532 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_533 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_532, x_531, x_452, x_528);
x_534 = lean_ctor_get(x_533, 1);
lean_inc(x_534);
lean_dec(x_533);
x_503 = x_534;
goto block_526;
}
}
}
}
block_562:
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_553, 2);
lean_inc(x_555);
x_556 = lean_ctor_get(x_553, 3);
lean_inc(x_556);
x_557 = lean_ctor_get(x_553, 4);
lean_inc(x_557);
x_558 = lean_ctor_get(x_553, 5);
lean_inc(x_558);
if (lean_is_exclusive(x_553)) {
 lean_ctor_release(x_553, 0);
 lean_ctor_release(x_553, 1);
 lean_ctor_release(x_553, 2);
 lean_ctor_release(x_553, 3);
 lean_ctor_release(x_553, 4);
 lean_ctor_release(x_553, 5);
 x_559 = x_553;
} else {
 lean_dec_ref(x_553);
 x_559 = lean_box(0);
}
if (lean_is_scalar(x_559)) {
 x_560 = lean_alloc_ctor(0, 6, 0);
} else {
 x_560 = x_559;
}
lean_ctor_set(x_560, 0, x_554);
lean_ctor_set(x_560, 1, x_484);
lean_ctor_set(x_560, 2, x_555);
lean_ctor_set(x_560, 3, x_556);
lean_ctor_set(x_560, 4, x_557);
lean_ctor_set(x_560, 5, x_558);
if (lean_is_scalar(x_456)) {
 x_561 = lean_alloc_ctor(1, 2, 0);
} else {
 x_561 = x_456;
 lean_ctor_set_tag(x_561, 1);
}
lean_ctor_set(x_561, 0, x_552);
lean_ctor_set(x_561, 1, x_560);
return x_561;
}
}
else
{
lean_object* x_644; lean_object* x_645; 
lean_dec(x_488);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_452);
lean_dec(x_448);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
x_644 = lean_ctor_get(x_490, 0);
lean_inc(x_644);
lean_dec(x_490);
if (lean_is_scalar(x_456)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_456;
}
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_460);
return x_645;
}
block_482:
{
uint8_t x_464; uint8_t x_465; 
x_464 = l_Lean_Expr_hasMVar(x_459);
x_465 = l_coeDecidableEq(x_464);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_466 = lean_ctor_get(x_463, 2);
lean_inc(x_466);
x_467 = lean_ctor_get(x_463, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_463, 1);
lean_inc(x_468);
x_469 = lean_ctor_get(x_463, 3);
lean_inc(x_469);
x_470 = lean_ctor_get(x_463, 4);
lean_inc(x_470);
x_471 = lean_ctor_get(x_463, 5);
lean_inc(x_471);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 lean_ctor_release(x_463, 4);
 lean_ctor_release(x_463, 5);
 x_472 = x_463;
} else {
 lean_dec_ref(x_463);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_466, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_466, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_466, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 x_476 = x_466;
} else {
 lean_dec_ref(x_466);
 x_476 = lean_box(0);
}
lean_inc(x_462);
x_477 = l_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(x_475, x_459, x_462);
if (lean_is_scalar(x_476)) {
 x_478 = lean_alloc_ctor(0, 3, 0);
} else {
 x_478 = x_476;
}
lean_ctor_set(x_478, 0, x_473);
lean_ctor_set(x_478, 1, x_474);
lean_ctor_set(x_478, 2, x_477);
if (lean_is_scalar(x_472)) {
 x_479 = lean_alloc_ctor(0, 6, 0);
} else {
 x_479 = x_472;
}
lean_ctor_set(x_479, 0, x_467);
lean_ctor_set(x_479, 1, x_468);
lean_ctor_set(x_479, 2, x_478);
lean_ctor_set(x_479, 3, x_469);
lean_ctor_set(x_479, 4, x_470);
lean_ctor_set(x_479, 5, x_471);
if (lean_is_scalar(x_461)) {
 x_480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_480 = x_461;
}
lean_ctor_set(x_480, 0, x_462);
lean_ctor_set(x_480, 1, x_479);
return x_480;
}
else
{
lean_object* x_481; 
lean_dec(x_459);
if (lean_is_scalar(x_461)) {
 x_481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_481 = x_461;
}
lean_ctor_set(x_481, 0, x_462);
lean_ctor_set(x_481, 1, x_463);
return x_481;
}
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_456);
lean_dec(x_452);
lean_dec(x_448);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
x_646 = lean_ctor_get(x_458, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_458, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_648 = x_458;
} else {
 lean_dec_ref(x_458);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(1, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_646);
lean_ctor_set(x_649, 1, x_647);
return x_649;
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
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(x_1, x_2);
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
lean_object* l___private_Init_Lean_Meta_SynthInstance_7__regTraceClasses(lean_object* x_1) {
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
lean_object* initialize_Init_Default(lean_object*);
lean_object* initialize_Init_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Init_Lean_Meta_Instances(lean_object*);
lean_object* initialize_Init_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Init_Lean_Meta_AbstractMVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_SynthInstance(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Instances(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_AbstractMVars(lean_io_mk_world());
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
l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__1 = _init_l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__1);
l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__2 = _init_l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__2);
l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__3 = _init_l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__3);
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
l___private_Init_Lean_Meta_SynthInstance_2__preprocess___closed__1 = _init_l___private_Init_Lean_Meta_SynthInstance_2__preprocess___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_SynthInstance_2__preprocess___closed__1);
l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1 = _init_l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1);
l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2 = _init_l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2);
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
res = l___private_Init_Lean_Meta_SynthInstance_7__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

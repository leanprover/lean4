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
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_12__regTraceClasses(lean_object*);
lean_object* l_Lean_Meta_maxStepsOption___closed__6;
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkGeneratorNode_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_out_param(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_addAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__3;
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_Meta_SynthInstance_tryAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4(lean_object*, lean_object*);
lean_object* l_Option_toLOption___rarg(lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__3;
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Meta_SynthInstance_6__preprocessOutParam___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_4__preprocessLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___closed__1;
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__6(lean_object*, size_t, lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__3;
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_maxStepsOption___closed__5;
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__10(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_6__preprocessOutParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__1;
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_maxStepsOption(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_33__withMCtxImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__2;
lean_object* l_Std_PersistentHashMap_findAtAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Answer_inhabited;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__6(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__2;
lean_object* l_Lean_Meta_SynthInstance_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__3;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_maxStepsOption___closed__3;
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___rarg(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3;
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__2;
lean_object* l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__1;
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__1;
lean_object* l_Lean_MetavarContext_hasAssignableMVar___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
lean_object* l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__3;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__3___boxed(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__11(lean_object*);
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__2;
extern lean_object* l_Lean_Meta_AbstractMVarsResult_inhabited___closed__1;
lean_object* l_Lean_Meta_setSynthPendingRef___closed__1;
uint8_t l_Lean_Meta_SynthInstance_Waiter_isRoot(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__3;
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_SynthInstance_newSubgoal___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TagAttribute_Inhabited___closed__1;
lean_object* l_Lean_Meta_abstractMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__3;
extern lean_object* l_Lean_Exception_inhabited___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocess___closed__1;
lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__4;
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4;
extern lean_object* l_Std_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___closed__3;
lean_object* l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_4__preprocessLevels___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__1;
lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_main___spec__1(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mapMetaM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__9;
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4(lean_object*);
extern lean_object* l_Lean_Meta_isDefEqStuckExceptionId;
lean_object* l_Lean_Meta_isExprMVarAssigned___at___private_Lean_Meta_SynthInstance_11__synthPendingImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f___at___private_Lean_Meta_Basic_26__withNewFVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_modifyTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_inferTypeRef;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__2(lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1;
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_GeneratorNode_inhabited;
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___boxed(lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__2(lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getGlobalInstances___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_11__synthPendingImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1;
lean_object* l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__1(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__3___closed__2;
lean_object* l_Lean_Meta_setSynthPendingRef(lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr(lean_object*);
lean_object* l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__5;
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__1;
lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__3___closed__1;
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
extern lean_object* l_Lean_MessageData_hasCoeOfArrayExpr___closed__2;
lean_object* l_Lean_Meta_SynthInstance_resume___closed__3;
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2___boxed(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getNextToResume___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
lean_object* l_Lean_Meta_SynthInstance_resume___closed__7;
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__1;
lean_object* l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__2;
lean_object* l___private_Lean_Meta_SynthInstance_10__synthInstanceImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_9__trySynthInstanceImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1___boxed(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__1;
lean_object* l_Lean_Meta_SynthInstance_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__1;
lean_object* l_Lean_Meta_SynthInstance_synth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__2;
uint8_t l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__1;
lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
lean_object* l_Lean_Meta_trySynthInstance(lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1___boxed(lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__2;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2;
lean_object* l_Lean_Meta_SynthInstance_wakeUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__1;
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__1(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_SynthInstance_isNewAnswer(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4;
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__1;
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__6;
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__4;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__7(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__2;
lean_object* l_Lean_Meta_SynthInstance_Waiter_isRoot___boxed(lean_object*);
extern lean_object* l_Lean_Meta_synthPendingRef;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__3;
extern lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___boxed(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__2;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__2;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1;
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__2;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__2;
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__3___closed__3;
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKey(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_7__getMaxSteps(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getNextToResume(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_isNewAnswer___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isLevelAssignable(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
lean_object* l_Lean_Meta_SynthInstance_Consumernode_inhabited;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2;
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned___at___private_Lean_Meta_SynthInstance_11__synthPendingImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__3;
lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_modifyTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__1;
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__2___boxed(lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___closed__2;
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Meta_SynthInstance_generate___closed__1;
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1;
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__2;
lean_object* l_Lean_Meta_maxStepsOption___closed__1;
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__2;
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_maxStepsDefault;
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1;
lean_object* l_Lean_Meta_maxStepsOption___closed__2;
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1(lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isExprAssignable(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1;
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__1;
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__2;
lean_object* l_Lean_Meta_SynthInstance_consume(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__1;
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__4;
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2;
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessLevels___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__3;
lean_object* l_Lean_Meta_SynthInstance_tryAnswer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___closed__2;
lean_object* l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_has_out_params(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__2;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__2;
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___closed__2;
lean_object* l___private_Lean_Meta_SynthInstance_7__getMaxSteps___boxed(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__5;
lean_object* l_Lean_Meta_SynthInstance_main___closed__1;
lean_object* l_Lean_Meta_SynthInstance_resume___closed__1;
lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___closed__3;
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_maxStepsOption___closed__4;
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__3(lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__3;
lean_object* l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inferTCGoalsLR");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instruct type class resolution procedure to solve goals from left to right for this instance");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1___boxed), 5, 0);
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
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
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
static lean_object* _init_l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1() {
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
static lean_object* _init_l_Lean_Meta_SynthInstance_GeneratorNode_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1() {
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
static lean_object* _init_l_Lean_Meta_SynthInstance_Consumernode_inhabited() {
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
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_tc");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2() {
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
static lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__3() {
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
static lean_object* _init_l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1() {
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
static lean_object* _init_l_Lean_Meta_SynthInstance_Answer_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_mapMetaM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_1(x_3, x_4);
x_11 = lean_apply_7(x_1, lean_box(0), x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_SynthM_inhabited___rarg), 1, 0);
return x_7;
}
}
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_SynthM_inhabited(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_10, x_2, x_3, x_4, x_5, x_14);
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
x_22 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_21, x_2, x_3, x_4, x_5, x_24);
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
static lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.SynthInstance");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("global instance is not a constant");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
x_2 = lean_unsigned_to_nat(176u);
x_3 = lean_unsigned_to_nat(13u);
x_4 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = x_2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_28; 
x_12 = lean_array_fget(x_2, x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_fset(x_2, x_1, x_13);
x_28 = x_12;
if (lean_obj_tag(x_28) == 4)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_29, x_3, x_4, x_5, x_6, x_7);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_expr_update_const(x_28, x_32);
lean_ctor_set(x_30, 0, x_33);
x_15 = x_30;
goto block_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_expr_update_const(x_28, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_15 = x_37;
goto block_27;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
x_38 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_39 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3;
x_40 = lean_panic_fn(x_38, x_39);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_41 = lean_apply_5(x_40, x_3, x_4, x_5, x_6, x_7);
x_15 = x_41;
goto block_27;
}
block_27:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_1, x_18);
x_20 = x_16;
x_21 = lean_array_fset(x_14, x_1, x_20);
lean_dec(x_1);
x_1 = x_19;
x_2 = x_21;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
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
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_6 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_MessageData_hasCoeOfArrayExpr___closed__2;
x_9 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_2, x_7, x_8);
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
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
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("synthInstance");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("globalInstances");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_2 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_isClass_x3f___at___private_Lean_Meta_Basic_26__withNewFVar___spec__1(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_indentExpr(x_3);
x_13 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__3;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_14, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = l_Lean_Meta_getGlobalInstances___rarg(x_7, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_Meta_DiscrTree_getUnify___rarg(x_19, x_3, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = x_22;
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2), 7, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_24);
x_27 = x_26;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = lean_apply_5(x_27, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed), 3, 2);
lean_closure_set(x_31, 0, x_3);
lean_closure_set(x_31, 1, x_29);
x_32 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7;
x_33 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_32, x_31, x_4, x_5, x_6, x_7, x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(x_1, x_17, x_1, x_25, x_29);
lean_dec(x_17);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(x_1, x_17, x_1, x_25, x_29);
lean_dec(x_17);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
return x_28;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_28, 0);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_28);
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
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_21);
if (x_44 == 0)
{
return x_21;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getInstances___lambda__2___boxed), 8, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_1, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_getInstances___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_getInstances___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_SynthInstance_mkGeneratorNode_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_9, x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
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
lean_object* x_19; uint8_t x_20; 
lean_free_object(x_14);
x_19 = lean_st_ref_get(x_4, x_17);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_array_get_size(x_16);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_16);
lean_ctor_set(x_24, 4, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_get_size(x_16);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_1);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_16);
lean_ctor_set(x_30, 4, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_box(0);
lean_ctor_set(x_14, 0, x_33);
return x_14;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = l_Array_isEmpty___rarg(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_st_ref_get(x_4, x_35);
lean_dec(x_4);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_array_get_size(x_34);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_1);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_34);
lean_ctor_set(x_43, 4, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
if (lean_is_scalar(x_40)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_40;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_34);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
return x_14;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_14);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_8);
if (x_52 == 0)
{
return x_8;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_8, 0);
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_8);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lean_checkTraceOption(x_8, x_1);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 3);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_11);
lean_inc(x_9);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Std_PersistentArray_push___rarg(x_20, x_22);
lean_ctor_set(x_15, 0, x_23);
x_24 = lean_st_ref_set(x_7, x_14, x_16);
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
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_11);
lean_inc(x_9);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_9);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Std_PersistentArray_push___rarg(x_32, x_34);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_31);
lean_ctor_set(x_14, 3, x_36);
x_37 = lean_st_ref_set(x_7, x_14, x_16);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_ctor_get(x_14, 1);
x_44 = lean_ctor_get(x_14, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_14);
x_45 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_46 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_47 = x_15;
} else {
 lean_dec_ref(x_15);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_11);
lean_inc(x_9);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_9);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Std_PersistentArray_push___rarg(x_46, x_49);
if (lean_is_scalar(x_47)) {
 x_51 = lean_alloc_ctor(0, 1, 1);
} else {
 x_51 = x_47;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_45);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_52, 2, x_44);
lean_ctor_set(x_52, 3, x_51);
x_53 = lean_st_ref_set(x_7, x_52, x_16);
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
x_56 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
lean_inc(x_1);
x_20 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_box(0);
x_31 = lean_apply_1(x_2, x_30);
x_32 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_1, x_31, x_3, x_4, x_5, x_6, x_7, x_29);
return x_32;
}
}
}
}
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_1, x_2, x_7);
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
x_14 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_1, x_2, x_12);
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
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(x_2, x_10);
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
x_17 = l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_13, x_15);
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
x_18 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_2, x_3, x_10);
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
x_26 = l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(x_2, x_25);
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
x_32 = l_Std_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_28, x_30);
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
x_34 = l_Std_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__9(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_7(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg), 8, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_1(x_2, x_3);
x_10 = l___private_Lean_Meta_Basic_33__withMCtxImp___rarg(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
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
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = l_Lean_mkOptionalNode___closed__2;
x_22 = lean_array_push(x_21, x_3);
x_23 = l_Array_empty___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_st_ref_take(x_5, x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_26, 3);
x_31 = lean_array_push(x_29, x_20);
x_32 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_30, x_1, x_24);
lean_ctor_set(x_26, 3, x_32);
lean_ctor_set(x_26, 1, x_31);
x_33 = lean_st_ref_set(x_5, x_26, x_27);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
x_42 = lean_ctor_get(x_26, 2);
x_43 = lean_ctor_get(x_26, 3);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_44 = lean_array_push(x_41, x_20);
x_45 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_43, x_1, x_24);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_45);
x_47 = lean_st_ref_set(x_5, x_46, x_27);
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
}
else
{
uint8_t x_52; 
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_11);
if (x_52 == 0)
{
return x_11;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_11);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
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
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_2 = l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_2);
x_12 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_13 = lean_alloc_closure((void*)(l_Lean_MonadTracer_trace___at_Lean_Meta_SynthInstance_newSubgoal___spec__1___boxed), 8, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_newSubgoal___lambda__1___boxed), 10, 3);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_4);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg), 8, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg(x_1, x_15, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_SynthInstance_newSubgoal___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MonadTracer_trace___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_newSubgoal___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_SynthInstance_newSubgoal___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
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
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(x_11, x_1);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_ctor_get(x_13, 3);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(x_15, x_1);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
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
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_SynthM_inhabited___boxed), 6, 1);
lean_closure_set(x_1, 0, lean_box(0));
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
x_2 = lean_unsigned_to_nat(220u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Lean_Meta_SynthInstance_getEntry___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_SynthInstance_getEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_SynthInstance_getEntry___closed__1;
x_12 = l_Lean_Meta_SynthInstance_getEntry___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
x_14 = lean_apply_6(x_13, x_2, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_getEntry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_getEntry(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_nat_dec_eq(x_9, x_10);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_5, 3);
lean_dec(x_14);
x_15 = lean_ctor_get(x_5, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_9, x_18);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_19);
x_20 = l_Lean_Meta_inferTypeRef;
x_21 = lean_st_ref_get(x_20, x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_apply_6(x_22, x_1, x_3, x_4, x_5, x_6, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_5);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_9, x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_10);
lean_ctor_set(x_27, 3, x_11);
x_28 = l_Lean_Meta_inferTypeRef;
x_29 = lean_st_ref_get(x_28, x_7);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_apply_6(x_30, x_1, x_3, x_4, x_27, x_6, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_33 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_34 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_33, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasMVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_4, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_Lean_MetavarContext_instantiateMVars(x_14, x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_17);
x_18 = lean_st_ref_set(x_4, x_11, x_12);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_26 = l_Lean_MetavarContext_instantiateMVars(x_23, x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_st_ref_set(x_4, x_29, x_12);
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
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_11);
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
x_15 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1___boxed), 7, 1);
lean_closure_set(x_9, 0, x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1___boxed), 8, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg), 8, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_inferType___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_mkTableKeyFor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
if (lean_obj_tag(x_8) == 7)
{
lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_8, 2);
lean_inc(x_36);
x_37 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_38 = lean_array_get_size(x_4);
x_39 = lean_expr_instantiate_rev_range(x_35, x_5, x_38, x_4);
lean_dec(x_38);
lean_dec(x_35);
lean_inc(x_9);
lean_inc(x_3);
x_40 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(x_3, x_39, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = 0;
x_44 = lean_box(0);
x_45 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_1);
x_46 = l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2(x_1, x_2, x_41, x_43, x_44, x_45, x_9, x_10, x_11, x_12, x_42);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_47);
x_49 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_3, x_3, x_45, x_47);
lean_inc(x_49);
x_50 = l_Lean_mkApp(x_7, x_49);
x_51 = (uint8_t)((x_37 << 24) >> 61);
x_52 = l_Lean_BinderInfo_isInstImplicit(x_51);
x_53 = lean_array_push(x_4, x_49);
if (x_52 == 0)
{
lean_dec(x_47);
x_4 = x_53;
x_7 = x_50;
x_8 = x_36;
x_13 = x_48;
goto _start;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_6);
x_4 = x_53;
x_6 = x_55;
x_7 = x_50;
x_8 = x_36;
x_13 = x_48;
goto _start;
}
}
else
{
uint8_t x_57; 
lean_dec(x_36);
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
x_57 = !lean_is_exclusive(x_40);
if (x_57 == 0)
{
return x_40;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_40, 0);
x_59 = lean_ctor_get(x_40, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_40);
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
x_14 = x_61;
goto block_34;
}
block_34:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
x_15 = lean_array_get_size(x_4);
x_16 = lean_expr_instantiate_rev_range(x_8, x_5, x_15, x_4);
lean_dec(x_5);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_Expr_isForall(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_free_object(x_17);
x_5 = x_15;
x_8 = x_19;
x_13 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = l_Lean_Expr_isForall(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_7);
lean_ctor_set(x_27, 2, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
x_5 = x_15;
x_8 = x_24;
x_13 = x_25;
goto _start;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_15);
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
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_SynthInstance_getSubgoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Array_empty___closed__1;
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_4);
x_16 = l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(x_1, x_2, x_3, x_14, x_15, x_13, x_4, x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Expr_getAppFn___main(x_4);
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
x_26 = l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
x_27 = l_Lean_TagAttribute_hasTag(x_26, x_25, x_21);
lean_dec(x_21);
lean_dec(x_25);
if (x_27 == 0)
{
lean_ctor_set(x_22, 0, x_18);
return x_22;
}
else
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
x_39 = l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
x_40 = l_Lean_TagAttribute_hasTag(x_39, x_38, x_21);
lean_dec(x_21);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_18, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_18, 2);
lean_inc(x_44);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_45 = x_18;
} else {
 lean_dec_ref(x_18);
 x_45 = lean_box(0);
}
x_46 = l_List_reverse___rarg(x_42);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 3, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
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
x_51 = l_Lean_Expr_getAppFn___main(x_4);
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
x_58 = l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
x_59 = l_Lean_TagAttribute_hasTag(x_58, x_57, x_52);
lean_dec(x_52);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_60; 
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_49, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_49, 2);
lean_inc(x_63);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 x_64 = x_49;
} else {
 lean_dec_ref(x_49);
 x_64 = lean_box(0);
}
x_65 = l_List_reverse___rarg(x_61);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 3, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_63);
if (lean_is_scalar(x_56)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_56;
}
lean_ctor_set(x_67, 0, x_66);
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
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___rarg(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_9 = lean_st_ref_get(x_4, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_6, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = l_Std_HashMap_inhabited___closed__1;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = 1;
x_21 = 0;
x_22 = l_Lean_MetavarContext_MkBinding_mkBinding(x_20, x_17, x_1, x_2, x_21, x_21, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_st_ref_take(x_6, x_15);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_28, 2);
lean_dec(x_31);
lean_ctor_set(x_28, 2, x_26);
x_32 = lean_st_ref_set(x_6, x_28, x_29);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_34, x_3, x_4, x_5, x_6, x_33);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_25);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
x_42 = lean_ctor_get(x_28, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_26);
lean_ctor_set(x_43, 3, x_42);
x_44 = lean_st_ref_set(x_6, x_43, x_29);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_24, 0);
lean_inc(x_46);
lean_dec(x_24);
x_47 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_46, x_3, x_4, x_5, x_6, x_45);
lean_dec(x_3);
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
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_25);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_51 = lean_ctor_get(x_22, 1);
lean_inc(x_51);
lean_dec(x_22);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_52, x_3, x_4, x_5, x_6, x_15);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_st_ref_take(x_6, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_57, 2);
lean_dec(x_60);
lean_ctor_set(x_57, 2, x_55);
x_61 = lean_st_ref_set(x_6, x_57, x_58);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
x_64 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_63, x_3, x_4, x_5, x_6, x_62);
lean_dec(x_3);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_57, 0);
x_66 = lean_ctor_get(x_57, 1);
x_67 = lean_ctor_get(x_57, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_57);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_55);
lean_ctor_set(x_68, 3, x_67);
x_69 = lean_st_ref_set(x_6, x_68, x_58);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
x_72 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_71, x_3, x_4, x_5, x_6, x_70);
lean_dec(x_3);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_3);
lean_dec(x_1);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_2);
lean_ctor_set(x_73, 1, x_7);
return x_73;
}
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3;
x_6 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failure assigning");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__3;
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__9;
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tryResolve");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_2 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
lean_inc(x_17);
lean_inc(x_6);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___boxed), 3, 2);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__2;
x_20 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_19, x_18, x_7, x_8, x_9, x_10, x_14);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_6, x_17, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__3;
x_27 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_19, x_26, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
lean_inc(x_7);
x_35 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_5, x_16, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_4, x_36, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_15);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__4;
x_43 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_19, x_42, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
x_51 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__5;
x_52 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_19, x_51, x_7, x_8, x_9, x_10, x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_st_ref_get(x_8, x_53);
lean_dec(x_8);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_15);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_54, 0, x_59);
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_54, 0);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_54);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_15);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_66 = !lean_is_exclusive(x_38);
if (x_66 == 0)
{
return x_38;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_38, 0);
x_68 = lean_ctor_get(x_38, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_38);
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
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_35);
if (x_70 == 0)
{
return x_35;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_35, 0);
x_72 = lean_ctor_get(x_35, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_35);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_22);
if (x_74 == 0)
{
return x_22;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_22, 0);
x_76 = lean_ctor_get(x_22, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_22);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_12);
if (x_78 == 0)
{
return x_12;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_12, 0);
x_80 = lean_ctor_get(x_12, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_12);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_3, x_4, x_5, x_6, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5), 11, 4);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_1);
x_16 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_9, x_15, x_3, x_4, x_5, x_6, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_33__withMCtxImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolveCore), 7, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
x_214 = lean_st_ref_get(x_8, x_9);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_215, 3);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_ctor_get_uint8(x_216, sizeof(void*)*1);
lean_dec(x_216);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_214, 1);
lean_inc(x_218);
lean_dec(x_214);
x_219 = 0;
x_11 = x_219;
x_12 = x_218;
goto block_213;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_220 = lean_ctor_get(x_214, 1);
lean_inc(x_220);
lean_dec(x_214);
x_221 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__2;
x_222 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_221, x_5, x_6, x_7, x_8, x_220);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_unbox(x_223);
lean_dec(x_223);
x_11 = x_225;
x_12 = x_224;
goto block_213;
}
block_213:
{
if (x_11 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_st_ref_get(x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_8, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_19, 3);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = 0;
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_25);
x_26 = lean_st_ref_set(x_8, x_19, x_21);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_8);
x_28 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_8, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_take(x_8, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_34, 3);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_17);
x_40 = lean_st_ref_set(x_8, x_34, x_36);
lean_dec(x_8);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_29);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_17);
lean_ctor_set(x_34, 3, x_46);
x_47 = lean_st_ref_set(x_8, x_34, x_36);
lean_dec(x_8);
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
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_29);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_51 = lean_ctor_get(x_34, 0);
x_52 = lean_ctor_get(x_34, 1);
x_53 = lean_ctor_get(x_34, 2);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_34);
x_54 = lean_ctor_get(x_35, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_55 = x_35;
} else {
 lean_dec_ref(x_35);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 1, 1);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_17);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_57, 2, x_53);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_st_ref_set(x_8, x_57, x_36);
lean_dec(x_8);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_29);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_62 = lean_ctor_get(x_28, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_28, 1);
lean_inc(x_63);
lean_dec(x_28);
x_64 = lean_st_ref_get(x_8, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_take(x_8, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_67, 3);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_17);
x_73 = lean_st_ref_set(x_8, x_67, x_69);
lean_dec(x_8);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
lean_ctor_set_tag(x_73, 1);
lean_ctor_set(x_73, 0, x_62);
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_62);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_68, 0);
lean_inc(x_78);
lean_dec(x_68);
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_17);
lean_ctor_set(x_67, 3, x_79);
x_80 = lean_st_ref_set(x_8, x_67, x_69);
lean_dec(x_8);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
 lean_ctor_set_tag(x_83, 1);
}
lean_ctor_set(x_83, 0, x_62);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_84 = lean_ctor_get(x_67, 0);
x_85 = lean_ctor_get(x_67, 1);
x_86 = lean_ctor_get(x_67, 2);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_67);
x_87 = lean_ctor_get(x_68, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_88 = x_68;
} else {
 lean_dec_ref(x_68);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 1, 1);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_17);
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set(x_90, 2, x_86);
lean_ctor_set(x_90, 3, x_89);
x_91 = lean_st_ref_set(x_8, x_90, x_69);
lean_dec(x_8);
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
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
 lean_ctor_set_tag(x_94, 1);
}
lean_ctor_set(x_94, 0, x_62);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_20, 0);
lean_inc(x_95);
lean_dec(x_20);
x_96 = 0;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
lean_ctor_set(x_19, 3, x_97);
x_98 = lean_st_ref_set(x_8, x_19, x_21);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
lean_inc(x_8);
x_100 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_st_ref_get(x_8, x_102);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_st_ref_take(x_8, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_106, 2);
lean_inc(x_111);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 x_112 = x_106;
} else {
 lean_dec_ref(x_106);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_107, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 1, 1);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_112)) {
 x_116 = lean_alloc_ctor(0, 4, 0);
} else {
 x_116 = x_112;
}
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_110);
lean_ctor_set(x_116, 2, x_111);
lean_ctor_set(x_116, 3, x_115);
x_117 = lean_st_ref_set(x_8, x_116, x_108);
lean_dec(x_8);
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
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_101);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_121 = lean_ctor_get(x_100, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_100, 1);
lean_inc(x_122);
lean_dec(x_100);
x_123 = lean_st_ref_get(x_8, x_122);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_st_ref_take(x_8, x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_126, 2);
lean_inc(x_131);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 lean_ctor_release(x_126, 3);
 x_132 = x_126;
} else {
 lean_dec_ref(x_126);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_127, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_134 = x_127;
} else {
 lean_dec_ref(x_127);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 1, 1);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_132)) {
 x_136 = lean_alloc_ctor(0, 4, 0);
} else {
 x_136 = x_132;
}
lean_ctor_set(x_136, 0, x_129);
lean_ctor_set(x_136, 1, x_130);
lean_ctor_set(x_136, 2, x_131);
lean_ctor_set(x_136, 3, x_135);
x_137 = lean_st_ref_set(x_8, x_136, x_128);
lean_dec(x_8);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
 lean_ctor_set_tag(x_140, 1);
}
lean_ctor_set(x_140, 0, x_121);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_141 = lean_ctor_get(x_19, 0);
x_142 = lean_ctor_get(x_19, 1);
x_143 = lean_ctor_get(x_19, 2);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_19);
x_144 = lean_ctor_get(x_20, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_145 = x_20;
} else {
 lean_dec_ref(x_20);
 x_145 = lean_box(0);
}
x_146 = 0;
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 1, 1);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_146);
x_148 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_142);
lean_ctor_set(x_148, 2, x_143);
lean_ctor_set(x_148, 3, x_147);
x_149 = lean_st_ref_set(x_8, x_148, x_21);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
lean_inc(x_8);
x_151 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_st_ref_get(x_8, x_153);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_st_ref_take(x_8, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_157, 3);
lean_inc(x_158);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_157, 2);
lean_inc(x_162);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 lean_ctor_release(x_157, 2);
 lean_ctor_release(x_157, 3);
 x_163 = x_157;
} else {
 lean_dec_ref(x_157);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_158, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 x_165 = x_158;
} else {
 lean_dec_ref(x_158);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 1, 1);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_163)) {
 x_167 = lean_alloc_ctor(0, 4, 0);
} else {
 x_167 = x_163;
}
lean_ctor_set(x_167, 0, x_160);
lean_ctor_set(x_167, 1, x_161);
lean_ctor_set(x_167, 2, x_162);
lean_ctor_set(x_167, 3, x_166);
x_168 = lean_st_ref_set(x_8, x_167, x_159);
lean_dec(x_8);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_152);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_172 = lean_ctor_get(x_151, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_151, 1);
lean_inc(x_173);
lean_dec(x_151);
x_174 = lean_st_ref_get(x_8, x_173);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_st_ref_take(x_8, x_175);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_177, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_177, 2);
lean_inc(x_182);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_183 = x_177;
} else {
 lean_dec_ref(x_177);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_178, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 x_185 = x_178;
} else {
 lean_dec_ref(x_178);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 1, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_183)) {
 x_187 = lean_alloc_ctor(0, 4, 0);
} else {
 x_187 = x_183;
}
lean_ctor_set(x_187, 0, x_180);
lean_ctor_set(x_187, 1, x_181);
lean_ctor_set(x_187, 2, x_182);
lean_ctor_set(x_187, 3, x_186);
x_188 = lean_st_ref_set(x_8, x_187, x_179);
lean_dec(x_8);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
 lean_ctor_set_tag(x_191, 1);
}
lean_ctor_set(x_191, 0, x_172);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_ctor_get(x_7, 3);
lean_inc(x_192);
x_193 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(x_8, x_12);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_196 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__2;
x_200 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_194, x_199, x_192, x_5, x_6, x_7, x_8, x_198);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_200, 0);
lean_dec(x_202);
lean_ctor_set(x_200, 0, x_197);
return x_200;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec(x_200);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_197);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_196, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_196, 1);
lean_inc(x_206);
lean_dec(x_196);
x_207 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__2;
x_208 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_194, x_207, x_192, x_5, x_6, x_7, x_8, x_206);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_208, 0);
lean_dec(x_210);
lean_ctor_set_tag(x_208, 1);
lean_ctor_set(x_208, 0, x_205);
return x_208;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_205);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_tryResolve(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryAnswer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_4);
x_10 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_4);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_st_ref_get(x_4, x_19);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
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
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_tryAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_openAbstractMVarsResult), 6, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryAnswer___lambda__1), 7, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(x_1, x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryAnswer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SynthInstance_tryAnswer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("skip answer containing metavariables ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_wakeUp___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__3;
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_SynthInstance_wakeUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_st_ref_take(x_3, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_array_push(x_14, x_15);
lean_ctor_set(x_11, 2, x_16);
x_17 = lean_st_ref_set(x_3, x_11, x_12);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 2);
x_27 = lean_ctor_get(x_11, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_9);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_1);
x_29 = lean_array_push(x_26, x_28);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_27);
x_31 = lean_st_ref_set(x_3, x_30, x_12);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_57; uint8_t x_58; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_57 = lean_ctor_get(x_36, 0);
lean_inc(x_57);
x_58 = l_Array_isEmpty___rarg(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_37 = x_59;
goto block_56;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_36, 1);
lean_inc(x_60);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_eq(x_60, x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_box(0);
x_37 = x_63;
goto block_56;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_64 = lean_st_ref_take(x_3, x_8);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_36, 2);
lean_inc(x_67);
lean_dec(x_36);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = !lean_is_exclusive(x_65);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_65, 0);
lean_dec(x_70);
lean_ctor_set(x_65, 0, x_68);
x_71 = lean_st_ref_set(x_3, x_65, x_66);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
x_74 = lean_box(0);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_78 = lean_ctor_get(x_65, 1);
x_79 = lean_ctor_get(x_65, 2);
x_80 = lean_ctor_get(x_65, 3);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_65);
x_81 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_81, 0, x_68);
lean_ctor_set(x_81, 1, x_78);
lean_ctor_set(x_81, 2, x_79);
lean_ctor_set(x_81, 3, x_80);
x_82 = lean_st_ref_set(x_3, x_81, x_66);
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
x_85 = lean_box(0);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
}
block_56:
{
lean_object* x_38; 
lean_dec(x_37);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Meta_openAbstractMVarsResult(x_36, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_wakeUp___lambda__1___boxed), 2, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_45 = l_Lean_MonadTracer_trace___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_44, x_43, x_3, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_38);
if (x_52 == 0)
{
return x_38;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_38, 0);
x_54 = lean_ctor_get(x_38, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_38);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_wakeUp___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_wakeUp___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_wakeUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_wakeUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
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
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_3 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__3(x_2, x_14, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
}
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_abstractMVars(x_9, x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
x_15 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_14, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_12);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("newAnswer");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_2 = l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg___lambda__2___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___closed__2;
x_2 = l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__2;
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_2__mkAnswer___lambda__1___boxed), 8, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__4;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_2__mkAnswer___lambda__2___boxed), 7, 1);
lean_closure_set(x_13, 0, x_8);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(x_7, x_14, x_2, x_3, x_4, x_5, x_6);
return x_15;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l___private_Lean_Meta_SynthInstance_2__mkAnswer___lambda__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_2__mkAnswer___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_SynthInstance_2__mkAnswer___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_15 = l_Lean_Meta_SynthInstance_wakeUp(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_3, x_17);
lean_dec(x_3);
x_3 = x_18;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_addAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_SynthInstance_2__mkAnswer(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Meta_SynthInstance_getEntry(x_11, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = l_Lean_Meta_SynthInstance_isNewAnswer(x_18, x_9);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_free_object(x_12);
lean_inc(x_9);
x_21 = lean_array_push(x_18, x_9);
lean_inc(x_17);
lean_ctor_set(x_14, 1, x_21);
x_22 = lean_st_ref_take(x_2, x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_23, 3);
x_27 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_26, x_11, x_14);
lean_ctor_set(x_23, 3, x_27);
x_28 = lean_st_ref_set(x_2, x_23, x_24);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_9, x_17, x_30, x_2, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_2);
lean_dec(x_17);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
x_34 = lean_ctor_get(x_23, 2);
x_35 = lean_ctor_get(x_23, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_36 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_35, x_11, x_14);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_st_ref_set(x_2, x_37, x_24);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_9, x_17, x_40, x_2, x_3, x_4, x_5, x_6, x_39);
lean_dec(x_2);
lean_dec(x_17);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = l_Lean_Meta_SynthInstance_isNewAnswer(x_44, x_9);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_box(0);
lean_ctor_set(x_12, 0, x_46);
return x_12;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_free_object(x_12);
lean_inc(x_9);
x_47 = lean_array_push(x_44, x_9);
lean_inc(x_43);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_st_ref_take(x_2, x_42);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 3);
lean_inc(x_55);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 x_56 = x_50;
} else {
 lean_dec_ref(x_50);
 x_56 = lean_box(0);
}
x_57 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_55, x_11, x_48);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 4, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_54);
lean_ctor_set(x_58, 3, x_57);
x_59 = lean_st_ref_set(x_2, x_58, x_51);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_9, x_43, x_61, x_2, x_3, x_4, x_5, x_6, x_60);
lean_dec(x_2);
lean_dec(x_43);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_12, 0);
x_64 = lean_ctor_get(x_12, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_12);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
x_68 = l_Lean_Meta_SynthInstance_isNewAnswer(x_66, x_9);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_64);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_inc(x_9);
x_71 = lean_array_push(x_66, x_9);
lean_inc(x_65);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_st_ref_take(x_2, x_64);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_80 = x_74;
} else {
 lean_dec_ref(x_74);
 x_80 = lean_box(0);
}
x_81 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_79, x_11, x_72);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 4, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_77);
lean_ctor_set(x_82, 2, x_78);
lean_ctor_set(x_82, 3, x_81);
x_83 = lean_st_ref_set(x_2, x_82, x_75);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_9, x_65, x_85, x_2, x_3, x_4, x_5, x_6, x_84);
lean_dec(x_2);
lean_dec(x_65);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_12);
if (x_87 == 0)
{
return x_12;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_12, 0);
x_89 = lean_ctor_get(x_12, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_12);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_8);
if (x_91 == 0)
{
return x_8;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_8, 0);
x_93 = lean_ctor_get(x_8, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_8);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
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
lean_object* l_Lean_Meta_SynthInstance_consume(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_addAnswer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
lean_inc(x_12);
x_13 = l_Lean_Meta_SynthInstance_mkTableKeyFor(x_12, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_14, x_2, x_3, x_4, x_5, x_6, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_SynthInstance_newSubgoal(x_12, x_14, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_st_ref_take(x_2, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_23, 2);
x_27 = lean_ctor_get(x_23, 3);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(x_1, x_21, x_29, x_30, x_26);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_21, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_21, 0);
lean_dec(x_34);
x_35 = lean_array_push(x_28, x_11);
lean_ctor_set(x_21, 0, x_35);
x_36 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_27, x_14, x_21);
lean_ctor_set(x_23, 3, x_36);
lean_ctor_set(x_23, 2, x_31);
x_37 = lean_st_ref_set(x_2, x_23, x_24);
lean_dec(x_2);
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_21);
x_44 = lean_array_push(x_28, x_11);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_29);
x_46 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_27, x_14, x_45);
lean_ctor_set(x_23, 3, x_46);
lean_ctor_set(x_23, 2, x_31);
x_47 = lean_st_ref_set(x_2, x_23, x_24);
lean_dec(x_2);
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
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
x_54 = lean_ctor_get(x_23, 2);
x_55 = lean_ctor_get(x_23, 3);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_56 = lean_ctor_get(x_21, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(x_1, x_21, x_57, x_58, x_54);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_60 = x_21;
} else {
 lean_dec_ref(x_21);
 x_60 = lean_box(0);
}
x_61 = lean_array_push(x_56, x_11);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
x_63 = l_Std_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_55, x_14, x_62);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_53);
lean_ctor_set(x_64, 2, x_59);
lean_ctor_set(x_64, 3, x_63);
x_65 = lean_st_ref_set(x_2, x_64, x_24);
lean_dec(x_2);
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
else
{
uint8_t x_70; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_13);
if (x_70 == 0)
{
return x_13;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_13, 0);
x_72 = lean_ctor_get(x_13, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_13);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
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
lean_object* l_Lean_Meta_SynthInstance_getTop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1(x_10);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
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
lean_object* l_Lean_Meta_SynthInstance_getTop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_getTop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_SynthInstance_modifyTop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
x_16 = lean_nat_dec_lt(x_15, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_1);
x_17 = lean_st_ref_set(x_2, x_9, x_10);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_array_fget(x_12, x_15);
x_25 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_26 = lean_array_fset(x_12, x_15, x_25);
x_27 = lean_apply_1(x_1, x_24);
x_28 = lean_array_fset(x_26, x_15, x_27);
lean_dec(x_15);
lean_ctor_set(x_9, 1, x_28);
x_29 = lean_st_ref_set(x_2, x_9, x_10);
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
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_9, 0);
x_37 = lean_ctor_get(x_9, 1);
x_38 = lean_ctor_get(x_9, 2);
x_39 = lean_ctor_get(x_9, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_9);
x_40 = lean_array_get_size(x_37);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_sub(x_40, x_41);
x_43 = lean_nat_dec_lt(x_42, x_40);
lean_dec(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set(x_44, 2, x_38);
lean_ctor_set(x_44, 3, x_39);
x_45 = lean_st_ref_set(x_2, x_44, x_10);
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
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_array_fget(x_37, x_42);
x_51 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_52 = lean_array_fset(x_37, x_42, x_51);
x_53 = lean_apply_1(x_1, x_50);
x_54 = lean_array_fset(x_52, x_42, x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_36);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_38);
lean_ctor_set(x_55, 3, x_39);
x_56 = lean_st_ref_set(x_2, x_55, x_10);
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
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_modifyTop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_modifyTop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instance ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_generate___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Lean_Meta_SynthInstance_generate___lambda__1___closed__3;
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
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
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_2 = l_Lean_Meta_SynthInstance_generate___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_generate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = l_Lean_Meta_SynthInstance_getTop(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 4);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_19 = l_Lean_Expr_Inhabited;
x_20 = lean_array_get(x_19, x_13, x_18);
lean_dec(x_13);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_generate___lambda__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_23 = l_Lean_MonadTracer_trace___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_22, x_21, x_1, x_2, x_3, x_4, x_5, x_9);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_45 = lean_st_ref_take(x_1, x_24);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_array_get_size(x_49);
x_51 = lean_nat_sub(x_50, x_17);
x_52 = lean_nat_dec_lt(x_51, x_50);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
lean_dec(x_18);
x_53 = lean_st_ref_set(x_1, x_46, x_47);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_25 = x_54;
goto block_44;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_array_fget(x_49, x_51);
x_56 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_57 = lean_array_fset(x_49, x_51, x_56);
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_55, 4);
lean_dec(x_59);
lean_ctor_set(x_55, 4, x_18);
x_60 = lean_array_fset(x_57, x_51, x_55);
lean_dec(x_51);
lean_ctor_set(x_46, 1, x_60);
x_61 = lean_st_ref_set(x_1, x_46, x_47);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_25 = x_62;
goto block_44;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_55, 0);
x_64 = lean_ctor_get(x_55, 1);
x_65 = lean_ctor_get(x_55, 2);
x_66 = lean_ctor_get(x_55, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_55);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_66);
lean_ctor_set(x_67, 4, x_18);
x_68 = lean_array_fset(x_57, x_51, x_67);
lean_dec(x_51);
lean_ctor_set(x_46, 1, x_68);
x_69 = lean_st_ref_set(x_1, x_46, x_47);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_25 = x_70;
goto block_44;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_46, 0);
x_72 = lean_ctor_get(x_46, 1);
x_73 = lean_ctor_get(x_46, 2);
x_74 = lean_ctor_get(x_46, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_46);
x_75 = lean_array_get_size(x_72);
x_76 = lean_nat_sub(x_75, x_17);
x_77 = lean_nat_dec_lt(x_76, x_75);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_76);
lean_dec(x_18);
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set(x_78, 2, x_73);
lean_ctor_set(x_78, 3, x_74);
x_79 = lean_st_ref_set(x_1, x_78, x_47);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_25 = x_80;
goto block_44;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_81 = lean_array_fget(x_72, x_76);
x_82 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_83 = lean_array_fset(x_72, x_76, x_82);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 3);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 5, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_86);
lean_ctor_set(x_89, 3, x_87);
lean_ctor_set(x_89, 4, x_18);
x_90 = lean_array_fset(x_83, x_76, x_89);
lean_dec(x_76);
x_91 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_91, 0, x_71);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_73);
lean_ctor_set(x_91, 3, x_74);
x_92 = lean_st_ref_set(x_1, x_91, x_47);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_25 = x_93;
goto block_44;
}
}
block_44:
{
lean_object* x_26; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
x_26 = l_Lean_Meta_SynthInstance_tryResolve(x_12, x_10, x_20, x_1, x_2, x_3, x_4, x_5, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_11);
lean_ctor_set(x_38, 2, x_36);
lean_ctor_set(x_38, 3, x_37);
x_39 = l_Lean_Meta_SynthInstance_consume(x_38, x_1, x_2, x_3, x_4, x_5, x_35);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
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
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_st_ref_take(x_1, x_9);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_95, 1);
x_99 = lean_array_pop(x_98);
lean_ctor_set(x_95, 1, x_99);
x_100 = lean_st_ref_set(x_1, x_95, x_96);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 0);
lean_dec(x_102);
x_103 = lean_box(0);
lean_ctor_set(x_100, 0, x_103);
return x_100;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_dec(x_100);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_107 = lean_ctor_get(x_95, 0);
x_108 = lean_ctor_get(x_95, 1);
x_109 = lean_ctor_get(x_95, 2);
x_110 = lean_ctor_get(x_95, 3);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_95);
x_111 = lean_array_pop(x_108);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_109);
lean_ctor_set(x_112, 3, x_110);
x_113 = lean_st_ref_set(x_1, x_112, x_96);
lean_dec(x_1);
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
}
}
}
lean_object* l_Lean_Meta_SynthInstance_generate___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_generate___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1() {
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
lean_object* l_Lean_Meta_SynthInstance_getNextToResume(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(x_10);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_1, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 2);
x_17 = lean_array_pop(x_16);
lean_ctor_set(x_13, 2, x_17);
x_18 = lean_st_ref_set(x_1, x_13, x_14);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
x_25 = lean_ctor_get(x_13, 2);
x_26 = lean_ctor_get(x_13, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_27 = lean_array_pop(x_25);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_st_ref_set(x_1, x_28, x_14);
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
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
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
lean_object* l_Lean_Meta_SynthInstance_getNextToResume___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_getNextToResume(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
lean_dec(x_9);
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
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" <== ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_4 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Meta_inferType___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(x_1, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_inferType___at_Lean_Meta_SynthInstance_mkTableKeyFor___spec__1(x_2, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = l_Lean_Meta_SynthInstance_resume___lambda__3___closed__3;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_3, x_23, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
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
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resume found no remaining subgoals");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
x_2 = lean_unsigned_to_nat(417u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Lean_Meta_SynthInstance_resume___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resume");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_2 = l_Lean_Meta_SynthInstance_resume___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lambda__2___boxed), 8, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_resume___closed__6;
x_2 = l_Lean_Meta_SynthInstance_resume___closed__5;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_resume(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_SynthInstance_getNextToResume(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_Meta_SynthInstance_getEntry___closed__1;
x_13 = l_Lean_Meta_SynthInstance_resume___closed__2;
x_14 = lean_panic_fn(x_12, x_13);
x_15 = lean_apply_6(x_14, x_1, x_2, x_3, x_4, x_5, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
x_21 = lean_ctor_get(x_9, 2);
x_22 = lean_ctor_get(x_9, 3);
lean_dec(x_22);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_23);
x_25 = l_Lean_Meta_SynthInstance_tryAnswer(x_21, x_23, x_17, x_1, x_2, x_3, x_4, x_5, x_16);
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
lean_free_object(x_9);
lean_dec(x_20);
lean_dec(x_19);
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
x_35 = l_Lean_Meta_SynthInstance_resume___closed__4;
lean_inc(x_19);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lambda__3___boxed), 10, 3);
lean_closure_set(x_36, 0, x_19);
lean_closure_set(x_36, 1, x_23);
lean_closure_set(x_36, 2, x_35);
x_37 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_38 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg), 8, 2);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, x_36);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_34);
x_39 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg(x_34, x_38, x_1, x_2, x_3, x_4, x_5, x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_ctor_set(x_9, 3, x_24);
lean_ctor_set(x_9, 2, x_34);
x_41 = l_Lean_Meta_SynthInstance_consume(x_9, x_1, x_2, x_3, x_4, x_5, x_40);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_34);
lean_dec(x_24);
lean_free_object(x_9);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_9);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_9, 0);
x_51 = lean_ctor_get(x_9, 1);
x_52 = lean_ctor_get(x_9, 2);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_9);
x_53 = lean_ctor_get(x_10, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_10, 1);
lean_inc(x_54);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_53);
x_55 = l_Lean_Meta_SynthInstance_tryAnswer(x_52, x_53, x_17, x_1, x_2, x_3, x_4, x_5, x_16);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
lean_dec(x_56);
x_63 = l_Lean_Meta_SynthInstance_resume___closed__4;
lean_inc(x_50);
x_64 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_resume___lambda__3___boxed), 10, 3);
lean_closure_set(x_64, 0, x_50);
lean_closure_set(x_64, 1, x_53);
lean_closure_set(x_64, 2, x_63);
x_65 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_66 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_SynthInstance_newSubgoal___spec__10___rarg), 8, 2);
lean_closure_set(x_66, 0, x_65);
lean_closure_set(x_66, 1, x_64);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_62);
x_67 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_newSubgoal___spec__11___rarg(x_62, x_66, x_1, x_2, x_3, x_4, x_5, x_61);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_50);
lean_ctor_set(x_69, 1, x_51);
lean_ctor_set(x_69, 2, x_62);
lean_ctor_set(x_69, 3, x_54);
x_70 = l_Lean_Meta_SynthInstance_consume(x_69, x_1, x_2, x_3, x_4, x_5, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_62);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_ctor_get(x_55, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_55, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_77 = x_55;
} else {
 lean_dec_ref(x_55);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_resume___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SynthInstance_resume___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_SynthInstance_resume___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_SynthInstance_resume___lambda__3(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_Meta_SynthInstance_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_12 = l_Array_isEmpty___rarg(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_7);
lean_dec(x_9);
x_13 = l_Lean_Meta_SynthInstance_resume(x_1, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec(x_9);
x_27 = l_Array_isEmpty___rarg(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_free_object(x_7);
x_28 = l_Lean_Meta_SynthInstance_generate(x_1, x_2, x_3, x_4, x_5, x_10);
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
else
{
uint8_t x_41; lean_object* x_42; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = 0;
x_42 = lean_box(x_41);
lean_ctor_set(x_7, 0, x_42);
return x_7;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_7);
x_45 = lean_ctor_get(x_43, 2);
lean_inc(x_45);
x_46 = l_Array_isEmpty___rarg(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_43);
x_47 = l_Lean_Meta_SynthInstance_resume(x_1, x_2, x_3, x_4, x_5, x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
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
x_50 = 1;
x_51 = lean_box(x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_55 = x_47;
} else {
 lean_dec_ref(x_47);
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
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_43, 1);
lean_inc(x_57);
lean_dec(x_43);
x_58 = l_Array_isEmpty___rarg(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_Lean_Meta_SynthInstance_generate(x_1, x_2, x_3, x_4, x_5, x_44);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
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
x_62 = 1;
x_63 = lean_box(x_62);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_44);
return x_71;
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_getResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
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
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* l_Lean_Meta_SynthInstance_getResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SynthInstance_getResult(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("remaining fuel ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Nat_repr(x_1);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__3;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__3;
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("synthInstance is out of fuel");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__3;
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_synth___main___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_synth___main___lambda__3___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_synth___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_1, x_10);
lean_dec(x_1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_synth___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_14 = l_Lean_MonadTracer_trace___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_13, x_12, x_2, x_3, x_4, x_5, x_6, x_7);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Meta_SynthInstance_step(x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_Meta_SynthInstance_synth___main___closed__1;
x_21 = l_Lean_MonadTracer_trace___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_13, x_20, x_2, x_3, x_4, x_5, x_6, x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = l_Lean_Meta_SynthInstance_getResult(x_2, x_3, x_4, x_5, x_6, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_1 = x_11;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_29, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_29, 0, x_37);
return x_29;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_40 = x_30;
} else {
 lean_dec_ref(x_30);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
return x_16;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_1);
x_47 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_48 = l_Lean_Meta_SynthInstance_synth___main___closed__2;
x_49 = l_Lean_MonadTracer_trace___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_47, x_48, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_synth___main___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_synth___main___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_synth___main___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_synth___main___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_synth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SynthInstance_synth___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("main goal ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_main___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Lean_Meta_SynthInstance_main___lambda__1___closed__3;
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SynthInstance_main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Array_empty___closed__1;
x_3 = l_Lean_Meta_SynthInstance_main___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; 
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_main___lambda__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_1);
x_357 = lean_st_ref_get(x_6, x_7);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_358, 3);
lean_inc(x_359);
lean_dec(x_358);
x_360 = lean_ctor_get_uint8(x_359, sizeof(void*)*1);
lean_dec(x_359);
if (x_360 == 0)
{
lean_object* x_361; uint8_t x_362; 
x_361 = lean_ctor_get(x_357, 1);
lean_inc(x_361);
lean_dec(x_357);
x_362 = 0;
x_22 = x_362;
x_23 = x_361;
goto block_356;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_363 = lean_ctor_get(x_357, 1);
lean_inc(x_363);
lean_dec(x_357);
x_364 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_365 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_364, x_3, x_4, x_5, x_6, x_363);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = lean_unbox(x_366);
lean_dec(x_366);
x_22 = x_368;
x_23 = x_367;
goto block_356;
}
block_20:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
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
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
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
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
block_356:
{
if (x_22 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_24 = lean_st_ref_get(x_6, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get_uint8(x_26, sizeof(void*)*1);
lean_dec(x_26);
x_29 = lean_st_ref_take(x_6, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 3);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_36 = 0;
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_36);
x_37 = lean_st_ref_set(x_6, x_30, x_32);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_73 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_74 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_73, x_21, x_3, x_4, x_5, x_6, x_38);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
lean_inc(x_1);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_1);
x_77 = 0;
x_78 = lean_box(0);
lean_inc(x_3);
x_79 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_76, x_77, x_78, x_3, x_4, x_5, x_6, x_75);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_st_ref_get(x_4, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_85);
x_86 = l_Lean_Meta_SynthInstance_mkTableKey(x_85, x_1);
x_87 = l_Lean_Meta_SynthInstance_main___closed__2;
x_88 = lean_st_mk_ref(x_87, x_84);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_box(1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_89);
x_92 = l_Lean_Meta_SynthInstance_newSubgoal(x_85, x_86, x_80, x_91, x_89, x_3, x_4, x_5, x_6, x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
lean_inc(x_6);
lean_inc(x_89);
x_94 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_89, x_3, x_4, x_5, x_6, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_st_ref_get(x_89, x_96);
lean_dec(x_89);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_st_ref_get(x_6, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_ctor_get(x_100, 3);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get_uint8(x_102, sizeof(void*)*1);
lean_dec(x_102);
x_104 = lean_st_ref_take(x_6, x_101);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_105, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_105, 3);
lean_dec(x_109);
x_110 = !lean_is_exclusive(x_106);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_28);
x_111 = lean_st_ref_set(x_6, x_105, x_107);
lean_dec(x_6);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_111, 0);
lean_dec(x_113);
x_114 = lean_box(x_103);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_95);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_111, 0, x_115);
x_8 = x_111;
goto block_20;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_dec(x_111);
x_117 = lean_box(x_103);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_95);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
x_8 = x_119;
goto block_20;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = lean_ctor_get(x_106, 0);
lean_inc(x_120);
lean_dec(x_106);
x_121 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set_uint8(x_121, sizeof(void*)*1, x_28);
lean_ctor_set(x_105, 3, x_121);
x_122 = lean_st_ref_set(x_6, x_105, x_107);
lean_dec(x_6);
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
x_125 = lean_box(x_103);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_95);
lean_ctor_set(x_126, 1, x_125);
if (lean_is_scalar(x_124)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_124;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_123);
x_8 = x_127;
goto block_20;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_128 = lean_ctor_get(x_105, 0);
x_129 = lean_ctor_get(x_105, 1);
x_130 = lean_ctor_get(x_105, 2);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_105);
x_131 = lean_ctor_get(x_106, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_132 = x_106;
} else {
 lean_dec_ref(x_106);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 1, 1);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_28);
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_128);
lean_ctor_set(x_134, 1, x_129);
lean_ctor_set(x_134, 2, x_130);
lean_ctor_set(x_134, 3, x_133);
x_135 = lean_st_ref_set(x_6, x_134, x_107);
lean_dec(x_6);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
x_138 = lean_box(x_103);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_95);
lean_ctor_set(x_139, 1, x_138);
if (lean_is_scalar(x_137)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_137;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_136);
x_8 = x_140;
goto block_20;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_89);
x_141 = lean_ctor_get(x_94, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_94, 1);
lean_inc(x_142);
lean_dec(x_94);
x_39 = x_141;
x_40 = x_142;
goto block_72;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_89);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_143 = lean_ctor_get(x_92, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_92, 1);
lean_inc(x_144);
lean_dec(x_92);
x_39 = x_143;
x_40 = x_144;
goto block_72;
}
block_72:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_st_ref_get(x_6, x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_st_ref_take(x_6, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_44, 3);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_28);
x_50 = lean_st_ref_set(x_6, x_44, x_46);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 0, x_39);
x_8 = x_50;
goto block_20;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_39);
lean_ctor_set(x_54, 1, x_53);
x_8 = x_54;
goto block_20;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
lean_dec(x_45);
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_28);
lean_ctor_set(x_44, 3, x_56);
x_57 = lean_st_ref_set(x_6, x_44, x_46);
lean_dec(x_6);
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
lean_ctor_set(x_60, 0, x_39);
lean_ctor_set(x_60, 1, x_58);
x_8 = x_60;
goto block_20;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_61 = lean_ctor_get(x_44, 0);
x_62 = lean_ctor_get(x_44, 1);
x_63 = lean_ctor_get(x_44, 2);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_44);
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_65 = x_45;
} else {
 lean_dec_ref(x_45);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 1, 1);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_28);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_62);
lean_ctor_set(x_67, 2, x_63);
lean_ctor_set(x_67, 3, x_66);
x_68 = lean_st_ref_set(x_6, x_67, x_46);
lean_dec(x_6);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
 lean_ctor_set_tag(x_71, 1);
}
lean_ctor_set(x_71, 0, x_39);
lean_ctor_set(x_71, 1, x_69);
x_8 = x_71;
goto block_20;
}
}
}
else
{
lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_145 = lean_ctor_get(x_31, 0);
lean_inc(x_145);
lean_dec(x_31);
x_146 = 0;
x_147 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_146);
lean_ctor_set(x_30, 3, x_147);
x_148 = lean_st_ref_set(x_6, x_30, x_32);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_171 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_172 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_171, x_21, x_3, x_4, x_5, x_6, x_149);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
lean_inc(x_1);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_1);
x_175 = 0;
x_176 = lean_box(0);
lean_inc(x_3);
x_177 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_174, x_175, x_176, x_3, x_4, x_5, x_6, x_173);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_st_ref_get(x_4, x_179);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
lean_dec(x_181);
lean_inc(x_183);
x_184 = l_Lean_Meta_SynthInstance_mkTableKey(x_183, x_1);
x_185 = l_Lean_Meta_SynthInstance_main___closed__2;
x_186 = lean_st_mk_ref(x_185, x_182);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_box(1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_187);
x_190 = l_Lean_Meta_SynthInstance_newSubgoal(x_183, x_184, x_178, x_189, x_187, x_3, x_4, x_5, x_6, x_188);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
lean_inc(x_6);
lean_inc(x_187);
x_192 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_187, x_3, x_4, x_5, x_6, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_get(x_187, x_194);
lean_dec(x_187);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_197 = lean_st_ref_get(x_6, x_196);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get(x_198, 3);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_ctor_get_uint8(x_200, sizeof(void*)*1);
lean_dec(x_200);
x_202 = lean_st_ref_take(x_6, x_199);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_203, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_ctor_get(x_203, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_203, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_203, 2);
lean_inc(x_208);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 lean_ctor_release(x_203, 2);
 lean_ctor_release(x_203, 3);
 x_209 = x_203;
} else {
 lean_dec_ref(x_203);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get(x_204, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_211 = x_204;
} else {
 lean_dec_ref(x_204);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(0, 1, 1);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*1, x_28);
if (lean_is_scalar(x_209)) {
 x_213 = lean_alloc_ctor(0, 4, 0);
} else {
 x_213 = x_209;
}
lean_ctor_set(x_213, 0, x_206);
lean_ctor_set(x_213, 1, x_207);
lean_ctor_set(x_213, 2, x_208);
lean_ctor_set(x_213, 3, x_212);
x_214 = lean_st_ref_set(x_6, x_213, x_205);
lean_dec(x_6);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_216 = x_214;
} else {
 lean_dec_ref(x_214);
 x_216 = lean_box(0);
}
x_217 = lean_box(x_201);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_193);
lean_ctor_set(x_218, 1, x_217);
if (lean_is_scalar(x_216)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_216;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_215);
x_8 = x_219;
goto block_20;
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_187);
x_220 = lean_ctor_get(x_192, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_192, 1);
lean_inc(x_221);
lean_dec(x_192);
x_150 = x_220;
x_151 = x_221;
goto block_170;
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_187);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_222 = lean_ctor_get(x_190, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_190, 1);
lean_inc(x_223);
lean_dec(x_190);
x_150 = x_222;
x_151 = x_223;
goto block_170;
}
block_170:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_152 = lean_st_ref_get(x_6, x_151);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_st_ref_take(x_6, x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_155, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 2);
lean_inc(x_160);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 lean_ctor_release(x_155, 3);
 x_161 = x_155;
} else {
 lean_dec_ref(x_155);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_156, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_163 = x_156;
} else {
 lean_dec_ref(x_156);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 1, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_28);
if (lean_is_scalar(x_161)) {
 x_165 = lean_alloc_ctor(0, 4, 0);
} else {
 x_165 = x_161;
}
lean_ctor_set(x_165, 0, x_158);
lean_ctor_set(x_165, 1, x_159);
lean_ctor_set(x_165, 2, x_160);
lean_ctor_set(x_165, 3, x_164);
x_166 = lean_st_ref_set(x_6, x_165, x_157);
lean_dec(x_6);
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
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
 lean_ctor_set_tag(x_169, 1);
}
lean_ctor_set(x_169, 0, x_150);
lean_ctor_set(x_169, 1, x_167);
x_8 = x_169;
goto block_20;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_224 = lean_ctor_get(x_30, 0);
x_225 = lean_ctor_get(x_30, 1);
x_226 = lean_ctor_get(x_30, 2);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_30);
x_227 = lean_ctor_get(x_31, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_228 = x_31;
} else {
 lean_dec_ref(x_31);
 x_228 = lean_box(0);
}
x_229 = 0;
if (lean_is_scalar(x_228)) {
 x_230 = lean_alloc_ctor(0, 1, 1);
} else {
 x_230 = x_228;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set_uint8(x_230, sizeof(void*)*1, x_229);
x_231 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_231, 0, x_224);
lean_ctor_set(x_231, 1, x_225);
lean_ctor_set(x_231, 2, x_226);
lean_ctor_set(x_231, 3, x_230);
x_232 = lean_st_ref_set(x_6, x_231, x_32);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_255 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_256 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_255, x_21, x_3, x_4, x_5, x_6, x_233);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec(x_256);
lean_inc(x_1);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_1);
x_259 = 0;
x_260 = lean_box(0);
lean_inc(x_3);
x_261 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_258, x_259, x_260, x_3, x_4, x_5, x_6, x_257);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_st_ref_get(x_4, x_263);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_ctor_get(x_265, 0);
lean_inc(x_267);
lean_dec(x_265);
lean_inc(x_267);
x_268 = l_Lean_Meta_SynthInstance_mkTableKey(x_267, x_1);
x_269 = l_Lean_Meta_SynthInstance_main___closed__2;
x_270 = lean_st_mk_ref(x_269, x_266);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = lean_box(1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_271);
x_274 = l_Lean_Meta_SynthInstance_newSubgoal(x_267, x_268, x_262, x_273, x_271, x_3, x_4, x_5, x_6, x_272);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec(x_274);
lean_inc(x_6);
lean_inc(x_271);
x_276 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_271, x_3, x_4, x_5, x_6, x_275);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_st_ref_get(x_271, x_278);
lean_dec(x_271);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_281 = lean_st_ref_get(x_6, x_280);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_ctor_get(x_282, 3);
lean_inc(x_284);
lean_dec(x_282);
x_285 = lean_ctor_get_uint8(x_284, sizeof(void*)*1);
lean_dec(x_284);
x_286 = lean_st_ref_take(x_6, x_283);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_287, 3);
lean_inc(x_288);
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
lean_dec(x_286);
x_290 = lean_ctor_get(x_287, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_287, 1);
lean_inc(x_291);
x_292 = lean_ctor_get(x_287, 2);
lean_inc(x_292);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 x_293 = x_287;
} else {
 lean_dec_ref(x_287);
 x_293 = lean_box(0);
}
x_294 = lean_ctor_get(x_288, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 x_295 = x_288;
} else {
 lean_dec_ref(x_288);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(0, 1, 1);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set_uint8(x_296, sizeof(void*)*1, x_28);
if (lean_is_scalar(x_293)) {
 x_297 = lean_alloc_ctor(0, 4, 0);
} else {
 x_297 = x_293;
}
lean_ctor_set(x_297, 0, x_290);
lean_ctor_set(x_297, 1, x_291);
lean_ctor_set(x_297, 2, x_292);
lean_ctor_set(x_297, 3, x_296);
x_298 = lean_st_ref_set(x_6, x_297, x_289);
lean_dec(x_6);
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_300 = x_298;
} else {
 lean_dec_ref(x_298);
 x_300 = lean_box(0);
}
x_301 = lean_box(x_285);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_277);
lean_ctor_set(x_302, 1, x_301);
if (lean_is_scalar(x_300)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_300;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_299);
x_8 = x_303;
goto block_20;
}
else
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_271);
x_304 = lean_ctor_get(x_276, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_276, 1);
lean_inc(x_305);
lean_dec(x_276);
x_234 = x_304;
x_235 = x_305;
goto block_254;
}
}
else
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_271);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_306 = lean_ctor_get(x_274, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_274, 1);
lean_inc(x_307);
lean_dec(x_274);
x_234 = x_306;
x_235 = x_307;
goto block_254;
}
block_254:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_236 = lean_st_ref_get(x_6, x_235);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_st_ref_take(x_6, x_237);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_239, 3);
lean_inc(x_240);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_dec(x_238);
x_242 = lean_ctor_get(x_239, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_239, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_239, 2);
lean_inc(x_244);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 lean_ctor_release(x_239, 2);
 lean_ctor_release(x_239, 3);
 x_245 = x_239;
} else {
 lean_dec_ref(x_239);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_240, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 x_247 = x_240;
} else {
 lean_dec_ref(x_240);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 1, 1);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set_uint8(x_248, sizeof(void*)*1, x_28);
if (lean_is_scalar(x_245)) {
 x_249 = lean_alloc_ctor(0, 4, 0);
} else {
 x_249 = x_245;
}
lean_ctor_set(x_249, 0, x_242);
lean_ctor_set(x_249, 1, x_243);
lean_ctor_set(x_249, 2, x_244);
lean_ctor_set(x_249, 3, x_248);
x_250 = lean_st_ref_set(x_6, x_249, x_241);
lean_dec(x_6);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
 lean_ctor_set_tag(x_253, 1);
}
lean_ctor_set(x_253, 0, x_234);
lean_ctor_set(x_253, 1, x_251);
x_8 = x_253;
goto block_20;
}
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_308 = lean_ctor_get(x_5, 3);
lean_inc(x_308);
x_309 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(x_6, x_23);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_321 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_322 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_321, x_21, x_3, x_4, x_5, x_6, x_311);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec(x_322);
lean_inc(x_1);
x_324 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_324, 0, x_1);
x_325 = 0;
x_326 = lean_box(0);
lean_inc(x_3);
x_327 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_324, x_325, x_326, x_3, x_4, x_5, x_6, x_323);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = lean_st_ref_get(x_4, x_329);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_ctor_get(x_331, 0);
lean_inc(x_333);
lean_dec(x_331);
lean_inc(x_333);
x_334 = l_Lean_Meta_SynthInstance_mkTableKey(x_333, x_1);
x_335 = l_Lean_Meta_SynthInstance_main___closed__2;
x_336 = lean_st_mk_ref(x_335, x_332);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_box(1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_337);
x_340 = l_Lean_Meta_SynthInstance_newSubgoal(x_333, x_334, x_328, x_339, x_337, x_3, x_4, x_5, x_6, x_338);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
lean_dec(x_340);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_337);
x_342 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_337, x_3, x_4, x_5, x_6, x_341);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_st_ref_get(x_337, x_344);
lean_dec(x_337);
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
lean_dec(x_345);
x_347 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_310, x_321, x_308, x_3, x_4, x_5, x_6, x_346);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_dec(x_349);
lean_ctor_set(x_347, 0, x_343);
return x_347;
}
else
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
lean_dec(x_347);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_343);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
else
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_337);
x_352 = lean_ctor_get(x_342, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_342, 1);
lean_inc(x_353);
lean_dec(x_342);
x_312 = x_352;
x_313 = x_353;
goto block_320;
}
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_337);
lean_dec(x_2);
x_354 = lean_ctor_get(x_340, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_340, 1);
lean_inc(x_355);
lean_dec(x_340);
x_312 = x_354;
x_313 = x_355;
goto block_320;
}
block_320:
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_314 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_315 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_310, x_314, x_308, x_3, x_4, x_5, x_6, x_313);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
lean_object* x_317; 
x_317 = lean_ctor_get(x_315, 0);
lean_dec(x_317);
lean_ctor_set_tag(x_315, 1);
lean_ctor_set(x_315, 0, x_312);
return x_315;
}
else
{
lean_object* x_318; lean_object* x_319; 
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
lean_dec(x_315);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_312);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_main___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_main___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(x_1, x_9, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
static lean_object* _init_l___private_Lean_Meta_SynthInstance_3__preprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_3__preprocess___lambda__1), 7, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_SynthInstance_3__preprocess___closed__1;
x_8 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_4__preprocessLevels___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_10, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Level_hasMVar(x_13);
if (x_15 == 0)
{
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_13);
x_1 = x_2;
x_2 = x_11;
x_7 = x_14;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(x_4, x_5, x_6, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_18);
x_1 = x_2;
x_2 = x_11;
x_7 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_23 = l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_21, x_3, x_4, x_5, x_6, x_7);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Level_hasMVar(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_1);
x_1 = x_27;
x_2 = x_22;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
x_29 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(x_4, x_5, x_6, x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_1);
x_1 = x_32;
x_2 = x_22;
x_7 = x_31;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessLevels(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_box(0);
x_8 = l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_4__preprocessLevels___spec__1(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_List_reverse___rarg(x_10);
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
x_14 = l_List_reverse___rarg(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_4__preprocessLevels___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_4__preprocessLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessLevels___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_SynthInstance_4__preprocessLevels(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type class resolution failed, insufficient number of arguments");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_1, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_inc(x_17);
x_19 = lean_array_fset(x_3, x_2, x_17);
x_20 = lean_expr_instantiate1(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_1 = x_20;
x_2 = x_22;
x_3 = x_19;
x_8 = x_14;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_15);
x_25 = 0;
x_26 = lean_box(0);
lean_inc(x_4);
x_27 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_24, x_25, x_26, x_4, x_5, x_6, x_7, x_14);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_28);
x_30 = lean_array_fset(x_3, x_2, x_28);
x_31 = lean_expr_instantiate1(x_16, x_28);
lean_dec(x_28);
lean_dec(x_16);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_2, x_32);
lean_dec(x_2);
x_1 = x_31;
x_2 = x_33;
x_3 = x_30;
x_8 = x_29;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_dec(x_12);
x_36 = l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__3;
x_37 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_36, x_4, x_5, x_6, x_7, x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_6__preprocessOutParam___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_getAppFn___main(x_3);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_10);
x_17 = lean_has_out_params(x_16, x_10);
if (x_17 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_12);
lean_dec(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_18);
x_20 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_19);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_19, x_22);
lean_dec(x_19);
x_24 = l___private_Lean_Expr_3__getAppArgsAux___main(x_3, x_21, x_23);
x_25 = l___private_Lean_Meta_SynthInstance_4__preprocessLevels(x_11, x_4, x_5, x_6, x_7, x_15);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_mkConst(x_10, x_26);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_28);
x_29 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_28, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_32 = l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main(x_30, x_18, x_24, x_4, x_5, x_6, x_7, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_33, x_33, x_18, x_28);
lean_dec(x_33);
x_36 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(x_2, x_35, x_4, x_5, x_6, x_7, x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
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
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_29);
if (x_41 == 0)
{
return x_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 0);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_29);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_12);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_10);
x_48 = lean_has_out_params(x_47, x_10);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_1);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_50);
x_52 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_51);
x_53 = lean_mk_array(x_51, x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_51, x_54);
lean_dec(x_51);
x_56 = l___private_Lean_Expr_3__getAppArgsAux___main(x_3, x_53, x_55);
x_57 = l___private_Lean_Meta_SynthInstance_4__preprocessLevels(x_11, x_4, x_5, x_6, x_7, x_46);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_mkConst(x_10, x_58);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_60);
x_61 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_60, x_4, x_5, x_6, x_7, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_64 = l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main(x_62, x_50, x_56, x_4, x_5, x_6, x_7, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_65, x_65, x_50, x_60);
lean_dec(x_65);
x_68 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(x_2, x_67, x_4, x_5, x_6, x_7, x_66);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
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
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_73 = lean_ctor_get(x_61, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_61, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_75 = x_61;
} else {
 lean_dec_ref(x_61);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_8);
return x_77;
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_6__preprocessOutParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_6__preprocessOutParam___lambda__1), 8, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_maxStepsDefault() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1000u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_maxStepsOption___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_maxStepsOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maxSteps");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_maxStepsOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_maxStepsOption___closed__1;
x_2 = l_Lean_Meta_maxStepsOption___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_maxStepsOption___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_maxStepsDefault;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_maxStepsOption___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum steps for the type class instance synthesis procedure");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_maxStepsOption___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_maxStepsOption___closed__4;
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_Meta_maxStepsOption___closed__5;
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
x_2 = l_Lean_Meta_maxStepsOption___closed__3;
x_3 = l_Lean_Meta_maxStepsOption___closed__6;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_7__getMaxSteps(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_maxStepsOption___closed__3;
x_3 = l_Lean_Meta_maxStepsDefault;
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_7__getMaxSteps___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_SynthInstance_7__getMaxSteps(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_38 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__2(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__2(x_40, x_41, x_42, x_4, x_5);
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
x_75 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__2(x_71, x_73, x_74, x_4, x_5);
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
x_83 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__3(x_1, x_82, x_4, x_5);
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
x_92 = l_Array_iterateMAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__4(x_3, x_89, x_90, x_89, x_82, x_91);
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
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__2(x_5, x_7, x_8, x_2, x_3);
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
x_16 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__2(x_12, x_14, x_15, x_2, x_3);
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
lean_object* l_Std_PersistentHashMap_findAtAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__6(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_23 = l_Std_PersistentHashMap_findAtAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__7(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__6(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_MetavarContext_hasAssignableMVar___main(x_10, x_1);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_MetavarContext_hasAssignableMVar___main(x_16, x_1);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ==> ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__3;
x_6 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("FOUND result ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__3;
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_3);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___boxed), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_11 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_10, x_9, x_4, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Meta_SynthInstance_main(x_3, x_2, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___boxed), 2, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_10, x_22, x_4, x_5, x_6, x_7, x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_21, x_4, x_5, x_6, x_7, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__8(x_26, x_4, x_5, x_6, x_7, x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
lean_ctor_set(x_14, 0, x_26);
lean_ctor_set(x_28, 0, x_14);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
lean_ctor_set(x_14, 0, x_26);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_26);
lean_free_object(x_14);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_28, 0, x_37);
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_41 = lean_ctor_get(x_14, 0);
lean_inc(x_41);
lean_dec(x_14);
lean_inc(x_41);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___boxed), 2, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_10, x_42, x_4, x_5, x_6, x_7, x_19);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_41, x_4, x_5, x_6, x_7, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__8(x_46, x_4, x_5, x_6, x_7, x_47);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_46);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_46);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_13);
if (x_59 == 0)
{
return x_13;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_13, 0);
x_61 = lean_ctor_get(x_13, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_13);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__3;
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l___private_Lean_Meta_SynthInstance_7__getMaxSteps(x_7);
lean_dec(x_7);
x_9 = l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__3(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = 1;
x_19 = 0;
x_20 = 2;
lean_ctor_set_uint8(x_10, 0, x_18);
lean_ctor_set_uint8(x_10, 1, x_18);
lean_ctor_set_uint8(x_10, 3, x_19);
lean_ctor_set_uint8(x_10, 4, x_18);
lean_ctor_set_uint8(x_10, 5, x_20);
lean_inc(x_15);
lean_inc(x_14);
x_21 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_12);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Meta_SynthInstance_3__preprocess___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_22, x_24, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_74; uint8_t x_75; 
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
x_74 = lean_st_ref_get(x_3, x_27);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_78, 2);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__5(x_79, x_26);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_free_object(x_74);
lean_inc(x_26);
x_81 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_6__preprocessOutParam), 6, 1);
lean_closure_set(x_81, 0, x_26);
lean_inc(x_26);
x_82 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__3), 8, 2);
lean_closure_set(x_82, 0, x_26);
lean_closure_set(x_82, 1, x_8);
x_83 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_83, 0, x_81);
lean_closure_set(x_83, 1, x_82);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_84 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_83, x_2, x_3, x_4, x_5, x_77);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_29 = x_85;
x_30 = x_86;
goto block_73;
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = !lean_is_exclusive(x_85);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
x_90 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___boxed), 2, 1);
lean_closure_set(x_90, 0, x_89);
x_91 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_92 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_91, x_90, x_2, x_3, x_4, x_5, x_87);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_89);
x_94 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_89, x_2, x_3, x_4, x_5, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_11);
lean_ctor_set(x_97, 1, x_14);
lean_ctor_set(x_97, 2, x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_98 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_26, x_95, x_97, x_3, x_4, x_5, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_free_object(x_85);
lean_dec(x_89);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_box(0);
x_29 = x_102;
x_30 = x_101;
goto block_73;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_dec(x_98);
x_104 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_89, x_2, x_3, x_4, x_5, x_103);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_ctor_set(x_85, 0, x_105);
x_29 = x_85;
x_30 = x_106;
goto block_73;
}
}
else
{
uint8_t x_107; 
lean_free_object(x_85);
lean_dec(x_89);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_98);
if (x_107 == 0)
{
return x_98;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_98, 0);
x_109 = lean_ctor_get(x_98, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_98);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_free_object(x_85);
lean_dec(x_89);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = !lean_is_exclusive(x_94);
if (x_111 == 0)
{
return x_94;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_94, 0);
x_113 = lean_ctor_get(x_94, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_94);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_85, 0);
lean_inc(x_115);
lean_dec(x_85);
lean_inc(x_115);
x_116 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___boxed), 2, 1);
lean_closure_set(x_116, 0, x_115);
x_117 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_118 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_117, x_116, x_2, x_3, x_4, x_5, x_87);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_115);
x_120 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_115, x_2, x_3, x_4, x_5, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_123, 0, x_11);
lean_ctor_set(x_123, 1, x_14);
lean_ctor_set(x_123, 2, x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_124 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_26, x_121, x_123, x_3, x_4, x_5, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_115);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_box(0);
x_29 = x_128;
x_30 = x_127;
goto block_73;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_115, x_2, x_3, x_4, x_5, x_129);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_131);
x_29 = x_133;
x_30 = x_132;
goto block_73;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_115);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_134 = lean_ctor_get(x_124, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_124, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_136 = x_124;
} else {
 lean_dec_ref(x_124);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_115);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_ctor_get(x_120, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_120, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_140 = x_120;
} else {
 lean_dec_ref(x_120);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_142 = !lean_is_exclusive(x_84);
if (x_142 == 0)
{
return x_84;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_84, 0);
x_144 = lean_ctor_get(x_84, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_84);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_object* x_146; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_146 = lean_ctor_get(x_80, 0);
lean_inc(x_146);
lean_dec(x_80);
lean_ctor_set(x_74, 0, x_146);
return x_74;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_74, 0);
x_148 = lean_ctor_get(x_74, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_74);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_149, 2);
lean_inc(x_150);
lean_dec(x_149);
x_151 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__5(x_150, x_26);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_inc(x_26);
x_152 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_6__preprocessOutParam), 6, 1);
lean_closure_set(x_152, 0, x_26);
lean_inc(x_26);
x_153 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__3), 8, 2);
lean_closure_set(x_153, 0, x_26);
lean_closure_set(x_153, 1, x_8);
x_154 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_154, 0, x_152);
lean_closure_set(x_154, 1, x_153);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_155 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_154, x_2, x_3, x_4, x_5, x_148);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_29 = x_156;
x_30 = x_157;
goto block_73;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec(x_155);
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_160 = x_156;
} else {
 lean_dec_ref(x_156);
 x_160 = lean_box(0);
}
lean_inc(x_159);
x_161 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___boxed), 2, 1);
lean_closure_set(x_161, 0, x_159);
x_162 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_163 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_162, x_161, x_2, x_3, x_4, x_5, x_158);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_159);
x_165 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_159, x_2, x_3, x_4, x_5, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_11);
lean_ctor_set(x_168, 1, x_14);
lean_ctor_set(x_168, 2, x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_169 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_26, x_166, x_168, x_3, x_4, x_5, x_167);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_box(0);
x_29 = x_173;
x_30 = x_172;
goto block_73;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_169, 1);
lean_inc(x_174);
lean_dec(x_169);
x_175 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_159, x_2, x_3, x_4, x_5, x_174);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
if (lean_is_scalar(x_160)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_160;
}
lean_ctor_set(x_178, 0, x_176);
x_29 = x_178;
x_30 = x_177;
goto block_73;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_179 = lean_ctor_get(x_169, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_169, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_181 = x_169;
} else {
 lean_dec_ref(x_169);
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
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_183 = lean_ctor_get(x_165, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_165, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_185 = x_165;
} else {
 lean_dec_ref(x_165);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_187 = lean_ctor_get(x_155, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_155, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_189 = x_155;
} else {
 lean_dec_ref(x_155);
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
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_191 = lean_ctor_get(x_151, 0);
lean_inc(x_191);
lean_dec(x_151);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_148);
return x_192;
}
}
block_73:
{
uint8_t x_31; 
x_31 = l_Lean_Expr_hasMVar(x_26);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_28);
x_32 = lean_st_ref_take(x_3, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 1);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_34, 2);
lean_inc(x_29);
x_40 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__1(x_39, x_26, x_29);
lean_ctor_set(x_34, 2, x_40);
x_41 = lean_st_ref_set(x_3, x_33, x_35);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_29);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
x_48 = lean_ctor_get(x_34, 2);
x_49 = lean_ctor_get(x_34, 3);
x_50 = lean_ctor_get(x_34, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
lean_inc(x_29);
x_51 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__1(x_48, x_26, x_29);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set(x_52, 4, x_50);
lean_ctor_set(x_33, 1, x_52);
x_53 = lean_st_ref_set(x_3, x_33, x_35);
lean_dec(x_3);
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
lean_ctor_set(x_56, 0, x_29);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_57 = lean_ctor_get(x_33, 0);
x_58 = lean_ctor_get(x_33, 2);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_33);
x_59 = lean_ctor_get(x_34, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_34, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_34, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_34, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_34, 4);
lean_inc(x_63);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 lean_ctor_release(x_34, 4);
 x_64 = x_34;
} else {
 lean_dec_ref(x_34);
 x_64 = lean_box(0);
}
lean_inc(x_29);
x_65 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__1(x_61, x_26, x_29);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 5, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_62);
lean_ctor_set(x_66, 4, x_63);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_58);
x_68 = lean_st_ref_set(x_3, x_67, x_35);
lean_dec(x_3);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_29);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; 
lean_dec(x_26);
lean_dec(x_3);
if (lean_is_scalar(x_28)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_28;
}
lean_ctor_set(x_72, 0, x_29);
lean_ctor_set(x_72, 1, x_30);
return x_72;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_193 = !lean_is_exclusive(x_25);
if (x_193 == 0)
{
return x_25;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_25, 0);
x_195 = lean_ctor_get(x_25, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_25);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_197 = lean_ctor_get_uint8(x_10, 2);
x_198 = lean_ctor_get_uint8(x_10, 6);
x_199 = lean_ctor_get_uint8(x_10, 7);
lean_dec(x_10);
x_200 = 1;
x_201 = 0;
x_202 = 2;
x_203 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_203, 0, x_200);
lean_ctor_set_uint8(x_203, 1, x_200);
lean_ctor_set_uint8(x_203, 2, x_197);
lean_ctor_set_uint8(x_203, 3, x_201);
lean_ctor_set_uint8(x_203, 4, x_200);
lean_ctor_set_uint8(x_203, 5, x_202);
lean_ctor_set_uint8(x_203, 6, x_198);
lean_ctor_set_uint8(x_203, 7, x_199);
lean_inc(x_15);
lean_inc(x_14);
lean_ctor_set(x_2, 0, x_203);
x_204 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_12);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l___private_Lean_Meta_SynthInstance_3__preprocess___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_208 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_205, x_207, x_2, x_3, x_4, x_5, x_206);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_211 = x_208;
} else {
 lean_dec_ref(x_208);
 x_211 = lean_box(0);
}
x_237 = lean_st_ref_get(x_3, x_210);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_240 = x_237;
} else {
 lean_dec_ref(x_237);
 x_240 = lean_box(0);
}
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_dec(x_238);
x_242 = lean_ctor_get(x_241, 2);
lean_inc(x_242);
lean_dec(x_241);
x_243 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__5(x_242, x_209);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_240);
lean_inc(x_209);
x_244 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_6__preprocessOutParam), 6, 1);
lean_closure_set(x_244, 0, x_209);
lean_inc(x_209);
x_245 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__3), 8, 2);
lean_closure_set(x_245, 0, x_209);
lean_closure_set(x_245, 1, x_8);
x_246 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_246, 0, x_244);
lean_closure_set(x_246, 1, x_245);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_247 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_246, x_2, x_3, x_4, x_5, x_239);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; 
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_212 = x_248;
x_213 = x_249;
goto block_236;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_dec(x_247);
x_251 = lean_ctor_get(x_248, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_252 = x_248;
} else {
 lean_dec_ref(x_248);
 x_252 = lean_box(0);
}
lean_inc(x_251);
x_253 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___boxed), 2, 1);
lean_closure_set(x_253, 0, x_251);
x_254 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_255 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_254, x_253, x_2, x_3, x_4, x_5, x_250);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec(x_255);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_251);
x_257 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_251, x_2, x_3, x_4, x_5, x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_260, 0, x_11);
lean_ctor_set(x_260, 1, x_14);
lean_ctor_set(x_260, 2, x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_209);
x_261 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_209, x_258, x_260, x_3, x_4, x_5, x_259);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; uint8_t x_263; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_unbox(x_262);
lean_dec(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
lean_dec(x_261);
x_265 = lean_box(0);
x_212 = x_265;
x_213 = x_264;
goto block_236;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_ctor_get(x_261, 1);
lean_inc(x_266);
lean_dec(x_261);
x_267 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_251, x_2, x_3, x_4, x_5, x_266);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
if (lean_is_scalar(x_252)) {
 x_270 = lean_alloc_ctor(1, 1, 0);
} else {
 x_270 = x_252;
}
lean_ctor_set(x_270, 0, x_268);
x_212 = x_270;
x_213 = x_269;
goto block_236;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_271 = lean_ctor_get(x_261, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_261, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_273 = x_261;
} else {
 lean_dec_ref(x_261);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_275 = lean_ctor_get(x_257, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_257, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_277 = x_257;
} else {
 lean_dec_ref(x_257);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_279 = lean_ctor_get(x_247, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_247, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_281 = x_247;
} else {
 lean_dec_ref(x_247);
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
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_283 = lean_ctor_get(x_243, 0);
lean_inc(x_283);
lean_dec(x_243);
if (lean_is_scalar(x_240)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_240;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_239);
return x_284;
}
block_236:
{
uint8_t x_214; 
x_214 = l_Lean_Expr_hasMVar(x_209);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_211);
x_215 = lean_st_ref_take(x_3, x_213);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_dec(x_215);
x_219 = lean_ctor_get(x_216, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_216, 2);
lean_inc(x_220);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 x_221 = x_216;
} else {
 lean_dec_ref(x_216);
 x_221 = lean_box(0);
}
x_222 = lean_ctor_get(x_217, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_217, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_217, 2);
lean_inc(x_224);
x_225 = lean_ctor_get(x_217, 3);
lean_inc(x_225);
x_226 = lean_ctor_get(x_217, 4);
lean_inc(x_226);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 lean_ctor_release(x_217, 4);
 x_227 = x_217;
} else {
 lean_dec_ref(x_217);
 x_227 = lean_box(0);
}
lean_inc(x_212);
x_228 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__1(x_224, x_209, x_212);
if (lean_is_scalar(x_227)) {
 x_229 = lean_alloc_ctor(0, 5, 0);
} else {
 x_229 = x_227;
}
lean_ctor_set(x_229, 0, x_222);
lean_ctor_set(x_229, 1, x_223);
lean_ctor_set(x_229, 2, x_228);
lean_ctor_set(x_229, 3, x_225);
lean_ctor_set(x_229, 4, x_226);
if (lean_is_scalar(x_221)) {
 x_230 = lean_alloc_ctor(0, 3, 0);
} else {
 x_230 = x_221;
}
lean_ctor_set(x_230, 0, x_219);
lean_ctor_set(x_230, 1, x_229);
lean_ctor_set(x_230, 2, x_220);
x_231 = lean_st_ref_set(x_3, x_230, x_218);
lean_dec(x_3);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_212);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
else
{
lean_object* x_235; 
lean_dec(x_209);
lean_dec(x_3);
if (lean_is_scalar(x_211)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_211;
}
lean_ctor_set(x_235, 0, x_212);
lean_ctor_set(x_235, 1, x_213);
return x_235;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_285 = lean_ctor_get(x_208, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_208, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_287 = x_208;
} else {
 lean_dec_ref(x_208);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
else
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; uint8_t x_293; lean_object* x_294; uint8_t x_295; uint8_t x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_289 = lean_ctor_get(x_2, 1);
x_290 = lean_ctor_get(x_2, 2);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_2);
x_291 = lean_ctor_get_uint8(x_10, 2);
x_292 = lean_ctor_get_uint8(x_10, 6);
x_293 = lean_ctor_get_uint8(x_10, 7);
if (lean_is_exclusive(x_10)) {
 x_294 = x_10;
} else {
 lean_dec_ref(x_10);
 x_294 = lean_box(0);
}
x_295 = 1;
x_296 = 0;
x_297 = 2;
if (lean_is_scalar(x_294)) {
 x_298 = lean_alloc_ctor(0, 0, 8);
} else {
 x_298 = x_294;
}
lean_ctor_set_uint8(x_298, 0, x_295);
lean_ctor_set_uint8(x_298, 1, x_295);
lean_ctor_set_uint8(x_298, 2, x_291);
lean_ctor_set_uint8(x_298, 3, x_296);
lean_ctor_set_uint8(x_298, 4, x_295);
lean_ctor_set_uint8(x_298, 5, x_297);
lean_ctor_set_uint8(x_298, 6, x_292);
lean_ctor_set_uint8(x_298, 7, x_293);
lean_inc(x_290);
lean_inc(x_289);
x_299 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_289);
lean_ctor_set(x_299, 2, x_290);
x_300 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_1, x_299, x_3, x_4, x_5, x_12);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = l___private_Lean_Meta_SynthInstance_3__preprocess___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_299);
x_304 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_301, x_303, x_299, x_3, x_4, x_5, x_302);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_307 = x_304;
} else {
 lean_dec_ref(x_304);
 x_307 = lean_box(0);
}
x_333 = lean_st_ref_get(x_3, x_306);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_336 = x_333;
} else {
 lean_dec_ref(x_333);
 x_336 = lean_box(0);
}
x_337 = lean_ctor_get(x_334, 1);
lean_inc(x_337);
lean_dec(x_334);
x_338 = lean_ctor_get(x_337, 2);
lean_inc(x_338);
lean_dec(x_337);
x_339 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__5(x_338, x_305);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_336);
lean_inc(x_305);
x_340 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_6__preprocessOutParam), 6, 1);
lean_closure_set(x_340, 0, x_305);
lean_inc(x_305);
x_341 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__3), 8, 2);
lean_closure_set(x_341, 0, x_305);
lean_closure_set(x_341, 1, x_8);
x_342 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_342, 0, x_340);
lean_closure_set(x_342, 1, x_341);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_299);
x_343 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_342, x_299, x_3, x_4, x_5, x_335);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; 
lean_dec(x_299);
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_308 = x_344;
x_309 = x_345;
goto block_332;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
lean_dec(x_343);
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 x_348 = x_344;
} else {
 lean_dec_ref(x_344);
 x_348 = lean_box(0);
}
lean_inc(x_347);
x_349 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___boxed), 2, 1);
lean_closure_set(x_349, 0, x_347);
x_350 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_351 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_350, x_349, x_299, x_3, x_4, x_5, x_346);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec(x_351);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_299);
lean_inc(x_347);
x_353 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_347, x_299, x_3, x_4, x_5, x_352);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_356, 0, x_11);
lean_ctor_set(x_356, 1, x_289);
lean_ctor_set(x_356, 2, x_290);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_305);
x_357 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_305, x_354, x_356, x_3, x_4, x_5, x_355);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; uint8_t x_359; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_unbox(x_358);
lean_dec(x_358);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; 
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_299);
lean_dec(x_5);
lean_dec(x_4);
x_360 = lean_ctor_get(x_357, 1);
lean_inc(x_360);
lean_dec(x_357);
x_361 = lean_box(0);
x_308 = x_361;
x_309 = x_360;
goto block_332;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_362 = lean_ctor_get(x_357, 1);
lean_inc(x_362);
lean_dec(x_357);
x_363 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_347, x_299, x_3, x_4, x_5, x_362);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_299);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
if (lean_is_scalar(x_348)) {
 x_366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_366 = x_348;
}
lean_ctor_set(x_366, 0, x_364);
x_308 = x_366;
x_309 = x_365;
goto block_332;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_307);
lean_dec(x_305);
lean_dec(x_299);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_367 = lean_ctor_get(x_357, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_357, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_369 = x_357;
} else {
 lean_dec_ref(x_357);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(1, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_307);
lean_dec(x_305);
lean_dec(x_299);
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_371 = lean_ctor_get(x_353, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_353, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_373 = x_353;
} else {
 lean_dec_ref(x_353);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_307);
lean_dec(x_305);
lean_dec(x_299);
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_375 = lean_ctor_get(x_343, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_343, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_377 = x_343;
} else {
 lean_dec_ref(x_343);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_375);
lean_ctor_set(x_378, 1, x_376);
return x_378;
}
}
else
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_307);
lean_dec(x_305);
lean_dec(x_299);
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_379 = lean_ctor_get(x_339, 0);
lean_inc(x_379);
lean_dec(x_339);
if (lean_is_scalar(x_336)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_336;
}
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_335);
return x_380;
}
block_332:
{
uint8_t x_310; 
x_310 = l_Lean_Expr_hasMVar(x_305);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_307);
x_311 = lean_st_ref_take(x_3, x_309);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
lean_dec(x_311);
x_315 = lean_ctor_get(x_312, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_312, 2);
lean_inc(x_316);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 lean_ctor_release(x_312, 2);
 x_317 = x_312;
} else {
 lean_dec_ref(x_312);
 x_317 = lean_box(0);
}
x_318 = lean_ctor_get(x_313, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_313, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_313, 2);
lean_inc(x_320);
x_321 = lean_ctor_get(x_313, 3);
lean_inc(x_321);
x_322 = lean_ctor_get(x_313, 4);
lean_inc(x_322);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 lean_ctor_release(x_313, 2);
 lean_ctor_release(x_313, 3);
 lean_ctor_release(x_313, 4);
 x_323 = x_313;
} else {
 lean_dec_ref(x_313);
 x_323 = lean_box(0);
}
lean_inc(x_308);
x_324 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__1(x_320, x_305, x_308);
if (lean_is_scalar(x_323)) {
 x_325 = lean_alloc_ctor(0, 5, 0);
} else {
 x_325 = x_323;
}
lean_ctor_set(x_325, 0, x_318);
lean_ctor_set(x_325, 1, x_319);
lean_ctor_set(x_325, 2, x_324);
lean_ctor_set(x_325, 3, x_321);
lean_ctor_set(x_325, 4, x_322);
if (lean_is_scalar(x_317)) {
 x_326 = lean_alloc_ctor(0, 3, 0);
} else {
 x_326 = x_317;
}
lean_ctor_set(x_326, 0, x_315);
lean_ctor_set(x_326, 1, x_325);
lean_ctor_set(x_326, 2, x_316);
x_327 = lean_st_ref_set(x_3, x_326, x_314);
lean_dec(x_3);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_329 = x_327;
} else {
 lean_dec_ref(x_327);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_308);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
else
{
lean_object* x_331; 
lean_dec(x_305);
lean_dec(x_3);
if (lean_is_scalar(x_307)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_307;
}
lean_ctor_set(x_331, 0, x_308);
lean_ctor_set(x_331, 1, x_309);
return x_331;
}
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_299);
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_381 = lean_ctor_get(x_304, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_304, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_383 = x_304;
} else {
 lean_dec_ref(x_304);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__6(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_9__trySynthInstanceImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Option_toLOption___rarg(x_9);
lean_dec(x_9);
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
x_13 = l_Option_toLOption___rarg(x_11);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_7, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
x_23 = l_Lean_Meta_isDefEqStuckExceptionId;
x_24 = lean_nat_dec_eq(x_23, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; 
lean_dec(x_15);
x_25 = lean_box(2);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_dec(x_7);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
x_28 = l_Lean_Meta_isDefEqStuckExceptionId;
x_29 = lean_nat_dec_eq(x_28, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_15);
x_31 = lean_box(2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to synthesize");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_10__synthInstanceImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_19; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_1);
x_22 = l_Lean_indentExpr(x_1);
x_23 = l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__3;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_24, x_2, x_3, x_4, x_5, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_7 = x_26;
x_8 = x_27;
goto block_18;
}
else
{
uint8_t x_28; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_7 = x_34;
x_8 = x_35;
goto block_18;
}
block_18:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = l_Lean_Meta_isDefEqStuckExceptionId;
x_12 = lean_nat_dec_eq(x_11, x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_14 = l_Lean_indentExpr(x_1);
x_15 = l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_16, x_2, x_3, x_4, x_5, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
}
}
}
lean_object* l_Lean_Meta_isExprMVarAssigned___at___private_Lean_Meta_SynthInstance_11__synthPendingImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_metavar_ctx_is_expr_assigned(x_10, x_1);
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_metavar_ctx_is_expr_assigned(x_15, x_1);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_11__synthPendingImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
x_10 = lean_box(x_9);
if (lean_obj_tag(x_10) == 1)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_8, 2);
lean_inc(x_14);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_14);
x_15 = l_Lean_Meta_isClass_x3f___at___private_Lean_Meta_Basic_26__withNewFVar___spec__1(x_14, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_47; lean_object* x_48; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = 0;
x_48 = lean_box(x_47);
lean_ctor_set(x_7, 1, x_17);
lean_ctor_set(x_7, 0, x_48);
return x_7;
}
else
{
lean_object* x_49; 
lean_dec(x_16);
lean_free_object(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_49 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(x_14, x_2, x_3, x_4, x_5, x_17);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_19 = x_50;
x_20 = x_51;
goto block_46;
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_49, 0);
lean_dec(x_54);
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_49);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_49, 1);
x_59 = lean_ctor_get(x_49, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
x_61 = l_Lean_Meta_isDefEqStuckExceptionId;
x_62 = lean_nat_dec_eq(x_61, x_60);
lean_dec(x_60);
if (x_62 == 0)
{
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_49;
}
else
{
lean_object* x_63; 
lean_free_object(x_49);
lean_dec(x_52);
x_63 = lean_box(0);
x_19 = x_63;
x_20 = x_58;
goto block_46;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_49, 1);
lean_inc(x_64);
lean_dec(x_49);
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
x_66 = l_Lean_Meta_isDefEqStuckExceptionId;
x_67 = lean_nat_dec_eq(x_66, x_65);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_52);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; 
lean_dec(x_52);
x_69 = lean_box(0);
x_19 = x_69;
x_20 = x_64;
goto block_46;
}
}
}
}
}
block_46:
{
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = 0;
x_22 = lean_box(x_21);
if (lean_is_scalar(x_18)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_18;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
lean_inc(x_1);
x_25 = l_Lean_Meta_isExprMVarAssigned___at___private_Lean_Meta_SynthInstance_11__synthPendingImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_1, x_24, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = 1;
x_33 = lean_box(x_32);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = 1;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
lean_dec(x_39);
x_40 = 0;
x_41 = lean_box(x_40);
lean_ctor_set(x_25, 0, x_41);
return x_25;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_dec(x_25);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_14);
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_15);
if (x_70 == 0)
{
return x_15;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_15, 0);
x_72 = lean_ctor_get(x_15, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_15);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_7, 1);
lean_inc(x_74);
lean_dec(x_7);
x_75 = lean_ctor_get(x_8, 2);
lean_inc(x_75);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_75);
x_76 = l_Lean_Meta_isClass_x3f___at___private_Lean_Meta_Basic_26__withNewFVar___spec__1(x_75, x_2, x_3, x_4, x_5, x_74);
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
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = 0;
x_103 = lean_box(x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_78);
return x_104;
}
else
{
lean_object* x_105; 
lean_dec(x_77);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_105 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(x_75, x_2, x_3, x_4, x_5, x_78);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_80 = x_106;
x_81 = x_107;
goto block_101;
}
else
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_79);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_110 = x_105;
} else {
 lean_dec_ref(x_105);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_113 = x_105;
} else {
 lean_dec_ref(x_105);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_108, 0);
lean_inc(x_114);
x_115 = l_Lean_Meta_isDefEqStuckExceptionId;
x_116 = lean_nat_dec_eq(x_115, x_114);
lean_dec(x_114);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_79);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_113)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_113;
}
lean_ctor_set(x_117, 0, x_108);
lean_ctor_set(x_117, 1, x_112);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_113);
lean_dec(x_108);
x_118 = lean_box(0);
x_80 = x_118;
x_81 = x_112;
goto block_101;
}
}
}
}
block_101:
{
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = 0;
x_83 = lean_box(x_82);
if (lean_is_scalar(x_79)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_79;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_79);
x_85 = lean_ctor_get(x_80, 0);
lean_inc(x_85);
lean_dec(x_80);
lean_inc(x_1);
x_86 = l_Lean_Meta_isExprMVarAssigned___at___private_Lean_Meta_SynthInstance_11__synthPendingImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_81);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_1, x_85, x_2, x_3, x_4, x_5, x_89);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = 1;
x_94 = lean_box(x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_85);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_97 = x_86;
} else {
 lean_dec_ref(x_86);
 x_97 = lean_box(0);
}
x_98 = 0;
x_99 = lean_box(x_98);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_75);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_ctor_get(x_76, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_76, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_121 = x_76;
} else {
 lean_dec_ref(x_76);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_7);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_7, 0);
lean_dec(x_124);
x_125 = 0;
x_126 = lean_box(x_125);
lean_ctor_set(x_7, 0, x_126);
return x_7;
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 1);
lean_inc(x_127);
lean_dec(x_7);
x_128 = 0;
x_129 = lean_box(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_127);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_7);
if (x_131 == 0)
{
return x_7;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_7, 0);
x_133 = lean_ctor_get(x_7, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_7);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
lean_object* l_Lean_Meta_isExprMVarAssigned___at___private_Lean_Meta_SynthInstance_11__synthPendingImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isExprMVarAssigned___at___private_Lean_Meta_SynthInstance_11__synthPendingImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_setSynthPendingRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_11__synthPendingImp), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_setSynthPendingRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_Meta_synthPendingRef;
x_3 = l_Lean_Meta_setSynthPendingRef___closed__1;
x_4 = lean_st_ref_set(x_2, x_3, x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_12__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__5;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_SynthInstance_getInstances___lambda__2___closed__7;
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
x_11 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__2;
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
lean_object* l_Lean_Meta_synthInstance_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance_x3f___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_trySynthInstance___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_9__trySynthInstanceImp), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_trySynthInstance(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_trySynthInstance___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_synthInstance___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_10__synthInstanceImp), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_synthInstance(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance___rarg), 2, 0);
return x_2;
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
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1);
l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2);
l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3);
l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1);
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
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__1);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__2 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__2);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__3 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__3___closed__3);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__1 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__1);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__2 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__2);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__3 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__3);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__4 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__4);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__5 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__5___closed__5);
l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___lambda__1___closed__3);
l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__1 = _init_l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__1);
l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__2 = _init_l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__2);
l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__3 = _init_l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__3);
l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__4 = _init_l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__4();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_2__mkAnswer___closed__4);
l_Lean_Meta_SynthInstance_generate___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_generate___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_generate___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___lambda__1___closed__3);
l_Lean_Meta_SynthInstance_generate___closed__1 = _init_l_Lean_Meta_SynthInstance_generate___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__1);
l_Lean_Meta_SynthInstance_generate___closed__2 = _init_l_Lean_Meta_SynthInstance_generate___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__2);
l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1 = _init_l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1();
lean_mark_persistent(l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1);
l_Lean_Meta_SynthInstance_resume___lambda__3___closed__1 = _init_l_Lean_Meta_SynthInstance_resume___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__3___closed__1);
l_Lean_Meta_SynthInstance_resume___lambda__3___closed__2 = _init_l_Lean_Meta_SynthInstance_resume___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__3___closed__2);
l_Lean_Meta_SynthInstance_resume___lambda__3___closed__3 = _init_l_Lean_Meta_SynthInstance_resume___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___lambda__3___closed__3);
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
l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___lambda__1___closed__3);
l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__1 = _init_l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__1);
l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__2 = _init_l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__2);
l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__3 = _init_l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___lambda__2___closed__3);
l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__1 = _init_l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__1);
l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__2 = _init_l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__2);
l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__3 = _init_l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___lambda__3___closed__3);
l_Lean_Meta_SynthInstance_synth___main___closed__1 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__1);
l_Lean_Meta_SynthInstance_synth___main___closed__2 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__2);
l_Lean_Meta_SynthInstance_main___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_main___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_main___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_main___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___lambda__1___closed__3);
l_Lean_Meta_SynthInstance_main___closed__1 = _init_l_Lean_Meta_SynthInstance_main___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___closed__1);
l_Lean_Meta_SynthInstance_main___closed__2 = _init_l_Lean_Meta_SynthInstance_main___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___closed__2);
l___private_Lean_Meta_SynthInstance_3__preprocess___closed__1 = _init_l___private_Lean_Meta_SynthInstance_3__preprocess___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_3__preprocess___closed__1);
l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__1 = _init_l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__1);
l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__2 = _init_l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__2);
l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__3 = _init_l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_5__preprocessArgs___main___closed__3);
l_Lean_Meta_maxStepsDefault = _init_l_Lean_Meta_maxStepsDefault();
lean_mark_persistent(l_Lean_Meta_maxStepsDefault);
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
l_Lean_Meta_maxStepsOption___closed__6 = _init_l_Lean_Meta_maxStepsOption___closed__6();
lean_mark_persistent(l_Lean_Meta_maxStepsOption___closed__6);
res = l_Lean_Meta_maxStepsOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__1 = _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__1);
l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__2 = _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__2);
l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__3 = _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__1___closed__3);
l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__1 = _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__1);
l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__2 = _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__2);
l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__3 = _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__2___closed__3);
l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__1 = _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__1);
l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__2 = _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__2);
l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__3 = _init_l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___lambda__4___closed__3);
l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__1 = _init_l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__1);
l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__2 = _init_l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__2);
l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__3 = _init_l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_10__synthInstanceImp___closed__3);
l_Lean_Meta_setSynthPendingRef___closed__1 = _init_l_Lean_Meta_setSynthPendingRef___closed__1();
lean_mark_persistent(l_Lean_Meta_setSynthPendingRef___closed__1);
res = l_Lean_Meta_setSynthPendingRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_SynthInstance_12__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Meta.LevelDefEq
// Imports: Init Lean.Util.CollectMVars Lean.Util.ReplaceExpr Lean.Meta.Basic Lean.Meta.InferType
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
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__4;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1037____closed__2;
lean_object* l_Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses_match__1(lean_object*);
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isListLevelDefEqAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Level_collectMVars(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed_loop___closed__5;
lean_object* l_Lean_throwError___at_Lean_Meta_whnf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_termDepIfThenElse___closed__11;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unifConstraint___closed__3;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___closed__2;
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6;
lean_object* l_Lean_Meta_processPostponed_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_append___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(uint8_t, uint8_t);
extern lean_object* l_Std_PersistentArray_empty___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___closed__5;
lean_object* l_Lean_throwError___at_Lean_Meta_decLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___closed__3;
lean_object* l_Lean_Meta_checkpointDefEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore_match__2(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3;
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__3(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffsetAux(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_933____closed__1;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5;
lean_object* l_Lean_Level_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed_loop___closed__1;
extern lean_object* l_Lean_levelZero;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isListLevelDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4;
lean_object* l_Lean_Expr_setPPUniverses(lean_object*, uint8_t);
uint8_t l_Lean_Level_isParam(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__10(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_List_foldr___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getLevelAssignment_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__9(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__3;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_any(lean_object*, lean_object*);
lean_object* lean_level_mk_max_simp(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__4(lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg(lean_object*);
lean_object* l_Lean_Meta_mkLevelErrorMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed_loop___closed__6;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__11(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux___closed__1;
lean_object* l_Lean_Meta_checkpointDefEq_match__1(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___boxed(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
uint8_t l_Std_PersistentArray_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__5;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve_match__1(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_mkLevelStuckErrorMessage___closed__1;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___closed__6;
lean_object* l_Lean_Meta_mkLevelStuckErrorMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff_match__1(lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___closed__1;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Meta_decLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3;
lean_object* l_Lean_Meta_processPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelSucc(lean_object*);
extern lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit_match__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_decLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed_loop(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___closed__2;
lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed_loop___closed__3;
uint8_t l_Lean_MetavarContext_hasAssignableLevelMVar(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_toArray___rarg(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___closed__4;
lean_object* l_Lean_Meta_isDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__1;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__2(lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isMVar(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed_loop___closed__4;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
lean_object* l_Lean_Level_getLevelOffset(lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqNoConstantApprox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isListLevelDefEqAux_match__1(lean_object*);
lean_object* l_Lean_Meta_checkpointDefEq_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__2(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___closed__1;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
lean_object* l_Lean_Meta_checkpointDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses(lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed_loop___closed__2;
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore_match__1(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___closed__3;
lean_object* l_Lean_Meta_isLevelDefEq___closed__2;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__5(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep_match__1(lean_object*);
extern lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getResetPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_LevelDefEq___hyg_2828_(lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLevelErrorMessage___closed__1;
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux_match__1(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__2;
extern lean_object* l_Array_findSomeM_x3f___rarg___closed__1;
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isMax(lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_3(x_2, x_5, x_6, x_8);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_3, x_10, x_11, x_13);
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_apply_1(x_4, x_1);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_2(x_5, x_10, x_12);
return x_13;
}
case 4:
{
lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_16 = lean_box_uint64(x_15);
x_17 = lean_apply_2(x_3, x_14, x_16);
return x_17;
}
case 5:
{
lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_20 = lean_box_uint64(x_19);
x_21 = lean_apply_2(x_4, x_18, x_20);
return x_21;
}
default: 
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_apply_1(x_6, x_1);
return x_22;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f_match__4___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(x_11, x_2, x_3, x_4, x_5, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_22, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_level_mk_max_simp(x_21, x_33);
lean_ctor_set(x_23, 0, x_34);
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_level_mk_max_simp(x_21, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_22, 0, x_37);
return x_22;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_ctor_get(x_23, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_40 = x_23;
} else {
 lean_dec_ref(x_23);
 x_40 = lean_box(0);
}
x_41 = lean_level_mk_max_simp(x_21, x_39);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_21);
x_44 = !lean_is_exclusive(x_22);
if (x_44 == 0)
{
return x_22;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get(x_22, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_22);
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
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_12);
if (x_48 == 0)
{
return x_12;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_12, 0);
x_50 = lean_ctor_get(x_12, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_12);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
case 3:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_dec(x_1);
x_54 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(x_52, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
lean_dec(x_53);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
x_58 = lean_box(0);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_dec(x_54);
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
lean_dec(x_55);
x_64 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(x_53, x_2, x_3, x_4, x_5, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
lean_dec(x_63);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = lean_box(0);
lean_ctor_set(x_64, 0, x_68);
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_64, 0);
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_65);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_65, 0);
x_76 = lean_level_mk_max_simp(x_63, x_75);
lean_ctor_set(x_65, 0, x_76);
return x_64;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_65, 0);
lean_inc(x_77);
lean_dec(x_65);
x_78 = lean_level_mk_max_simp(x_63, x_77);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_64, 0, x_79);
return x_64;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_64, 1);
lean_inc(x_80);
lean_dec(x_64);
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_82 = x_65;
} else {
 lean_dec_ref(x_65);
 x_82 = lean_box(0);
}
x_83 = lean_level_mk_max_simp(x_63, x_81);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_63);
x_86 = !lean_is_exclusive(x_64);
if (x_86 == 0)
{
return x_64;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_64, 0);
x_88 = lean_ctor_get(x_64, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_64);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_53);
x_90 = !lean_is_exclusive(x_54);
if (x_90 == 0)
{
return x_54;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_54, 0);
x_92 = lean_ctor_get(x_54, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_54);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
case 5:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_1, 0);
lean_inc(x_94);
lean_dec(x_1);
x_95 = lean_st_ref_get(x_5, x_6);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_st_ref_get(x_3, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_MetavarContext_getLevelAssignment_x3f(x_100, x_94);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
lean_inc(x_94);
x_102 = l_Lean_Meta_isReadOnlyLevelMVar(x_94, x_2, x_3, x_4, x_5, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_3, x_4, x_5, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_107);
x_109 = l_Lean_mkLevelSucc(x_107);
x_110 = l_Lean_Meta_assignLevelMVar(x_94, x_109, x_2, x_3, x_4, x_5, x_108);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_110, 0);
lean_dec(x_112);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_110, 0, x_113);
return x_110;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec(x_110);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_107);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_94);
x_117 = !lean_is_exclusive(x_102);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_102, 0);
lean_dec(x_118);
x_119 = lean_box(0);
lean_ctor_set(x_102, 0, x_119);
return x_102;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_102, 1);
lean_inc(x_120);
lean_dec(x_102);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_94);
x_123 = !lean_is_exclusive(x_102);
if (x_123 == 0)
{
return x_102;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_102, 0);
x_125 = lean_ctor_get(x_102, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_102);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; 
lean_dec(x_94);
x_127 = lean_ctor_get(x_101, 0);
lean_inc(x_127);
lean_dec(x_101);
x_1 = x_127;
x_6 = x_99;
goto _start;
}
}
default: 
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_1);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_6);
return x_130;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_decLevel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
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
x_13 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(x_1, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_5, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_take(x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_12);
x_23 = lean_st_ref_set(x_3, x_19, x_20);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_19, 1);
x_31 = lean_ctor_get(x_19, 2);
x_32 = lean_ctor_get(x_19, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_st_ref_set(x_3, x_33, x_20);
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
uint8_t x_39; 
lean_dec(x_12);
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_13, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
return x_13;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_14, 0);
lean_inc(x_42);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_13, 0, x_43);
return x_13;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_dec(x_13);
x_45 = lean_ctor_get(x_14, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_46 = x_14;
} else {
 lean_dec_ref(x_14);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_12);
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
return x_13;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_13);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_Meta_decLevel_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_decLevel_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_decLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_Meta_decLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid universe level, ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_decLevel___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" is not greater than 0");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_decLevel___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_decLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_decLevel_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = l_Lean_Meta_decLevel___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_decLevel___closed__4;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Meta_decLevel___spec__1(x_14, x_2, x_3, x_4, x_5, x_9);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_decLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_decLevel___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_decLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_decLevel(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_getDecLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_getLevel(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_decLevel(x_8, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(x_1, x_3);
if (x_5 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = lean_level_eq(x_2, x_1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Level_occurs(x_1, x_2);
return x_9;
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
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(x_1, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_4(x_3, x_6, x_7, x_9, x_2);
return x_10;
}
case 5:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_4(x_4, x_1, x_11, x_13, x_2);
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_apply_2(x_5, x_1, x_2);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(x_1, x_4, x_3);
x_2 = x_5;
x_3 = x_6;
goto _start;
}
case 5:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_level_mk_max_simp(x_3, x_2);
return x_10;
}
else
{
lean_dec(x_2);
return x_3;
}
}
default: 
{
lean_object* x_11; 
x_11 = lean_level_mk_max_simp(x_3, x_2);
return x_11;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("v.isMax3004");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_instantiateBetaRevRange___closed__1;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.LevelDefEq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.LevelDefEq.0.Lean.Meta.solveSelfMax");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5;
x_3 = lean_unsigned_to_nat(82u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Level_isMax(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1;
x_10 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6;
x_11 = lean_panic_fn(x_9, x_10);
x_12 = lean_apply_5(x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(x_1, x_2, x_14);
x_17 = l_Lean_Meta_assignLevelMVar(x_1, x_16, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 3);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_1);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_1);
x_21 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
x_26 = l_Lean_KernelException_toMessageData___closed__15;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Std_PersistentArray_push___rarg(x_19, x_29);
lean_ctor_set(x_14, 0, x_30);
x_31 = lean_st_ref_set(x_6, x_13, x_15);
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
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_38 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_39 = lean_ctor_get(x_14, 0);
lean_inc(x_39);
lean_dec(x_14);
lean_inc(x_1);
x_40 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_40, 0, x_1);
x_41 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_10);
x_46 = l_Lean_KernelException_toMessageData___closed__15;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_8);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_8);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Std_PersistentArray_push___rarg(x_39, x_49);
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_38);
lean_ctor_set(x_13, 3, x_51);
x_52 = lean_st_ref_set(x_6, x_13, x_15);
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
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
x_59 = lean_ctor_get(x_13, 2);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_60 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_61 = lean_ctor_get(x_14, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_62 = x_14;
} else {
 lean_dec_ref(x_14);
 x_62 = lean_box(0);
}
lean_inc(x_1);
x_63 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_63, 0, x_1);
x_64 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_10);
x_69 = l_Lean_KernelException_toMessageData___closed__15;
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_70);
lean_inc(x_8);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_8);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Std_PersistentArray_push___rarg(x_61, x_72);
if (lean_is_scalar(x_62)) {
 x_74 = lean_alloc_ctor(0, 1, 1);
} else {
 x_74 = x_62;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_60);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_57);
lean_ctor_set(x_75, 1, x_58);
lean_ctor_set(x_75, 2, x_59);
lean_ctor_set(x_75, 3, x_74);
x_76 = lean_st_ref_set(x_6, x_75, x_15);
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
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Lean_checkTraceOption(x_7, x_1);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isLevelDefEq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1037____closed__2;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("stuck");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_unifConstraint___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_41; lean_object* x_42; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_8 = lean_ctor_get(x_5, 3);
x_55 = lean_st_ref_get(x_6, x_7);
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
x_41 = x_60;
x_42 = x_59;
goto block_54;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
x_62 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_63 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_62, x_3, x_4, x_5, x_6, x_61);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_unbox(x_64);
lean_dec(x_64);
x_41 = x_66;
x_42 = x_65;
goto block_54;
}
block_40:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_13, 3);
x_17 = lean_ctor_get(x_3, 3);
lean_inc(x_17);
lean_inc(x_8);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 3, x_17);
x_19 = l_Std_PersistentArray_push___rarg(x_16, x_18);
lean_ctor_set(x_13, 3, x_19);
x_20 = lean_st_ref_set(x_4, x_13, x_14);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
x_29 = lean_ctor_get(x_13, 2);
x_30 = lean_ctor_get(x_13, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_31 = lean_ctor_get(x_3, 3);
lean_inc(x_31);
lean_inc(x_8);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_1);
lean_ctor_set(x_32, 2, x_2);
lean_ctor_set(x_32, 3, x_31);
x_33 = l_Std_PersistentArray_push___rarg(x_30, x_32);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_st_ref_set(x_4, x_34, x_14);
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
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
block_54:
{
if (x_41 == 0)
{
x_9 = x_42;
goto block_40;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_inc(x_1);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_1);
x_44 = l_Lean_KernelException_toMessageData___closed__15;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_2);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_2);
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
x_51 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_52 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_51, x_50, x_3, x_4, x_5, x_6, x_42);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_9 = x_53;
goto block_40;
}
}
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_7);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 1:
{
uint64_t x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_12 = lean_box_uint64(x_9);
x_13 = lean_box_uint64(x_11);
x_14 = lean_apply_3(x_6, x_12, x_10, x_13);
return x_14;
}
case 2:
{
uint64_t x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_19 = lean_box_uint64(x_15);
x_20 = lean_box_uint64(x_18);
x_21 = lean_apply_4(x_4, x_19, x_16, x_17, x_20);
return x_21;
}
case 3:
{
uint64_t x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_22 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_26 = lean_box_uint64(x_22);
x_27 = lean_box_uint64(x_25);
x_28 = lean_apply_4(x_5, x_26, x_23, x_24, x_27);
return x_28;
}
default: 
{
lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = lean_apply_2(x_8, x_1, x_2);
return x_29;
}
}
}
case 1:
{
lean_object* x_30; uint64_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_32 = lean_box_uint64(x_31);
x_33 = lean_apply_3(x_7, x_30, x_32, x_2);
return x_33;
}
case 5:
{
lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_3(x_3, x_34, x_36, x_2);
return x_37;
}
default: 
{
lean_object* x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = lean_apply_2(x_8, x_1, x_2);
return x_38;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve_match__1___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isLevelDefEqAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_9 = lean_box_uint64(x_6);
x_10 = lean_box_uint64(x_8);
x_11 = lean_apply_4(x_3, x_5, x_9, x_7, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_apply_2(x_4, x_1, x_2);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_apply_2(x_4, x_1, x_2);
return x_13;
}
}
}
lean_object* l_Lean_Meta_isLevelDefEqAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAux_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_1);
switch (lean_obj_tag(x_2)) {
case 1:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_levelZero;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_isLevelDefEqAux(x_13, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_unbox(x_15);
lean_dec(x_15);
x_20 = l_Bool_toLBool(x_19);
x_21 = lean_box(x_20);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_unbox(x_15);
lean_dec(x_15);
x_24 = l_Bool_toLBool(x_23);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = l_Lean_Meta_isLevelDefEqAux(x_13, x_12, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
x_32 = l_Bool_toLBool(x_31);
x_33 = lean_box(x_32);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_unbox(x_34);
lean_dec(x_34);
x_37 = l_Bool_toLBool(x_36);
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
uint8_t x_40; 
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
}
else
{
uint8_t x_44; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 3:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec(x_2);
x_49 = l_Lean_levelZero;
x_50 = l_Lean_Meta_isLevelDefEqAux(x_49, x_48, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
x_54 = l_Bool_toLBool(x_53);
x_55 = lean_box(x_54);
lean_ctor_set(x_50, 0, x_55);
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_unbox(x_56);
lean_dec(x_56);
x_59 = l_Bool_toLBool(x_58);
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
return x_50;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_50, 0);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_50);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
default: 
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = 2;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_7);
return x_68;
}
}
}
case 1:
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
lean_dec(x_1);
x_70 = l_Lean_Level_isParam(x_2);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = l_Lean_Level_isMVar(x_69);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = l_Lean_Meta_decLevel_x3f(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
lean_dec(x_75);
x_76 = 2;
x_77 = lean_box(x_76);
lean_ctor_set(x_72, 0, x_77);
return x_72;
}
else
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = 2;
x_80 = lean_box(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_72, 1);
lean_inc(x_82);
lean_dec(x_72);
x_83 = lean_ctor_get(x_73, 0);
lean_inc(x_83);
lean_dec(x_73);
x_84 = l_Lean_Meta_isLevelDefEqAux(x_69, x_83, x_3, x_4, x_5, x_6, x_82);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
x_88 = l_Bool_toLBool(x_87);
x_89 = lean_box(x_88);
lean_ctor_set(x_84, 0, x_89);
return x_84;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_84, 0);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_84);
x_92 = lean_unbox(x_90);
lean_dec(x_90);
x_93 = l_Bool_toLBool(x_92);
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
return x_95;
}
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_84);
if (x_96 == 0)
{
return x_84;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_84, 0);
x_98 = lean_ctor_get(x_84, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_84);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_72);
if (x_100 == 0)
{
return x_72;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_72, 0);
x_102 = lean_ctor_get(x_72, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_72);
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
x_104 = l_Lean_Level_occurs(x_69, x_2);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = l_Lean_Meta_decLevel_x3f(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_107; 
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_105, 0);
lean_dec(x_108);
x_109 = 2;
x_110 = lean_box(x_109);
lean_ctor_set(x_105, 0, x_110);
return x_105;
}
else
{
lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_dec(x_105);
x_112 = 2;
x_113 = lean_box(x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_105, 1);
lean_inc(x_115);
lean_dec(x_105);
x_116 = lean_ctor_get(x_106, 0);
lean_inc(x_116);
lean_dec(x_106);
x_117 = l_Lean_Meta_isLevelDefEqAux(x_69, x_116, x_3, x_4, x_5, x_6, x_115);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
x_121 = l_Bool_toLBool(x_120);
x_122 = lean_box(x_121);
lean_ctor_set(x_117, 0, x_122);
return x_117;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_ctor_get(x_117, 0);
x_124 = lean_ctor_get(x_117, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_117);
x_125 = lean_unbox(x_123);
lean_dec(x_123);
x_126 = l_Bool_toLBool(x_125);
x_127 = lean_box(x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_124);
return x_128;
}
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_117);
if (x_129 == 0)
{
return x_117;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_117, 0);
x_131 = lean_ctor_get(x_117, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_117);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_133 = !lean_is_exclusive(x_105);
if (x_133 == 0)
{
return x_105;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_105, 0);
x_135 = lean_ctor_get(x_105, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_105);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = 2;
x_138 = lean_box(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_7);
return x_139;
}
}
}
else
{
uint8_t x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_140 = 0;
x_141 = lean_box(x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_7);
return x_142;
}
}
case 5:
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_1, 0);
lean_inc(x_143);
x_144 = l_Lean_Meta_isReadOnlyLevelMVar(x_143, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_144);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = lean_ctor_get(x_144, 1);
x_149 = lean_ctor_get(x_144, 0);
lean_dec(x_149);
x_150 = l_Lean_Level_occurs(x_1, x_2);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_free_object(x_144);
x_151 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_152 = l_Lean_Meta_assignLevelMVar(x_151, x_2, x_3, x_4, x_5, x_6, x_148);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_152, 0);
lean_dec(x_154);
x_155 = 1;
x_156 = lean_box(x_155);
lean_ctor_set(x_152, 0, x_156);
return x_152;
}
else
{
lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_152, 1);
lean_inc(x_157);
lean_dec(x_152);
x_158 = 1;
x_159 = lean_box(x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
}
else
{
uint8_t x_161; 
x_161 = l_Lean_Level_isMax(x_2);
if (x_161 == 0)
{
uint8_t x_162; lean_object* x_163; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = 2;
x_163 = lean_box(x_162);
lean_ctor_set(x_144, 0, x_163);
return x_144;
}
else
{
uint8_t x_164; 
x_164 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_free_object(x_144);
x_165 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_166 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(x_165, x_2, x_3, x_4, x_5, x_6, x_148);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_166, 0);
lean_dec(x_168);
x_169 = 1;
x_170 = lean_box(x_169);
lean_ctor_set(x_166, 0, x_170);
return x_166;
}
else
{
lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
lean_dec(x_166);
x_172 = 1;
x_173 = lean_box(x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
return x_174;
}
}
else
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_166);
if (x_175 == 0)
{
return x_166;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_166, 0);
x_177 = lean_ctor_get(x_166, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_166);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
uint8_t x_179; lean_object* x_180; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_179 = 2;
x_180 = lean_box(x_179);
lean_ctor_set(x_144, 0, x_180);
return x_144;
}
}
}
}
else
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_144, 1);
lean_inc(x_181);
lean_dec(x_144);
x_182 = l_Lean_Level_occurs(x_1, x_2);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; 
x_183 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_184 = l_Lean_Meta_assignLevelMVar(x_183, x_2, x_3, x_4, x_5, x_6, x_181);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_186 = x_184;
} else {
 lean_dec_ref(x_184);
 x_186 = lean_box(0);
}
x_187 = 1;
x_188 = lean_box(x_187);
if (lean_is_scalar(x_186)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_186;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_185);
return x_189;
}
else
{
uint8_t x_190; 
x_190 = l_Lean_Level_isMax(x_2);
if (x_190 == 0)
{
uint8_t x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = 2;
x_192 = lean_box(x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_181);
return x_193;
}
else
{
uint8_t x_194; 
x_194 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_196 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(x_195, x_2, x_3, x_4, x_5, x_6, x_181);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; 
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
x_199 = 1;
x_200 = lean_box(x_199);
if (lean_is_scalar(x_198)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_198;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_197);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_196, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_196, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_204 = x_196;
} else {
 lean_dec_ref(x_196);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
else
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_206 = 2;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_181);
return x_208;
}
}
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = !lean_is_exclusive(x_144);
if (x_209 == 0)
{
lean_object* x_210; uint8_t x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_144, 0);
lean_dec(x_210);
x_211 = 2;
x_212 = lean_box(x_211);
lean_ctor_set(x_144, 0, x_212);
return x_144;
}
else
{
lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_144, 1);
lean_inc(x_213);
lean_dec(x_144);
x_214 = 2;
x_215 = lean_box(x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_213);
return x_216;
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = !lean_is_exclusive(x_144);
if (x_217 == 0)
{
return x_144;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_144, 0);
x_219 = lean_ctor_get(x_144, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_144);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
default: 
{
uint8_t x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = 2;
x_222 = lean_box(x_221);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_7);
return x_223;
}
}
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_2 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_933____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_isLevelDefEqAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Level_getLevelOffset(x_1);
x_9 = l_Lean_Level_getLevelOffset(x_2);
x_10 = lean_level_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_340; lean_object* x_341; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_354 = lean_st_ref_get(x_6, x_7);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_355, 3);
lean_inc(x_356);
lean_dec(x_355);
x_357 = lean_ctor_get_uint8(x_356, sizeof(void*)*1);
lean_dec(x_356);
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; 
x_358 = lean_ctor_get(x_354, 1);
lean_inc(x_358);
lean_dec(x_354);
x_359 = 0;
x_340 = x_359;
x_341 = x_358;
goto block_353;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; 
x_360 = lean_ctor_get(x_354, 1);
lean_inc(x_360);
lean_dec(x_354);
x_361 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_362 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_361, x_3, x_4, x_5, x_6, x_360);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_365 = lean_unbox(x_363);
lean_dec(x_363);
x_340 = x_365;
x_341 = x_364;
goto block_353;
}
block_339:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_1);
x_12 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Level_normalize(x_13);
lean_dec(x_13);
lean_inc(x_2);
x_16 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_2, x_3, x_4, x_5, x_6, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Level_normalize(x_17);
lean_dec(x_17);
x_20 = lean_level_eq(x_1, x_15);
if (x_20 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_15;
x_2 = x_19;
x_7 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = lean_level_eq(x_2, x_19);
if (x_22 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_15;
x_2 = x_19;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = 2;
x_29 = lean_unbox(x_26);
x_30 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_29, x_28);
if (x_30 == 0)
{
uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = 1;
x_32 = lean_unbox(x_26);
lean_dec(x_26);
x_33 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_32, x_31);
x_34 = lean_box(x_33);
lean_ctor_set(x_24, 0, x_34);
return x_24;
}
else
{
lean_object* x_35; 
lean_free_object(x_24);
lean_dec(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_35 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_unbox(x_37);
x_40 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_39, x_28);
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = 1;
x_42 = lean_unbox(x_37);
lean_dec(x_37);
x_43 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_42, x_41);
x_44 = lean_box(x_43);
lean_ctor_set(x_35, 0, x_44);
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_35);
lean_dec(x_37);
x_45 = lean_st_ref_get(x_6, x_38);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_st_ref_get(x_4, x_46);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_51);
x_52 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_51, x_1);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_51, x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_3, 0);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_84, 4);
lean_dec(x_84);
if (x_85 == 0)
{
uint8_t x_86; lean_object* x_87; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = 0;
x_87 = lean_box(x_86);
lean_ctor_set(x_47, 0, x_87);
return x_47;
}
else
{
uint8_t x_88; 
x_88 = l_Lean_Level_isMVar(x_1);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Level_isMVar(x_2);
if (x_89 == 0)
{
uint8_t x_90; lean_object* x_91; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = 0;
x_91 = lean_box(x_90);
lean_ctor_set(x_47, 0, x_91);
return x_47;
}
else
{
lean_object* x_92; 
lean_free_object(x_47);
x_92 = lean_box(0);
x_54 = x_92;
goto block_83;
}
}
else
{
lean_object* x_93; 
lean_free_object(x_47);
x_93 = lean_box(0);
x_54 = x_93;
goto block_83;
}
}
block_83:
{
uint8_t x_55; lean_object* x_56; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_54);
x_71 = lean_st_ref_get(x_6, x_50);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 3);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_ctor_get_uint8(x_73, sizeof(void*)*1);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = 0;
x_55 = x_76;
x_56 = x_75;
goto block_70;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_dec(x_71);
x_78 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_79 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_78, x_3, x_4, x_5, x_6, x_77);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_unbox(x_80);
lean_dec(x_80);
x_55 = x_82;
x_56 = x_81;
goto block_70;
}
block_70:
{
if (x_55 == 0)
{
lean_object* x_57; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_1);
x_59 = l_Lean_KernelException_toMessageData___closed__15;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_2);
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
x_66 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_67 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_66, x_65, x_3, x_4, x_5, x_6, x_56);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_94; uint8_t x_95; 
lean_free_object(x_47);
x_94 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_50);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
x_97 = 1;
x_98 = lean_box(x_97);
lean_ctor_set(x_94, 0, x_98);
return x_94;
}
else
{
lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_dec(x_94);
x_100 = 1;
x_101 = lean_box(x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
}
else
{
lean_object* x_103; uint8_t x_104; 
lean_dec(x_51);
lean_free_object(x_47);
x_103 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_50);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_103, 0);
lean_dec(x_105);
x_106 = 1;
x_107 = lean_box(x_106);
lean_ctor_set(x_103, 0, x_107);
return x_103;
}
else
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_dec(x_103);
x_109 = 1;
x_110 = lean_box(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_47, 0);
x_113 = lean_ctor_get(x_47, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_47);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
lean_dec(x_112);
lean_inc(x_114);
x_115 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_114, x_1);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_114, x_2);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_3, 0);
lean_inc(x_147);
x_148 = lean_ctor_get_uint8(x_147, 4);
lean_dec(x_147);
if (x_148 == 0)
{
uint8_t x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = 0;
x_150 = lean_box(x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_113);
return x_151;
}
else
{
uint8_t x_152; 
x_152 = l_Lean_Level_isMVar(x_1);
if (x_152 == 0)
{
uint8_t x_153; 
x_153 = l_Lean_Level_isMVar(x_2);
if (x_153 == 0)
{
uint8_t x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = 0;
x_155 = lean_box(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_113);
return x_156;
}
else
{
lean_object* x_157; 
x_157 = lean_box(0);
x_117 = x_157;
goto block_146;
}
}
else
{
lean_object* x_158; 
x_158 = lean_box(0);
x_117 = x_158;
goto block_146;
}
}
block_146:
{
uint8_t x_118; lean_object* x_119; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
lean_dec(x_117);
x_134 = lean_st_ref_get(x_6, x_113);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 3);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_ctor_get_uint8(x_136, sizeof(void*)*1);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
lean_dec(x_134);
x_139 = 0;
x_118 = x_139;
x_119 = x_138;
goto block_133;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
lean_dec(x_134);
x_141 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_142 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_141, x_3, x_4, x_5, x_6, x_140);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_unbox(x_143);
lean_dec(x_143);
x_118 = x_145;
x_119 = x_144;
goto block_133;
}
block_133:
{
if (x_118 == 0)
{
lean_object* x_120; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_119);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_121 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_121, 0, x_1);
x_122 = l_Lean_KernelException_toMessageData___closed__15;
x_123 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_125 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_126, 0, x_2);
x_127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_122);
x_129 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_130 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_129, x_128, x_3, x_4, x_5, x_6, x_119);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_131);
return x_132;
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; 
x_159 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_113);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_162 = 1;
x_163 = lean_box(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_114);
x_165 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_113);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
x_168 = 1;
x_169 = lean_box(x_168);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
return x_170;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_174; 
x_171 = lean_ctor_get(x_35, 0);
x_172 = lean_ctor_get(x_35, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_35);
x_173 = lean_unbox(x_171);
x_174 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_173, x_28);
if (x_174 == 0)
{
uint8_t x_175; uint8_t x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_175 = 1;
x_176 = lean_unbox(x_171);
lean_dec(x_171);
x_177 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_176, x_175);
x_178 = lean_box(x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_172);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
lean_dec(x_171);
x_180 = lean_st_ref_get(x_6, x_172);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_st_ref_get(x_4, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
lean_dec(x_183);
lean_inc(x_186);
x_187 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_186, x_1);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_186, x_2);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_219; uint8_t x_220; 
x_219 = lean_ctor_get(x_3, 0);
lean_inc(x_219);
x_220 = lean_ctor_get_uint8(x_219, 4);
lean_dec(x_219);
if (x_220 == 0)
{
uint8_t x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = 0;
x_222 = lean_box(x_221);
if (lean_is_scalar(x_185)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_185;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_184);
return x_223;
}
else
{
uint8_t x_224; 
x_224 = l_Lean_Level_isMVar(x_1);
if (x_224 == 0)
{
uint8_t x_225; 
x_225 = l_Lean_Level_isMVar(x_2);
if (x_225 == 0)
{
uint8_t x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_226 = 0;
x_227 = lean_box(x_226);
if (lean_is_scalar(x_185)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_185;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_184);
return x_228;
}
else
{
lean_object* x_229; 
lean_dec(x_185);
x_229 = lean_box(0);
x_189 = x_229;
goto block_218;
}
}
else
{
lean_object* x_230; 
lean_dec(x_185);
x_230 = lean_box(0);
x_189 = x_230;
goto block_218;
}
}
block_218:
{
uint8_t x_190; lean_object* x_191; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
lean_dec(x_189);
x_206 = lean_st_ref_get(x_6, x_184);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_207, 3);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_ctor_get_uint8(x_208, sizeof(void*)*1);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
lean_dec(x_206);
x_211 = 0;
x_190 = x_211;
x_191 = x_210;
goto block_205;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_212 = lean_ctor_get(x_206, 1);
lean_inc(x_212);
lean_dec(x_206);
x_213 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_214 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_213, x_3, x_4, x_5, x_6, x_212);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_unbox(x_215);
lean_dec(x_215);
x_190 = x_217;
x_191 = x_216;
goto block_205;
}
block_205:
{
if (x_190 == 0)
{
lean_object* x_192; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_192 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_191);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_193 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_193, 0, x_1);
x_194 = l_Lean_KernelException_toMessageData___closed__15;
x_195 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_197 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_198, 0, x_2);
x_199 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_194);
x_201 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_202 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_201, x_200, x_3, x_4, x_5, x_6, x_191);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_203);
return x_204;
}
}
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_185);
x_231 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_184);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_234 = 1;
x_235 = lean_box(x_234);
if (lean_is_scalar(x_233)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_233;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_232);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_186);
lean_dec(x_185);
x_237 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_184);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
x_240 = 1;
x_241 = lean_box(x_240);
if (lean_is_scalar(x_239)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_239;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_238);
return x_242;
}
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_243 = !lean_is_exclusive(x_35);
if (x_243 == 0)
{
return x_35;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_35, 0);
x_245 = lean_ctor_get(x_35, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_35);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
}
else
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; uint8_t x_250; uint8_t x_251; 
x_247 = lean_ctor_get(x_24, 0);
x_248 = lean_ctor_get(x_24, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_24);
x_249 = 2;
x_250 = lean_unbox(x_247);
x_251 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_250, x_249);
if (x_251 == 0)
{
uint8_t x_252; uint8_t x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_252 = 1;
x_253 = lean_unbox(x_247);
lean_dec(x_247);
x_254 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_253, x_252);
x_255 = lean_box(x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_248);
return x_256;
}
else
{
lean_object* x_257; 
lean_dec(x_247);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_257 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_248);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_262; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_260 = x_257;
} else {
 lean_dec_ref(x_257);
 x_260 = lean_box(0);
}
x_261 = lean_unbox(x_258);
x_262 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_261, x_249);
if (x_262 == 0)
{
uint8_t x_263; uint8_t x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_263 = 1;
x_264 = lean_unbox(x_258);
lean_dec(x_258);
x_265 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_264, x_263);
x_266 = lean_box(x_265);
if (lean_is_scalar(x_260)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_260;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_259);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
lean_dec(x_260);
lean_dec(x_258);
x_268 = lean_st_ref_get(x_6, x_259);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_270 = lean_st_ref_get(x_4, x_269);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_273 = x_270;
} else {
 lean_dec_ref(x_270);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_271, 0);
lean_inc(x_274);
lean_dec(x_271);
lean_inc(x_274);
x_275 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_274, x_1);
if (x_275 == 0)
{
uint8_t x_276; 
x_276 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_274, x_2);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_307; uint8_t x_308; 
x_307 = lean_ctor_get(x_3, 0);
lean_inc(x_307);
x_308 = lean_ctor_get_uint8(x_307, 4);
lean_dec(x_307);
if (x_308 == 0)
{
uint8_t x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_309 = 0;
x_310 = lean_box(x_309);
if (lean_is_scalar(x_273)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_273;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_272);
return x_311;
}
else
{
uint8_t x_312; 
x_312 = l_Lean_Level_isMVar(x_1);
if (x_312 == 0)
{
uint8_t x_313; 
x_313 = l_Lean_Level_isMVar(x_2);
if (x_313 == 0)
{
uint8_t x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_314 = 0;
x_315 = lean_box(x_314);
if (lean_is_scalar(x_273)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_273;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_272);
return x_316;
}
else
{
lean_object* x_317; 
lean_dec(x_273);
x_317 = lean_box(0);
x_277 = x_317;
goto block_306;
}
}
else
{
lean_object* x_318; 
lean_dec(x_273);
x_318 = lean_box(0);
x_277 = x_318;
goto block_306;
}
}
block_306:
{
uint8_t x_278; lean_object* x_279; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
lean_dec(x_277);
x_294 = lean_st_ref_get(x_6, x_272);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_295, 3);
lean_inc(x_296);
lean_dec(x_295);
x_297 = lean_ctor_get_uint8(x_296, sizeof(void*)*1);
lean_dec(x_296);
if (x_297 == 0)
{
lean_object* x_298; uint8_t x_299; 
x_298 = lean_ctor_get(x_294, 1);
lean_inc(x_298);
lean_dec(x_294);
x_299 = 0;
x_278 = x_299;
x_279 = x_298;
goto block_293;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_300 = lean_ctor_get(x_294, 1);
lean_inc(x_300);
lean_dec(x_294);
x_301 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_302 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_301, x_3, x_4, x_5, x_6, x_300);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_unbox(x_303);
lean_dec(x_303);
x_278 = x_305;
x_279 = x_304;
goto block_293;
}
block_293:
{
if (x_278 == 0)
{
lean_object* x_280; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_280 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_279);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_281 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_281, 0, x_1);
x_282 = l_Lean_KernelException_toMessageData___closed__15;
x_283 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_281);
x_284 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_285 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_286, 0, x_2);
x_287 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_282);
x_289 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_290 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_289, x_288, x_3, x_4, x_5, x_6, x_279);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec(x_290);
x_292 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_291);
return x_292;
}
}
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_273);
x_319 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_272);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_321 = x_319;
} else {
 lean_dec_ref(x_319);
 x_321 = lean_box(0);
}
x_322 = 1;
x_323 = lean_box(x_322);
if (lean_is_scalar(x_321)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_321;
}
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_320);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_274);
lean_dec(x_273);
x_325 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_272);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_326 = lean_ctor_get(x_325, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_327 = x_325;
} else {
 lean_dec_ref(x_325);
 x_327 = lean_box(0);
}
x_328 = 1;
x_329 = lean_box(x_328);
if (lean_is_scalar(x_327)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_327;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_326);
return x_330;
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_331 = lean_ctor_get(x_257, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_257, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_333 = x_257;
} else {
 lean_dec_ref(x_257);
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
}
else
{
uint8_t x_335; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_335 = !lean_is_exclusive(x_24);
if (x_335 == 0)
{
return x_24;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_24, 0);
x_337 = lean_ctor_get(x_24, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_24);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
return x_338;
}
}
}
}
}
block_353:
{
if (x_340 == 0)
{
x_11 = x_341;
goto block_339;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_inc(x_1);
x_342 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_342, 0, x_1);
x_343 = l_Lean_KernelException_toMessageData___closed__15;
x_344 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_342);
x_345 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_346 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
lean_inc(x_2);
x_347 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_347, 0, x_2);
x_348 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
x_349 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_343);
x_350 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_351 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_350, x_349, x_3, x_4, x_5, x_6, x_341);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec(x_351);
x_11 = x_352;
goto block_339;
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_366 = lean_unsigned_to_nat(0u);
x_367 = l_Lean_Level_getOffsetAux(x_1, x_366);
lean_dec(x_1);
x_368 = l_Lean_Level_getOffsetAux(x_2, x_366);
lean_dec(x_2);
x_369 = lean_nat_dec_eq(x_367, x_368);
lean_dec(x_368);
lean_dec(x_367);
x_370 = lean_box(x_369);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_7);
return x_371;
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_372 = l_Lean_Level_getLevelOffset(x_1);
x_373 = l_Lean_Level_getLevelOffset(x_2);
x_374 = lean_level_eq(x_372, x_373);
lean_dec(x_373);
lean_dec(x_372);
if (x_374 == 0)
{
lean_object* x_375; uint8_t x_704; lean_object* x_705; lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; 
x_718 = lean_st_ref_get(x_6, x_7);
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_719, 3);
lean_inc(x_720);
lean_dec(x_719);
x_721 = lean_ctor_get_uint8(x_720, sizeof(void*)*1);
lean_dec(x_720);
if (x_721 == 0)
{
lean_object* x_722; uint8_t x_723; 
x_722 = lean_ctor_get(x_718, 1);
lean_inc(x_722);
lean_dec(x_718);
x_723 = 0;
x_704 = x_723;
x_705 = x_722;
goto block_717;
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; 
x_724 = lean_ctor_get(x_718, 1);
lean_inc(x_724);
lean_dec(x_718);
x_725 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_726 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_725, x_3, x_4, x_5, x_6, x_724);
x_727 = lean_ctor_get(x_726, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_726, 1);
lean_inc(x_728);
lean_dec(x_726);
x_729 = lean_unbox(x_727);
lean_dec(x_727);
x_704 = x_729;
x_705 = x_728;
goto block_717;
}
block_703:
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
lean_inc(x_1);
x_376 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_375);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_379 = l_Lean_Level_normalize(x_377);
lean_dec(x_377);
lean_inc(x_2);
x_380 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_2, x_3, x_4, x_5, x_6, x_378);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = l_Lean_Level_normalize(x_381);
lean_dec(x_381);
x_384 = lean_level_eq(x_1, x_379);
if (x_384 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_379;
x_2 = x_383;
x_7 = x_382;
goto _start;
}
else
{
uint8_t x_386; 
x_386 = lean_level_eq(x_2, x_383);
if (x_386 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_379;
x_2 = x_383;
x_7 = x_382;
goto _start;
}
else
{
lean_object* x_388; 
lean_dec(x_383);
lean_dec(x_379);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_388 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_382);
if (lean_obj_tag(x_388) == 0)
{
uint8_t x_389; 
x_389 = !lean_is_exclusive(x_388);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; uint8_t x_393; uint8_t x_394; 
x_390 = lean_ctor_get(x_388, 0);
x_391 = lean_ctor_get(x_388, 1);
x_392 = 2;
x_393 = lean_unbox(x_390);
x_394 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_393, x_392);
if (x_394 == 0)
{
uint8_t x_395; uint8_t x_396; uint8_t x_397; lean_object* x_398; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_395 = 1;
x_396 = lean_unbox(x_390);
lean_dec(x_390);
x_397 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_396, x_395);
x_398 = lean_box(x_397);
lean_ctor_set(x_388, 0, x_398);
return x_388;
}
else
{
lean_object* x_399; 
lean_free_object(x_388);
lean_dec(x_390);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_399 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_391);
if (lean_obj_tag(x_399) == 0)
{
uint8_t x_400; 
x_400 = !lean_is_exclusive(x_399);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; uint8_t x_403; uint8_t x_404; 
x_401 = lean_ctor_get(x_399, 0);
x_402 = lean_ctor_get(x_399, 1);
x_403 = lean_unbox(x_401);
x_404 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_403, x_392);
if (x_404 == 0)
{
uint8_t x_405; uint8_t x_406; uint8_t x_407; lean_object* x_408; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_405 = 1;
x_406 = lean_unbox(x_401);
lean_dec(x_401);
x_407 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_406, x_405);
x_408 = lean_box(x_407);
lean_ctor_set(x_399, 0, x_408);
return x_399;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
lean_free_object(x_399);
lean_dec(x_401);
x_409 = lean_st_ref_get(x_6, x_402);
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
lean_dec(x_409);
x_411 = lean_st_ref_get(x_4, x_410);
x_412 = !lean_is_exclusive(x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
x_413 = lean_ctor_get(x_411, 0);
x_414 = lean_ctor_get(x_411, 1);
x_415 = lean_ctor_get(x_413, 0);
lean_inc(x_415);
lean_dec(x_413);
lean_inc(x_415);
x_416 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_415, x_1);
if (x_416 == 0)
{
uint8_t x_417; 
x_417 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_415, x_2);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_448; uint8_t x_449; 
x_448 = lean_ctor_get(x_3, 0);
lean_inc(x_448);
x_449 = lean_ctor_get_uint8(x_448, 4);
lean_dec(x_448);
if (x_449 == 0)
{
uint8_t x_450; lean_object* x_451; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_450 = 0;
x_451 = lean_box(x_450);
lean_ctor_set(x_411, 0, x_451);
return x_411;
}
else
{
uint8_t x_452; 
x_452 = l_Lean_Level_isMVar(x_1);
if (x_452 == 0)
{
uint8_t x_453; 
x_453 = l_Lean_Level_isMVar(x_2);
if (x_453 == 0)
{
uint8_t x_454; lean_object* x_455; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_454 = 0;
x_455 = lean_box(x_454);
lean_ctor_set(x_411, 0, x_455);
return x_411;
}
else
{
lean_object* x_456; 
lean_free_object(x_411);
x_456 = lean_box(0);
x_418 = x_456;
goto block_447;
}
}
else
{
lean_object* x_457; 
lean_free_object(x_411);
x_457 = lean_box(0);
x_418 = x_457;
goto block_447;
}
}
block_447:
{
uint8_t x_419; lean_object* x_420; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; 
lean_dec(x_418);
x_435 = lean_st_ref_get(x_6, x_414);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_436, 3);
lean_inc(x_437);
lean_dec(x_436);
x_438 = lean_ctor_get_uint8(x_437, sizeof(void*)*1);
lean_dec(x_437);
if (x_438 == 0)
{
lean_object* x_439; uint8_t x_440; 
x_439 = lean_ctor_get(x_435, 1);
lean_inc(x_439);
lean_dec(x_435);
x_440 = 0;
x_419 = x_440;
x_420 = x_439;
goto block_434;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; 
x_441 = lean_ctor_get(x_435, 1);
lean_inc(x_441);
lean_dec(x_435);
x_442 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_443 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_442, x_3, x_4, x_5, x_6, x_441);
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = lean_unbox(x_444);
lean_dec(x_444);
x_419 = x_446;
x_420 = x_445;
goto block_434;
}
block_434:
{
if (x_419 == 0)
{
lean_object* x_421; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_421 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_420);
return x_421;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_422 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_422, 0, x_1);
x_423 = l_Lean_KernelException_toMessageData___closed__15;
x_424 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_422);
x_425 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_426 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
x_427 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_427, 0, x_2);
x_428 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
x_429 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_423);
x_430 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_431 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_430, x_429, x_3, x_4, x_5, x_6, x_420);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_432 = lean_ctor_get(x_431, 1);
lean_inc(x_432);
lean_dec(x_431);
x_433 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_432);
return x_433;
}
}
}
}
else
{
lean_object* x_458; uint8_t x_459; 
lean_free_object(x_411);
x_458 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_414);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_459 = !lean_is_exclusive(x_458);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_458, 0);
lean_dec(x_460);
x_461 = 1;
x_462 = lean_box(x_461);
lean_ctor_set(x_458, 0, x_462);
return x_458;
}
else
{
lean_object* x_463; uint8_t x_464; lean_object* x_465; lean_object* x_466; 
x_463 = lean_ctor_get(x_458, 1);
lean_inc(x_463);
lean_dec(x_458);
x_464 = 1;
x_465 = lean_box(x_464);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_463);
return x_466;
}
}
}
else
{
lean_object* x_467; uint8_t x_468; 
lean_dec(x_415);
lean_free_object(x_411);
x_467 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_414);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_468 = !lean_is_exclusive(x_467);
if (x_468 == 0)
{
lean_object* x_469; uint8_t x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_467, 0);
lean_dec(x_469);
x_470 = 1;
x_471 = lean_box(x_470);
lean_ctor_set(x_467, 0, x_471);
return x_467;
}
else
{
lean_object* x_472; uint8_t x_473; lean_object* x_474; lean_object* x_475; 
x_472 = lean_ctor_get(x_467, 1);
lean_inc(x_472);
lean_dec(x_467);
x_473 = 1;
x_474 = lean_box(x_473);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_472);
return x_475;
}
}
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; 
x_476 = lean_ctor_get(x_411, 0);
x_477 = lean_ctor_get(x_411, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_411);
x_478 = lean_ctor_get(x_476, 0);
lean_inc(x_478);
lean_dec(x_476);
lean_inc(x_478);
x_479 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_478, x_1);
if (x_479 == 0)
{
uint8_t x_480; 
x_480 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_478, x_2);
if (x_480 == 0)
{
lean_object* x_481; lean_object* x_511; uint8_t x_512; 
x_511 = lean_ctor_get(x_3, 0);
lean_inc(x_511);
x_512 = lean_ctor_get_uint8(x_511, 4);
lean_dec(x_511);
if (x_512 == 0)
{
uint8_t x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_513 = 0;
x_514 = lean_box(x_513);
x_515 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_477);
return x_515;
}
else
{
uint8_t x_516; 
x_516 = l_Lean_Level_isMVar(x_1);
if (x_516 == 0)
{
uint8_t x_517; 
x_517 = l_Lean_Level_isMVar(x_2);
if (x_517 == 0)
{
uint8_t x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_518 = 0;
x_519 = lean_box(x_518);
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_477);
return x_520;
}
else
{
lean_object* x_521; 
x_521 = lean_box(0);
x_481 = x_521;
goto block_510;
}
}
else
{
lean_object* x_522; 
x_522 = lean_box(0);
x_481 = x_522;
goto block_510;
}
}
block_510:
{
uint8_t x_482; lean_object* x_483; lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; 
lean_dec(x_481);
x_498 = lean_st_ref_get(x_6, x_477);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_499, 3);
lean_inc(x_500);
lean_dec(x_499);
x_501 = lean_ctor_get_uint8(x_500, sizeof(void*)*1);
lean_dec(x_500);
if (x_501 == 0)
{
lean_object* x_502; uint8_t x_503; 
x_502 = lean_ctor_get(x_498, 1);
lean_inc(x_502);
lean_dec(x_498);
x_503 = 0;
x_482 = x_503;
x_483 = x_502;
goto block_497;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; 
x_504 = lean_ctor_get(x_498, 1);
lean_inc(x_504);
lean_dec(x_498);
x_505 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_506 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_505, x_3, x_4, x_5, x_6, x_504);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = lean_unbox(x_507);
lean_dec(x_507);
x_482 = x_509;
x_483 = x_508;
goto block_497;
}
block_497:
{
if (x_482 == 0)
{
lean_object* x_484; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_484 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_483);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_485 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_485, 0, x_1);
x_486 = l_Lean_KernelException_toMessageData___closed__15;
x_487 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_485);
x_488 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_489 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
x_490 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_490, 0, x_2);
x_491 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
x_492 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_486);
x_493 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_494 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_493, x_492, x_3, x_4, x_5, x_6, x_483);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
lean_dec(x_494);
x_496 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_495);
return x_496;
}
}
}
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; 
x_523 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_477);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_525 = x_523;
} else {
 lean_dec_ref(x_523);
 x_525 = lean_box(0);
}
x_526 = 1;
x_527 = lean_box(x_526);
if (lean_is_scalar(x_525)) {
 x_528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_528 = x_525;
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_524);
return x_528;
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_478);
x_529 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_477);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_530 = lean_ctor_get(x_529, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_531 = x_529;
} else {
 lean_dec_ref(x_529);
 x_531 = lean_box(0);
}
x_532 = 1;
x_533 = lean_box(x_532);
if (lean_is_scalar(x_531)) {
 x_534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_534 = x_531;
}
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_530);
return x_534;
}
}
}
}
else
{
lean_object* x_535; lean_object* x_536; uint8_t x_537; uint8_t x_538; 
x_535 = lean_ctor_get(x_399, 0);
x_536 = lean_ctor_get(x_399, 1);
lean_inc(x_536);
lean_inc(x_535);
lean_dec(x_399);
x_537 = lean_unbox(x_535);
x_538 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_537, x_392);
if (x_538 == 0)
{
uint8_t x_539; uint8_t x_540; uint8_t x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_539 = 1;
x_540 = lean_unbox(x_535);
lean_dec(x_535);
x_541 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_540, x_539);
x_542 = lean_box(x_541);
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_536);
return x_543;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_551; 
lean_dec(x_535);
x_544 = lean_st_ref_get(x_6, x_536);
x_545 = lean_ctor_get(x_544, 1);
lean_inc(x_545);
lean_dec(x_544);
x_546 = lean_st_ref_get(x_4, x_545);
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_546)) {
 lean_ctor_release(x_546, 0);
 lean_ctor_release(x_546, 1);
 x_549 = x_546;
} else {
 lean_dec_ref(x_546);
 x_549 = lean_box(0);
}
x_550 = lean_ctor_get(x_547, 0);
lean_inc(x_550);
lean_dec(x_547);
lean_inc(x_550);
x_551 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_550, x_1);
if (x_551 == 0)
{
uint8_t x_552; 
x_552 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_550, x_2);
if (x_552 == 0)
{
lean_object* x_553; lean_object* x_583; uint8_t x_584; 
x_583 = lean_ctor_get(x_3, 0);
lean_inc(x_583);
x_584 = lean_ctor_get_uint8(x_583, 4);
lean_dec(x_583);
if (x_584 == 0)
{
uint8_t x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_585 = 0;
x_586 = lean_box(x_585);
if (lean_is_scalar(x_549)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_549;
}
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_548);
return x_587;
}
else
{
uint8_t x_588; 
x_588 = l_Lean_Level_isMVar(x_1);
if (x_588 == 0)
{
uint8_t x_589; 
x_589 = l_Lean_Level_isMVar(x_2);
if (x_589 == 0)
{
uint8_t x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_590 = 0;
x_591 = lean_box(x_590);
if (lean_is_scalar(x_549)) {
 x_592 = lean_alloc_ctor(0, 2, 0);
} else {
 x_592 = x_549;
}
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_548);
return x_592;
}
else
{
lean_object* x_593; 
lean_dec(x_549);
x_593 = lean_box(0);
x_553 = x_593;
goto block_582;
}
}
else
{
lean_object* x_594; 
lean_dec(x_549);
x_594 = lean_box(0);
x_553 = x_594;
goto block_582;
}
}
block_582:
{
uint8_t x_554; lean_object* x_555; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; 
lean_dec(x_553);
x_570 = lean_st_ref_get(x_6, x_548);
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_571, 3);
lean_inc(x_572);
lean_dec(x_571);
x_573 = lean_ctor_get_uint8(x_572, sizeof(void*)*1);
lean_dec(x_572);
if (x_573 == 0)
{
lean_object* x_574; uint8_t x_575; 
x_574 = lean_ctor_get(x_570, 1);
lean_inc(x_574);
lean_dec(x_570);
x_575 = 0;
x_554 = x_575;
x_555 = x_574;
goto block_569;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; 
x_576 = lean_ctor_get(x_570, 1);
lean_inc(x_576);
lean_dec(x_570);
x_577 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_578 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_577, x_3, x_4, x_5, x_6, x_576);
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_578, 1);
lean_inc(x_580);
lean_dec(x_578);
x_581 = lean_unbox(x_579);
lean_dec(x_579);
x_554 = x_581;
x_555 = x_580;
goto block_569;
}
block_569:
{
if (x_554 == 0)
{
lean_object* x_556; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_556 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_555);
return x_556;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_557 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_557, 0, x_1);
x_558 = l_Lean_KernelException_toMessageData___closed__15;
x_559 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_557);
x_560 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_561 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_561, 0, x_559);
lean_ctor_set(x_561, 1, x_560);
x_562 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_562, 0, x_2);
x_563 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
x_564 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_558);
x_565 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_566 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_565, x_564, x_3, x_4, x_5, x_6, x_555);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_567 = lean_ctor_get(x_566, 1);
lean_inc(x_567);
lean_dec(x_566);
x_568 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_567);
return x_568;
}
}
}
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_549);
x_595 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_548);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_596 = lean_ctor_get(x_595, 1);
lean_inc(x_596);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 lean_ctor_release(x_595, 1);
 x_597 = x_595;
} else {
 lean_dec_ref(x_595);
 x_597 = lean_box(0);
}
x_598 = 1;
x_599 = lean_box(x_598);
if (lean_is_scalar(x_597)) {
 x_600 = lean_alloc_ctor(0, 2, 0);
} else {
 x_600 = x_597;
}
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_596);
return x_600;
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; lean_object* x_605; lean_object* x_606; 
lean_dec(x_550);
lean_dec(x_549);
x_601 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_548);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_602 = lean_ctor_get(x_601, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_603 = x_601;
} else {
 lean_dec_ref(x_601);
 x_603 = lean_box(0);
}
x_604 = 1;
x_605 = lean_box(x_604);
if (lean_is_scalar(x_603)) {
 x_606 = lean_alloc_ctor(0, 2, 0);
} else {
 x_606 = x_603;
}
lean_ctor_set(x_606, 0, x_605);
lean_ctor_set(x_606, 1, x_602);
return x_606;
}
}
}
}
else
{
uint8_t x_607; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_607 = !lean_is_exclusive(x_399);
if (x_607 == 0)
{
return x_399;
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_608 = lean_ctor_get(x_399, 0);
x_609 = lean_ctor_get(x_399, 1);
lean_inc(x_609);
lean_inc(x_608);
lean_dec(x_399);
x_610 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_610, 0, x_608);
lean_ctor_set(x_610, 1, x_609);
return x_610;
}
}
}
}
else
{
lean_object* x_611; lean_object* x_612; uint8_t x_613; uint8_t x_614; uint8_t x_615; 
x_611 = lean_ctor_get(x_388, 0);
x_612 = lean_ctor_get(x_388, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_388);
x_613 = 2;
x_614 = lean_unbox(x_611);
x_615 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_614, x_613);
if (x_615 == 0)
{
uint8_t x_616; uint8_t x_617; uint8_t x_618; lean_object* x_619; lean_object* x_620; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_616 = 1;
x_617 = lean_unbox(x_611);
lean_dec(x_611);
x_618 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_617, x_616);
x_619 = lean_box(x_618);
x_620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_612);
return x_620;
}
else
{
lean_object* x_621; 
lean_dec(x_611);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_621 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_612);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; uint8_t x_625; uint8_t x_626; 
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_624 = x_621;
} else {
 lean_dec_ref(x_621);
 x_624 = lean_box(0);
}
x_625 = lean_unbox(x_622);
x_626 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_625, x_613);
if (x_626 == 0)
{
uint8_t x_627; uint8_t x_628; uint8_t x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_627 = 1;
x_628 = lean_unbox(x_622);
lean_dec(x_622);
x_629 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_628, x_627);
x_630 = lean_box(x_629);
if (lean_is_scalar(x_624)) {
 x_631 = lean_alloc_ctor(0, 2, 0);
} else {
 x_631 = x_624;
}
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_623);
return x_631;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; uint8_t x_639; 
lean_dec(x_624);
lean_dec(x_622);
x_632 = lean_st_ref_get(x_6, x_623);
x_633 = lean_ctor_get(x_632, 1);
lean_inc(x_633);
lean_dec(x_632);
x_634 = lean_st_ref_get(x_4, x_633);
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_637 = x_634;
} else {
 lean_dec_ref(x_634);
 x_637 = lean_box(0);
}
x_638 = lean_ctor_get(x_635, 0);
lean_inc(x_638);
lean_dec(x_635);
lean_inc(x_638);
x_639 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_638, x_1);
if (x_639 == 0)
{
uint8_t x_640; 
x_640 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_638, x_2);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_671; uint8_t x_672; 
x_671 = lean_ctor_get(x_3, 0);
lean_inc(x_671);
x_672 = lean_ctor_get_uint8(x_671, 4);
lean_dec(x_671);
if (x_672 == 0)
{
uint8_t x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_673 = 0;
x_674 = lean_box(x_673);
if (lean_is_scalar(x_637)) {
 x_675 = lean_alloc_ctor(0, 2, 0);
} else {
 x_675 = x_637;
}
lean_ctor_set(x_675, 0, x_674);
lean_ctor_set(x_675, 1, x_636);
return x_675;
}
else
{
uint8_t x_676; 
x_676 = l_Lean_Level_isMVar(x_1);
if (x_676 == 0)
{
uint8_t x_677; 
x_677 = l_Lean_Level_isMVar(x_2);
if (x_677 == 0)
{
uint8_t x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_678 = 0;
x_679 = lean_box(x_678);
if (lean_is_scalar(x_637)) {
 x_680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_680 = x_637;
}
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_636);
return x_680;
}
else
{
lean_object* x_681; 
lean_dec(x_637);
x_681 = lean_box(0);
x_641 = x_681;
goto block_670;
}
}
else
{
lean_object* x_682; 
lean_dec(x_637);
x_682 = lean_box(0);
x_641 = x_682;
goto block_670;
}
}
block_670:
{
uint8_t x_642; lean_object* x_643; lean_object* x_658; lean_object* x_659; lean_object* x_660; uint8_t x_661; 
lean_dec(x_641);
x_658 = lean_st_ref_get(x_6, x_636);
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_659, 3);
lean_inc(x_660);
lean_dec(x_659);
x_661 = lean_ctor_get_uint8(x_660, sizeof(void*)*1);
lean_dec(x_660);
if (x_661 == 0)
{
lean_object* x_662; uint8_t x_663; 
x_662 = lean_ctor_get(x_658, 1);
lean_inc(x_662);
lean_dec(x_658);
x_663 = 0;
x_642 = x_663;
x_643 = x_662;
goto block_657;
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_669; 
x_664 = lean_ctor_get(x_658, 1);
lean_inc(x_664);
lean_dec(x_658);
x_665 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_666 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_665, x_3, x_4, x_5, x_6, x_664);
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_666, 1);
lean_inc(x_668);
lean_dec(x_666);
x_669 = lean_unbox(x_667);
lean_dec(x_667);
x_642 = x_669;
x_643 = x_668;
goto block_657;
}
block_657:
{
if (x_642 == 0)
{
lean_object* x_644; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_644 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_643);
return x_644;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_645 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_645, 0, x_1);
x_646 = l_Lean_KernelException_toMessageData___closed__15;
x_647 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_645);
x_648 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_649 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_648);
x_650 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_650, 0, x_2);
x_651 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_650);
x_652 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_646);
x_653 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_654 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_653, x_652, x_3, x_4, x_5, x_6, x_643);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_655 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
lean_dec(x_654);
x_656 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_655);
return x_656;
}
}
}
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; uint8_t x_686; lean_object* x_687; lean_object* x_688; 
lean_dec(x_637);
x_683 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_636);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_684 = lean_ctor_get(x_683, 1);
lean_inc(x_684);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_685 = x_683;
} else {
 lean_dec_ref(x_683);
 x_685 = lean_box(0);
}
x_686 = 1;
x_687 = lean_box(x_686);
if (lean_is_scalar(x_685)) {
 x_688 = lean_alloc_ctor(0, 2, 0);
} else {
 x_688 = x_685;
}
lean_ctor_set(x_688, 0, x_687);
lean_ctor_set(x_688, 1, x_684);
return x_688;
}
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; uint8_t x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_638);
lean_dec(x_637);
x_689 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_636);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_690 = lean_ctor_get(x_689, 1);
lean_inc(x_690);
if (lean_is_exclusive(x_689)) {
 lean_ctor_release(x_689, 0);
 lean_ctor_release(x_689, 1);
 x_691 = x_689;
} else {
 lean_dec_ref(x_689);
 x_691 = lean_box(0);
}
x_692 = 1;
x_693 = lean_box(x_692);
if (lean_is_scalar(x_691)) {
 x_694 = lean_alloc_ctor(0, 2, 0);
} else {
 x_694 = x_691;
}
lean_ctor_set(x_694, 0, x_693);
lean_ctor_set(x_694, 1, x_690);
return x_694;
}
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_695 = lean_ctor_get(x_621, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_621, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_697 = x_621;
} else {
 lean_dec_ref(x_621);
 x_697 = lean_box(0);
}
if (lean_is_scalar(x_697)) {
 x_698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_698 = x_697;
}
lean_ctor_set(x_698, 0, x_695);
lean_ctor_set(x_698, 1, x_696);
return x_698;
}
}
}
}
else
{
uint8_t x_699; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_699 = !lean_is_exclusive(x_388);
if (x_699 == 0)
{
return x_388;
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_700 = lean_ctor_get(x_388, 0);
x_701 = lean_ctor_get(x_388, 1);
lean_inc(x_701);
lean_inc(x_700);
lean_dec(x_388);
x_702 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_702, 0, x_700);
lean_ctor_set(x_702, 1, x_701);
return x_702;
}
}
}
}
}
block_717:
{
if (x_704 == 0)
{
x_375 = x_705;
goto block_703;
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_inc(x_1);
x_706 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_706, 0, x_1);
x_707 = l_Lean_KernelException_toMessageData___closed__15;
x_708 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_706);
x_709 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_710 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_710, 0, x_708);
lean_ctor_set(x_710, 1, x_709);
lean_inc(x_2);
x_711 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_711, 0, x_2);
x_712 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_712, 0, x_710);
lean_ctor_set(x_712, 1, x_711);
x_713 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_707);
x_714 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_715 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_714, x_713, x_3, x_4, x_5, x_6, x_705);
x_716 = lean_ctor_get(x_715, 1);
lean_inc(x_716);
lean_dec(x_715);
x_375 = x_716;
goto block_703;
}
}
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; uint8_t x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_730 = lean_unsigned_to_nat(0u);
x_731 = l_Lean_Level_getOffsetAux(x_1, x_730);
lean_dec(x_1);
x_732 = l_Lean_Level_getOffsetAux(x_2, x_730);
lean_dec(x_2);
x_733 = lean_nat_dec_eq(x_731, x_732);
lean_dec(x_732);
lean_dec(x_731);
x_734 = lean_box(x_733);
x_735 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_7);
return x_735;
}
}
case 1:
{
lean_object* x_736; lean_object* x_737; 
x_736 = lean_ctor_get(x_1, 0);
lean_inc(x_736);
lean_dec(x_1);
x_737 = lean_ctor_get(x_2, 0);
lean_inc(x_737);
lean_dec(x_2);
x_1 = x_736;
x_2 = x_737;
goto _start;
}
case 2:
{
lean_object* x_739; lean_object* x_740; uint8_t x_741; 
x_739 = l_Lean_Level_getLevelOffset(x_1);
x_740 = l_Lean_Level_getLevelOffset(x_2);
x_741 = lean_level_eq(x_739, x_740);
lean_dec(x_740);
lean_dec(x_739);
if (x_741 == 0)
{
lean_object* x_742; uint8_t x_1071; lean_object* x_1072; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; uint8_t x_1088; 
x_1085 = lean_st_ref_get(x_6, x_7);
x_1086 = lean_ctor_get(x_1085, 0);
lean_inc(x_1086);
x_1087 = lean_ctor_get(x_1086, 3);
lean_inc(x_1087);
lean_dec(x_1086);
x_1088 = lean_ctor_get_uint8(x_1087, sizeof(void*)*1);
lean_dec(x_1087);
if (x_1088 == 0)
{
lean_object* x_1089; uint8_t x_1090; 
x_1089 = lean_ctor_get(x_1085, 1);
lean_inc(x_1089);
lean_dec(x_1085);
x_1090 = 0;
x_1071 = x_1090;
x_1072 = x_1089;
goto block_1084;
}
else
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; uint8_t x_1096; 
x_1091 = lean_ctor_get(x_1085, 1);
lean_inc(x_1091);
lean_dec(x_1085);
x_1092 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_1093 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1092, x_3, x_4, x_5, x_6, x_1091);
x_1094 = lean_ctor_get(x_1093, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1093, 1);
lean_inc(x_1095);
lean_dec(x_1093);
x_1096 = lean_unbox(x_1094);
lean_dec(x_1094);
x_1071 = x_1096;
x_1072 = x_1095;
goto block_1084;
}
block_1070:
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; 
lean_inc(x_1);
x_743 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_742);
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_746 = l_Lean_Level_normalize(x_744);
lean_dec(x_744);
lean_inc(x_2);
x_747 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_2, x_3, x_4, x_5, x_6, x_745);
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_747, 1);
lean_inc(x_749);
lean_dec(x_747);
x_750 = l_Lean_Level_normalize(x_748);
lean_dec(x_748);
x_751 = lean_level_eq(x_1, x_746);
if (x_751 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_746;
x_2 = x_750;
x_7 = x_749;
goto _start;
}
else
{
uint8_t x_753; 
x_753 = lean_level_eq(x_2, x_750);
if (x_753 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_746;
x_2 = x_750;
x_7 = x_749;
goto _start;
}
else
{
lean_object* x_755; 
lean_dec(x_750);
lean_dec(x_746);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_755 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_749);
if (lean_obj_tag(x_755) == 0)
{
uint8_t x_756; 
x_756 = !lean_is_exclusive(x_755);
if (x_756 == 0)
{
lean_object* x_757; lean_object* x_758; uint8_t x_759; uint8_t x_760; uint8_t x_761; 
x_757 = lean_ctor_get(x_755, 0);
x_758 = lean_ctor_get(x_755, 1);
x_759 = 2;
x_760 = lean_unbox(x_757);
x_761 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_760, x_759);
if (x_761 == 0)
{
uint8_t x_762; uint8_t x_763; uint8_t x_764; lean_object* x_765; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_762 = 1;
x_763 = lean_unbox(x_757);
lean_dec(x_757);
x_764 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_763, x_762);
x_765 = lean_box(x_764);
lean_ctor_set(x_755, 0, x_765);
return x_755;
}
else
{
lean_object* x_766; 
lean_free_object(x_755);
lean_dec(x_757);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_766 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_758);
if (lean_obj_tag(x_766) == 0)
{
uint8_t x_767; 
x_767 = !lean_is_exclusive(x_766);
if (x_767 == 0)
{
lean_object* x_768; lean_object* x_769; uint8_t x_770; uint8_t x_771; 
x_768 = lean_ctor_get(x_766, 0);
x_769 = lean_ctor_get(x_766, 1);
x_770 = lean_unbox(x_768);
x_771 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_770, x_759);
if (x_771 == 0)
{
uint8_t x_772; uint8_t x_773; uint8_t x_774; lean_object* x_775; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_772 = 1;
x_773 = lean_unbox(x_768);
lean_dec(x_768);
x_774 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_773, x_772);
x_775 = lean_box(x_774);
lean_ctor_set(x_766, 0, x_775);
return x_766;
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; uint8_t x_779; 
lean_free_object(x_766);
lean_dec(x_768);
x_776 = lean_st_ref_get(x_6, x_769);
x_777 = lean_ctor_get(x_776, 1);
lean_inc(x_777);
lean_dec(x_776);
x_778 = lean_st_ref_get(x_4, x_777);
x_779 = !lean_is_exclusive(x_778);
if (x_779 == 0)
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; uint8_t x_783; 
x_780 = lean_ctor_get(x_778, 0);
x_781 = lean_ctor_get(x_778, 1);
x_782 = lean_ctor_get(x_780, 0);
lean_inc(x_782);
lean_dec(x_780);
lean_inc(x_782);
x_783 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_782, x_1);
if (x_783 == 0)
{
uint8_t x_784; 
x_784 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_782, x_2);
if (x_784 == 0)
{
lean_object* x_785; lean_object* x_815; uint8_t x_816; 
x_815 = lean_ctor_get(x_3, 0);
lean_inc(x_815);
x_816 = lean_ctor_get_uint8(x_815, 4);
lean_dec(x_815);
if (x_816 == 0)
{
uint8_t x_817; lean_object* x_818; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_817 = 0;
x_818 = lean_box(x_817);
lean_ctor_set(x_778, 0, x_818);
return x_778;
}
else
{
uint8_t x_819; 
x_819 = l_Lean_Level_isMVar(x_1);
if (x_819 == 0)
{
uint8_t x_820; 
x_820 = l_Lean_Level_isMVar(x_2);
if (x_820 == 0)
{
uint8_t x_821; lean_object* x_822; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_821 = 0;
x_822 = lean_box(x_821);
lean_ctor_set(x_778, 0, x_822);
return x_778;
}
else
{
lean_object* x_823; 
lean_free_object(x_778);
x_823 = lean_box(0);
x_785 = x_823;
goto block_814;
}
}
else
{
lean_object* x_824; 
lean_free_object(x_778);
x_824 = lean_box(0);
x_785 = x_824;
goto block_814;
}
}
block_814:
{
uint8_t x_786; lean_object* x_787; lean_object* x_802; lean_object* x_803; lean_object* x_804; uint8_t x_805; 
lean_dec(x_785);
x_802 = lean_st_ref_get(x_6, x_781);
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_803, 3);
lean_inc(x_804);
lean_dec(x_803);
x_805 = lean_ctor_get_uint8(x_804, sizeof(void*)*1);
lean_dec(x_804);
if (x_805 == 0)
{
lean_object* x_806; uint8_t x_807; 
x_806 = lean_ctor_get(x_802, 1);
lean_inc(x_806);
lean_dec(x_802);
x_807 = 0;
x_786 = x_807;
x_787 = x_806;
goto block_801;
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; uint8_t x_813; 
x_808 = lean_ctor_get(x_802, 1);
lean_inc(x_808);
lean_dec(x_802);
x_809 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_810 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_809, x_3, x_4, x_5, x_6, x_808);
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_810, 1);
lean_inc(x_812);
lean_dec(x_810);
x_813 = lean_unbox(x_811);
lean_dec(x_811);
x_786 = x_813;
x_787 = x_812;
goto block_801;
}
block_801:
{
if (x_786 == 0)
{
lean_object* x_788; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_788 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_787);
return x_788;
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
x_789 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_789, 0, x_1);
x_790 = l_Lean_KernelException_toMessageData___closed__15;
x_791 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_791, 0, x_790);
lean_ctor_set(x_791, 1, x_789);
x_792 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_793 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_793, 0, x_791);
lean_ctor_set(x_793, 1, x_792);
x_794 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_794, 0, x_2);
x_795 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_795, 0, x_793);
lean_ctor_set(x_795, 1, x_794);
x_796 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_796, 0, x_795);
lean_ctor_set(x_796, 1, x_790);
x_797 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_798 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_797, x_796, x_3, x_4, x_5, x_6, x_787);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_799 = lean_ctor_get(x_798, 1);
lean_inc(x_799);
lean_dec(x_798);
x_800 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_799);
return x_800;
}
}
}
}
else
{
lean_object* x_825; uint8_t x_826; 
lean_free_object(x_778);
x_825 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_781);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_826 = !lean_is_exclusive(x_825);
if (x_826 == 0)
{
lean_object* x_827; uint8_t x_828; lean_object* x_829; 
x_827 = lean_ctor_get(x_825, 0);
lean_dec(x_827);
x_828 = 1;
x_829 = lean_box(x_828);
lean_ctor_set(x_825, 0, x_829);
return x_825;
}
else
{
lean_object* x_830; uint8_t x_831; lean_object* x_832; lean_object* x_833; 
x_830 = lean_ctor_get(x_825, 1);
lean_inc(x_830);
lean_dec(x_825);
x_831 = 1;
x_832 = lean_box(x_831);
x_833 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_833, 0, x_832);
lean_ctor_set(x_833, 1, x_830);
return x_833;
}
}
}
else
{
lean_object* x_834; uint8_t x_835; 
lean_dec(x_782);
lean_free_object(x_778);
x_834 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_781);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_835 = !lean_is_exclusive(x_834);
if (x_835 == 0)
{
lean_object* x_836; uint8_t x_837; lean_object* x_838; 
x_836 = lean_ctor_get(x_834, 0);
lean_dec(x_836);
x_837 = 1;
x_838 = lean_box(x_837);
lean_ctor_set(x_834, 0, x_838);
return x_834;
}
else
{
lean_object* x_839; uint8_t x_840; lean_object* x_841; lean_object* x_842; 
x_839 = lean_ctor_get(x_834, 1);
lean_inc(x_839);
lean_dec(x_834);
x_840 = 1;
x_841 = lean_box(x_840);
x_842 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_842, 0, x_841);
lean_ctor_set(x_842, 1, x_839);
return x_842;
}
}
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; uint8_t x_846; 
x_843 = lean_ctor_get(x_778, 0);
x_844 = lean_ctor_get(x_778, 1);
lean_inc(x_844);
lean_inc(x_843);
lean_dec(x_778);
x_845 = lean_ctor_get(x_843, 0);
lean_inc(x_845);
lean_dec(x_843);
lean_inc(x_845);
x_846 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_845, x_1);
if (x_846 == 0)
{
uint8_t x_847; 
x_847 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_845, x_2);
if (x_847 == 0)
{
lean_object* x_848; lean_object* x_878; uint8_t x_879; 
x_878 = lean_ctor_get(x_3, 0);
lean_inc(x_878);
x_879 = lean_ctor_get_uint8(x_878, 4);
lean_dec(x_878);
if (x_879 == 0)
{
uint8_t x_880; lean_object* x_881; lean_object* x_882; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_880 = 0;
x_881 = lean_box(x_880);
x_882 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_882, 0, x_881);
lean_ctor_set(x_882, 1, x_844);
return x_882;
}
else
{
uint8_t x_883; 
x_883 = l_Lean_Level_isMVar(x_1);
if (x_883 == 0)
{
uint8_t x_884; 
x_884 = l_Lean_Level_isMVar(x_2);
if (x_884 == 0)
{
uint8_t x_885; lean_object* x_886; lean_object* x_887; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_885 = 0;
x_886 = lean_box(x_885);
x_887 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_887, 0, x_886);
lean_ctor_set(x_887, 1, x_844);
return x_887;
}
else
{
lean_object* x_888; 
x_888 = lean_box(0);
x_848 = x_888;
goto block_877;
}
}
else
{
lean_object* x_889; 
x_889 = lean_box(0);
x_848 = x_889;
goto block_877;
}
}
block_877:
{
uint8_t x_849; lean_object* x_850; lean_object* x_865; lean_object* x_866; lean_object* x_867; uint8_t x_868; 
lean_dec(x_848);
x_865 = lean_st_ref_get(x_6, x_844);
x_866 = lean_ctor_get(x_865, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_866, 3);
lean_inc(x_867);
lean_dec(x_866);
x_868 = lean_ctor_get_uint8(x_867, sizeof(void*)*1);
lean_dec(x_867);
if (x_868 == 0)
{
lean_object* x_869; uint8_t x_870; 
x_869 = lean_ctor_get(x_865, 1);
lean_inc(x_869);
lean_dec(x_865);
x_870 = 0;
x_849 = x_870;
x_850 = x_869;
goto block_864;
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; uint8_t x_876; 
x_871 = lean_ctor_get(x_865, 1);
lean_inc(x_871);
lean_dec(x_865);
x_872 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_873 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_872, x_3, x_4, x_5, x_6, x_871);
x_874 = lean_ctor_get(x_873, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_873, 1);
lean_inc(x_875);
lean_dec(x_873);
x_876 = lean_unbox(x_874);
lean_dec(x_874);
x_849 = x_876;
x_850 = x_875;
goto block_864;
}
block_864:
{
if (x_849 == 0)
{
lean_object* x_851; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_851 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_850);
return x_851;
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_852 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_852, 0, x_1);
x_853 = l_Lean_KernelException_toMessageData___closed__15;
x_854 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_854, 0, x_853);
lean_ctor_set(x_854, 1, x_852);
x_855 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_856 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_856, 0, x_854);
lean_ctor_set(x_856, 1, x_855);
x_857 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_857, 0, x_2);
x_858 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_858, 0, x_856);
lean_ctor_set(x_858, 1, x_857);
x_859 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_859, 0, x_858);
lean_ctor_set(x_859, 1, x_853);
x_860 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_861 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_860, x_859, x_3, x_4, x_5, x_6, x_850);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_862 = lean_ctor_get(x_861, 1);
lean_inc(x_862);
lean_dec(x_861);
x_863 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_862);
return x_863;
}
}
}
}
else
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; uint8_t x_893; lean_object* x_894; lean_object* x_895; 
x_890 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_844);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_891 = lean_ctor_get(x_890, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 lean_ctor_release(x_890, 1);
 x_892 = x_890;
} else {
 lean_dec_ref(x_890);
 x_892 = lean_box(0);
}
x_893 = 1;
x_894 = lean_box(x_893);
if (lean_is_scalar(x_892)) {
 x_895 = lean_alloc_ctor(0, 2, 0);
} else {
 x_895 = x_892;
}
lean_ctor_set(x_895, 0, x_894);
lean_ctor_set(x_895, 1, x_891);
return x_895;
}
}
else
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; uint8_t x_899; lean_object* x_900; lean_object* x_901; 
lean_dec(x_845);
x_896 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_844);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_897 = lean_ctor_get(x_896, 1);
lean_inc(x_897);
if (lean_is_exclusive(x_896)) {
 lean_ctor_release(x_896, 0);
 lean_ctor_release(x_896, 1);
 x_898 = x_896;
} else {
 lean_dec_ref(x_896);
 x_898 = lean_box(0);
}
x_899 = 1;
x_900 = lean_box(x_899);
if (lean_is_scalar(x_898)) {
 x_901 = lean_alloc_ctor(0, 2, 0);
} else {
 x_901 = x_898;
}
lean_ctor_set(x_901, 0, x_900);
lean_ctor_set(x_901, 1, x_897);
return x_901;
}
}
}
}
else
{
lean_object* x_902; lean_object* x_903; uint8_t x_904; uint8_t x_905; 
x_902 = lean_ctor_get(x_766, 0);
x_903 = lean_ctor_get(x_766, 1);
lean_inc(x_903);
lean_inc(x_902);
lean_dec(x_766);
x_904 = lean_unbox(x_902);
x_905 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_904, x_759);
if (x_905 == 0)
{
uint8_t x_906; uint8_t x_907; uint8_t x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_906 = 1;
x_907 = lean_unbox(x_902);
lean_dec(x_902);
x_908 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_907, x_906);
x_909 = lean_box(x_908);
x_910 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_910, 0, x_909);
lean_ctor_set(x_910, 1, x_903);
return x_910;
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; uint8_t x_918; 
lean_dec(x_902);
x_911 = lean_st_ref_get(x_6, x_903);
x_912 = lean_ctor_get(x_911, 1);
lean_inc(x_912);
lean_dec(x_911);
x_913 = lean_st_ref_get(x_4, x_912);
x_914 = lean_ctor_get(x_913, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_913, 1);
lean_inc(x_915);
if (lean_is_exclusive(x_913)) {
 lean_ctor_release(x_913, 0);
 lean_ctor_release(x_913, 1);
 x_916 = x_913;
} else {
 lean_dec_ref(x_913);
 x_916 = lean_box(0);
}
x_917 = lean_ctor_get(x_914, 0);
lean_inc(x_917);
lean_dec(x_914);
lean_inc(x_917);
x_918 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_917, x_1);
if (x_918 == 0)
{
uint8_t x_919; 
x_919 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_917, x_2);
if (x_919 == 0)
{
lean_object* x_920; lean_object* x_950; uint8_t x_951; 
x_950 = lean_ctor_get(x_3, 0);
lean_inc(x_950);
x_951 = lean_ctor_get_uint8(x_950, 4);
lean_dec(x_950);
if (x_951 == 0)
{
uint8_t x_952; lean_object* x_953; lean_object* x_954; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_952 = 0;
x_953 = lean_box(x_952);
if (lean_is_scalar(x_916)) {
 x_954 = lean_alloc_ctor(0, 2, 0);
} else {
 x_954 = x_916;
}
lean_ctor_set(x_954, 0, x_953);
lean_ctor_set(x_954, 1, x_915);
return x_954;
}
else
{
uint8_t x_955; 
x_955 = l_Lean_Level_isMVar(x_1);
if (x_955 == 0)
{
uint8_t x_956; 
x_956 = l_Lean_Level_isMVar(x_2);
if (x_956 == 0)
{
uint8_t x_957; lean_object* x_958; lean_object* x_959; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_957 = 0;
x_958 = lean_box(x_957);
if (lean_is_scalar(x_916)) {
 x_959 = lean_alloc_ctor(0, 2, 0);
} else {
 x_959 = x_916;
}
lean_ctor_set(x_959, 0, x_958);
lean_ctor_set(x_959, 1, x_915);
return x_959;
}
else
{
lean_object* x_960; 
lean_dec(x_916);
x_960 = lean_box(0);
x_920 = x_960;
goto block_949;
}
}
else
{
lean_object* x_961; 
lean_dec(x_916);
x_961 = lean_box(0);
x_920 = x_961;
goto block_949;
}
}
block_949:
{
uint8_t x_921; lean_object* x_922; lean_object* x_937; lean_object* x_938; lean_object* x_939; uint8_t x_940; 
lean_dec(x_920);
x_937 = lean_st_ref_get(x_6, x_915);
x_938 = lean_ctor_get(x_937, 0);
lean_inc(x_938);
x_939 = lean_ctor_get(x_938, 3);
lean_inc(x_939);
lean_dec(x_938);
x_940 = lean_ctor_get_uint8(x_939, sizeof(void*)*1);
lean_dec(x_939);
if (x_940 == 0)
{
lean_object* x_941; uint8_t x_942; 
x_941 = lean_ctor_get(x_937, 1);
lean_inc(x_941);
lean_dec(x_937);
x_942 = 0;
x_921 = x_942;
x_922 = x_941;
goto block_936;
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; uint8_t x_948; 
x_943 = lean_ctor_get(x_937, 1);
lean_inc(x_943);
lean_dec(x_937);
x_944 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_945 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_944, x_3, x_4, x_5, x_6, x_943);
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
lean_dec(x_945);
x_948 = lean_unbox(x_946);
lean_dec(x_946);
x_921 = x_948;
x_922 = x_947;
goto block_936;
}
block_936:
{
if (x_921 == 0)
{
lean_object* x_923; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_923 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_922);
return x_923;
}
else
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_924 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_924, 0, x_1);
x_925 = l_Lean_KernelException_toMessageData___closed__15;
x_926 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_926, 0, x_925);
lean_ctor_set(x_926, 1, x_924);
x_927 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_928 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_928, 0, x_926);
lean_ctor_set(x_928, 1, x_927);
x_929 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_929, 0, x_2);
x_930 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_930, 0, x_928);
lean_ctor_set(x_930, 1, x_929);
x_931 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_931, 0, x_930);
lean_ctor_set(x_931, 1, x_925);
x_932 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_933 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_932, x_931, x_3, x_4, x_5, x_6, x_922);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_934 = lean_ctor_get(x_933, 1);
lean_inc(x_934);
lean_dec(x_933);
x_935 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_934);
return x_935;
}
}
}
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; uint8_t x_965; lean_object* x_966; lean_object* x_967; 
lean_dec(x_916);
x_962 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_915);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_963 = lean_ctor_get(x_962, 1);
lean_inc(x_963);
if (lean_is_exclusive(x_962)) {
 lean_ctor_release(x_962, 0);
 lean_ctor_release(x_962, 1);
 x_964 = x_962;
} else {
 lean_dec_ref(x_962);
 x_964 = lean_box(0);
}
x_965 = 1;
x_966 = lean_box(x_965);
if (lean_is_scalar(x_964)) {
 x_967 = lean_alloc_ctor(0, 2, 0);
} else {
 x_967 = x_964;
}
lean_ctor_set(x_967, 0, x_966);
lean_ctor_set(x_967, 1, x_963);
return x_967;
}
}
else
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; uint8_t x_971; lean_object* x_972; lean_object* x_973; 
lean_dec(x_917);
lean_dec(x_916);
x_968 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_915);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_969 = lean_ctor_get(x_968, 1);
lean_inc(x_969);
if (lean_is_exclusive(x_968)) {
 lean_ctor_release(x_968, 0);
 lean_ctor_release(x_968, 1);
 x_970 = x_968;
} else {
 lean_dec_ref(x_968);
 x_970 = lean_box(0);
}
x_971 = 1;
x_972 = lean_box(x_971);
if (lean_is_scalar(x_970)) {
 x_973 = lean_alloc_ctor(0, 2, 0);
} else {
 x_973 = x_970;
}
lean_ctor_set(x_973, 0, x_972);
lean_ctor_set(x_973, 1, x_969);
return x_973;
}
}
}
}
else
{
uint8_t x_974; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_974 = !lean_is_exclusive(x_766);
if (x_974 == 0)
{
return x_766;
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; 
x_975 = lean_ctor_get(x_766, 0);
x_976 = lean_ctor_get(x_766, 1);
lean_inc(x_976);
lean_inc(x_975);
lean_dec(x_766);
x_977 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_977, 0, x_975);
lean_ctor_set(x_977, 1, x_976);
return x_977;
}
}
}
}
else
{
lean_object* x_978; lean_object* x_979; uint8_t x_980; uint8_t x_981; uint8_t x_982; 
x_978 = lean_ctor_get(x_755, 0);
x_979 = lean_ctor_get(x_755, 1);
lean_inc(x_979);
lean_inc(x_978);
lean_dec(x_755);
x_980 = 2;
x_981 = lean_unbox(x_978);
x_982 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_981, x_980);
if (x_982 == 0)
{
uint8_t x_983; uint8_t x_984; uint8_t x_985; lean_object* x_986; lean_object* x_987; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_983 = 1;
x_984 = lean_unbox(x_978);
lean_dec(x_978);
x_985 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_984, x_983);
x_986 = lean_box(x_985);
x_987 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_987, 0, x_986);
lean_ctor_set(x_987, 1, x_979);
return x_987;
}
else
{
lean_object* x_988; 
lean_dec(x_978);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_988 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_979);
if (lean_obj_tag(x_988) == 0)
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; uint8_t x_992; uint8_t x_993; 
x_989 = lean_ctor_get(x_988, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_988, 1);
lean_inc(x_990);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 lean_ctor_release(x_988, 1);
 x_991 = x_988;
} else {
 lean_dec_ref(x_988);
 x_991 = lean_box(0);
}
x_992 = lean_unbox(x_989);
x_993 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_992, x_980);
if (x_993 == 0)
{
uint8_t x_994; uint8_t x_995; uint8_t x_996; lean_object* x_997; lean_object* x_998; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_994 = 1;
x_995 = lean_unbox(x_989);
lean_dec(x_989);
x_996 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_995, x_994);
x_997 = lean_box(x_996);
if (lean_is_scalar(x_991)) {
 x_998 = lean_alloc_ctor(0, 2, 0);
} else {
 x_998 = x_991;
}
lean_ctor_set(x_998, 0, x_997);
lean_ctor_set(x_998, 1, x_990);
return x_998;
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; uint8_t x_1006; 
lean_dec(x_991);
lean_dec(x_989);
x_999 = lean_st_ref_get(x_6, x_990);
x_1000 = lean_ctor_get(x_999, 1);
lean_inc(x_1000);
lean_dec(x_999);
x_1001 = lean_st_ref_get(x_4, x_1000);
x_1002 = lean_ctor_get(x_1001, 0);
lean_inc(x_1002);
x_1003 = lean_ctor_get(x_1001, 1);
lean_inc(x_1003);
if (lean_is_exclusive(x_1001)) {
 lean_ctor_release(x_1001, 0);
 lean_ctor_release(x_1001, 1);
 x_1004 = x_1001;
} else {
 lean_dec_ref(x_1001);
 x_1004 = lean_box(0);
}
x_1005 = lean_ctor_get(x_1002, 0);
lean_inc(x_1005);
lean_dec(x_1002);
lean_inc(x_1005);
x_1006 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1005, x_1);
if (x_1006 == 0)
{
uint8_t x_1007; 
x_1007 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1005, x_2);
if (x_1007 == 0)
{
lean_object* x_1008; lean_object* x_1038; uint8_t x_1039; 
x_1038 = lean_ctor_get(x_3, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get_uint8(x_1038, 4);
lean_dec(x_1038);
if (x_1039 == 0)
{
uint8_t x_1040; lean_object* x_1041; lean_object* x_1042; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1040 = 0;
x_1041 = lean_box(x_1040);
if (lean_is_scalar(x_1004)) {
 x_1042 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1042 = x_1004;
}
lean_ctor_set(x_1042, 0, x_1041);
lean_ctor_set(x_1042, 1, x_1003);
return x_1042;
}
else
{
uint8_t x_1043; 
x_1043 = l_Lean_Level_isMVar(x_1);
if (x_1043 == 0)
{
uint8_t x_1044; 
x_1044 = l_Lean_Level_isMVar(x_2);
if (x_1044 == 0)
{
uint8_t x_1045; lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1045 = 0;
x_1046 = lean_box(x_1045);
if (lean_is_scalar(x_1004)) {
 x_1047 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1047 = x_1004;
}
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_1003);
return x_1047;
}
else
{
lean_object* x_1048; 
lean_dec(x_1004);
x_1048 = lean_box(0);
x_1008 = x_1048;
goto block_1037;
}
}
else
{
lean_object* x_1049; 
lean_dec(x_1004);
x_1049 = lean_box(0);
x_1008 = x_1049;
goto block_1037;
}
}
block_1037:
{
uint8_t x_1009; lean_object* x_1010; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; uint8_t x_1028; 
lean_dec(x_1008);
x_1025 = lean_st_ref_get(x_6, x_1003);
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1026, 3);
lean_inc(x_1027);
lean_dec(x_1026);
x_1028 = lean_ctor_get_uint8(x_1027, sizeof(void*)*1);
lean_dec(x_1027);
if (x_1028 == 0)
{
lean_object* x_1029; uint8_t x_1030; 
x_1029 = lean_ctor_get(x_1025, 1);
lean_inc(x_1029);
lean_dec(x_1025);
x_1030 = 0;
x_1009 = x_1030;
x_1010 = x_1029;
goto block_1024;
}
else
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; uint8_t x_1036; 
x_1031 = lean_ctor_get(x_1025, 1);
lean_inc(x_1031);
lean_dec(x_1025);
x_1032 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1033 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1032, x_3, x_4, x_5, x_6, x_1031);
x_1034 = lean_ctor_get(x_1033, 0);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_1033, 1);
lean_inc(x_1035);
lean_dec(x_1033);
x_1036 = lean_unbox(x_1034);
lean_dec(x_1034);
x_1009 = x_1036;
x_1010 = x_1035;
goto block_1024;
}
block_1024:
{
if (x_1009 == 0)
{
lean_object* x_1011; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1011 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1010);
return x_1011;
}
else
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1012 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1012, 0, x_1);
x_1013 = l_Lean_KernelException_toMessageData___closed__15;
x_1014 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1014, 0, x_1013);
lean_ctor_set(x_1014, 1, x_1012);
x_1015 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1016 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1016, 0, x_1014);
lean_ctor_set(x_1016, 1, x_1015);
x_1017 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1017, 0, x_2);
x_1018 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1018, 0, x_1016);
lean_ctor_set(x_1018, 1, x_1017);
x_1019 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1019, 0, x_1018);
lean_ctor_set(x_1019, 1, x_1013);
x_1020 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1021 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1020, x_1019, x_3, x_4, x_5, x_6, x_1010);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1022 = lean_ctor_get(x_1021, 1);
lean_inc(x_1022);
lean_dec(x_1021);
x_1023 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1022);
return x_1023;
}
}
}
}
else
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; uint8_t x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_1004);
x_1050 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1003);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1051 = lean_ctor_get(x_1050, 1);
lean_inc(x_1051);
if (lean_is_exclusive(x_1050)) {
 lean_ctor_release(x_1050, 0);
 lean_ctor_release(x_1050, 1);
 x_1052 = x_1050;
} else {
 lean_dec_ref(x_1050);
 x_1052 = lean_box(0);
}
x_1053 = 1;
x_1054 = lean_box(x_1053);
if (lean_is_scalar(x_1052)) {
 x_1055 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1055 = x_1052;
}
lean_ctor_set(x_1055, 0, x_1054);
lean_ctor_set(x_1055, 1, x_1051);
return x_1055;
}
}
else
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; uint8_t x_1059; lean_object* x_1060; lean_object* x_1061; 
lean_dec(x_1005);
lean_dec(x_1004);
x_1056 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1003);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1057 = lean_ctor_get(x_1056, 1);
lean_inc(x_1057);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 lean_ctor_release(x_1056, 1);
 x_1058 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1058 = lean_box(0);
}
x_1059 = 1;
x_1060 = lean_box(x_1059);
if (lean_is_scalar(x_1058)) {
 x_1061 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1061 = x_1058;
}
lean_ctor_set(x_1061, 0, x_1060);
lean_ctor_set(x_1061, 1, x_1057);
return x_1061;
}
}
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1062 = lean_ctor_get(x_988, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_988, 1);
lean_inc(x_1063);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 lean_ctor_release(x_988, 1);
 x_1064 = x_988;
} else {
 lean_dec_ref(x_988);
 x_1064 = lean_box(0);
}
if (lean_is_scalar(x_1064)) {
 x_1065 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1065 = x_1064;
}
lean_ctor_set(x_1065, 0, x_1062);
lean_ctor_set(x_1065, 1, x_1063);
return x_1065;
}
}
}
}
else
{
uint8_t x_1066; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1066 = !lean_is_exclusive(x_755);
if (x_1066 == 0)
{
return x_755;
}
else
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
x_1067 = lean_ctor_get(x_755, 0);
x_1068 = lean_ctor_get(x_755, 1);
lean_inc(x_1068);
lean_inc(x_1067);
lean_dec(x_755);
x_1069 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1069, 0, x_1067);
lean_ctor_set(x_1069, 1, x_1068);
return x_1069;
}
}
}
}
}
block_1084:
{
if (x_1071 == 0)
{
x_742 = x_1072;
goto block_1070;
}
else
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
lean_inc(x_1);
x_1073 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1073, 0, x_1);
x_1074 = l_Lean_KernelException_toMessageData___closed__15;
x_1075 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1075, 0, x_1074);
lean_ctor_set(x_1075, 1, x_1073);
x_1076 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1077 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1077, 0, x_1075);
lean_ctor_set(x_1077, 1, x_1076);
lean_inc(x_2);
x_1078 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1078, 0, x_2);
x_1079 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1079, 0, x_1077);
lean_ctor_set(x_1079, 1, x_1078);
x_1080 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1080, 0, x_1079);
lean_ctor_set(x_1080, 1, x_1074);
x_1081 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_1082 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1081, x_1080, x_3, x_4, x_5, x_6, x_1072);
x_1083 = lean_ctor_get(x_1082, 1);
lean_inc(x_1083);
lean_dec(x_1082);
x_742 = x_1083;
goto block_1070;
}
}
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; uint8_t x_1100; lean_object* x_1101; lean_object* x_1102; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1097 = lean_unsigned_to_nat(0u);
x_1098 = l_Lean_Level_getOffsetAux(x_1, x_1097);
lean_dec(x_1);
x_1099 = l_Lean_Level_getOffsetAux(x_2, x_1097);
lean_dec(x_2);
x_1100 = lean_nat_dec_eq(x_1098, x_1099);
lean_dec(x_1099);
lean_dec(x_1098);
x_1101 = lean_box(x_1100);
x_1102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1102, 0, x_1101);
lean_ctor_set(x_1102, 1, x_7);
return x_1102;
}
}
case 3:
{
lean_object* x_1103; lean_object* x_1104; uint8_t x_1105; 
x_1103 = l_Lean_Level_getLevelOffset(x_1);
x_1104 = l_Lean_Level_getLevelOffset(x_2);
x_1105 = lean_level_eq(x_1103, x_1104);
lean_dec(x_1104);
lean_dec(x_1103);
if (x_1105 == 0)
{
lean_object* x_1106; uint8_t x_1435; lean_object* x_1436; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; uint8_t x_1452; 
x_1449 = lean_st_ref_get(x_6, x_7);
x_1450 = lean_ctor_get(x_1449, 0);
lean_inc(x_1450);
x_1451 = lean_ctor_get(x_1450, 3);
lean_inc(x_1451);
lean_dec(x_1450);
x_1452 = lean_ctor_get_uint8(x_1451, sizeof(void*)*1);
lean_dec(x_1451);
if (x_1452 == 0)
{
lean_object* x_1453; uint8_t x_1454; 
x_1453 = lean_ctor_get(x_1449, 1);
lean_inc(x_1453);
lean_dec(x_1449);
x_1454 = 0;
x_1435 = x_1454;
x_1436 = x_1453;
goto block_1448;
}
else
{
lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; uint8_t x_1460; 
x_1455 = lean_ctor_get(x_1449, 1);
lean_inc(x_1455);
lean_dec(x_1449);
x_1456 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_1457 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1456, x_3, x_4, x_5, x_6, x_1455);
x_1458 = lean_ctor_get(x_1457, 0);
lean_inc(x_1458);
x_1459 = lean_ctor_get(x_1457, 1);
lean_inc(x_1459);
lean_dec(x_1457);
x_1460 = lean_unbox(x_1458);
lean_dec(x_1458);
x_1435 = x_1460;
x_1436 = x_1459;
goto block_1448;
}
block_1434:
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; uint8_t x_1115; 
lean_inc(x_1);
x_1107 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_1106);
x_1108 = lean_ctor_get(x_1107, 0);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_1107, 1);
lean_inc(x_1109);
lean_dec(x_1107);
x_1110 = l_Lean_Level_normalize(x_1108);
lean_dec(x_1108);
lean_inc(x_2);
x_1111 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_2, x_3, x_4, x_5, x_6, x_1109);
x_1112 = lean_ctor_get(x_1111, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1111, 1);
lean_inc(x_1113);
lean_dec(x_1111);
x_1114 = l_Lean_Level_normalize(x_1112);
lean_dec(x_1112);
x_1115 = lean_level_eq(x_1, x_1110);
if (x_1115 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_1110;
x_2 = x_1114;
x_7 = x_1113;
goto _start;
}
else
{
uint8_t x_1117; 
x_1117 = lean_level_eq(x_2, x_1114);
if (x_1117 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_1110;
x_2 = x_1114;
x_7 = x_1113;
goto _start;
}
else
{
lean_object* x_1119; 
lean_dec(x_1114);
lean_dec(x_1110);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_1119 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_1113);
if (lean_obj_tag(x_1119) == 0)
{
uint8_t x_1120; 
x_1120 = !lean_is_exclusive(x_1119);
if (x_1120 == 0)
{
lean_object* x_1121; lean_object* x_1122; uint8_t x_1123; uint8_t x_1124; uint8_t x_1125; 
x_1121 = lean_ctor_get(x_1119, 0);
x_1122 = lean_ctor_get(x_1119, 1);
x_1123 = 2;
x_1124 = lean_unbox(x_1121);
x_1125 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1124, x_1123);
if (x_1125 == 0)
{
uint8_t x_1126; uint8_t x_1127; uint8_t x_1128; lean_object* x_1129; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1126 = 1;
x_1127 = lean_unbox(x_1121);
lean_dec(x_1121);
x_1128 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1127, x_1126);
x_1129 = lean_box(x_1128);
lean_ctor_set(x_1119, 0, x_1129);
return x_1119;
}
else
{
lean_object* x_1130; 
lean_free_object(x_1119);
lean_dec(x_1121);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_1130 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_1122);
if (lean_obj_tag(x_1130) == 0)
{
uint8_t x_1131; 
x_1131 = !lean_is_exclusive(x_1130);
if (x_1131 == 0)
{
lean_object* x_1132; lean_object* x_1133; uint8_t x_1134; uint8_t x_1135; 
x_1132 = lean_ctor_get(x_1130, 0);
x_1133 = lean_ctor_get(x_1130, 1);
x_1134 = lean_unbox(x_1132);
x_1135 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1134, x_1123);
if (x_1135 == 0)
{
uint8_t x_1136; uint8_t x_1137; uint8_t x_1138; lean_object* x_1139; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1136 = 1;
x_1137 = lean_unbox(x_1132);
lean_dec(x_1132);
x_1138 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1137, x_1136);
x_1139 = lean_box(x_1138);
lean_ctor_set(x_1130, 0, x_1139);
return x_1130;
}
else
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; uint8_t x_1143; 
lean_free_object(x_1130);
lean_dec(x_1132);
x_1140 = lean_st_ref_get(x_6, x_1133);
x_1141 = lean_ctor_get(x_1140, 1);
lean_inc(x_1141);
lean_dec(x_1140);
x_1142 = lean_st_ref_get(x_4, x_1141);
x_1143 = !lean_is_exclusive(x_1142);
if (x_1143 == 0)
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; uint8_t x_1147; 
x_1144 = lean_ctor_get(x_1142, 0);
x_1145 = lean_ctor_get(x_1142, 1);
x_1146 = lean_ctor_get(x_1144, 0);
lean_inc(x_1146);
lean_dec(x_1144);
lean_inc(x_1146);
x_1147 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1146, x_1);
if (x_1147 == 0)
{
uint8_t x_1148; 
x_1148 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1146, x_2);
if (x_1148 == 0)
{
lean_object* x_1149; lean_object* x_1179; uint8_t x_1180; 
x_1179 = lean_ctor_get(x_3, 0);
lean_inc(x_1179);
x_1180 = lean_ctor_get_uint8(x_1179, 4);
lean_dec(x_1179);
if (x_1180 == 0)
{
uint8_t x_1181; lean_object* x_1182; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1181 = 0;
x_1182 = lean_box(x_1181);
lean_ctor_set(x_1142, 0, x_1182);
return x_1142;
}
else
{
uint8_t x_1183; 
x_1183 = l_Lean_Level_isMVar(x_1);
if (x_1183 == 0)
{
uint8_t x_1184; 
x_1184 = l_Lean_Level_isMVar(x_2);
if (x_1184 == 0)
{
uint8_t x_1185; lean_object* x_1186; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1185 = 0;
x_1186 = lean_box(x_1185);
lean_ctor_set(x_1142, 0, x_1186);
return x_1142;
}
else
{
lean_object* x_1187; 
lean_free_object(x_1142);
x_1187 = lean_box(0);
x_1149 = x_1187;
goto block_1178;
}
}
else
{
lean_object* x_1188; 
lean_free_object(x_1142);
x_1188 = lean_box(0);
x_1149 = x_1188;
goto block_1178;
}
}
block_1178:
{
uint8_t x_1150; lean_object* x_1151; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; uint8_t x_1169; 
lean_dec(x_1149);
x_1166 = lean_st_ref_get(x_6, x_1145);
x_1167 = lean_ctor_get(x_1166, 0);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_1167, 3);
lean_inc(x_1168);
lean_dec(x_1167);
x_1169 = lean_ctor_get_uint8(x_1168, sizeof(void*)*1);
lean_dec(x_1168);
if (x_1169 == 0)
{
lean_object* x_1170; uint8_t x_1171; 
x_1170 = lean_ctor_get(x_1166, 1);
lean_inc(x_1170);
lean_dec(x_1166);
x_1171 = 0;
x_1150 = x_1171;
x_1151 = x_1170;
goto block_1165;
}
else
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; uint8_t x_1177; 
x_1172 = lean_ctor_get(x_1166, 1);
lean_inc(x_1172);
lean_dec(x_1166);
x_1173 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1174 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1173, x_3, x_4, x_5, x_6, x_1172);
x_1175 = lean_ctor_get(x_1174, 0);
lean_inc(x_1175);
x_1176 = lean_ctor_get(x_1174, 1);
lean_inc(x_1176);
lean_dec(x_1174);
x_1177 = lean_unbox(x_1175);
lean_dec(x_1175);
x_1150 = x_1177;
x_1151 = x_1176;
goto block_1165;
}
block_1165:
{
if (x_1150 == 0)
{
lean_object* x_1152; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1152 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1151);
return x_1152;
}
else
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1153 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1153, 0, x_1);
x_1154 = l_Lean_KernelException_toMessageData___closed__15;
x_1155 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1155, 0, x_1154);
lean_ctor_set(x_1155, 1, x_1153);
x_1156 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1157 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1157, 0, x_1155);
lean_ctor_set(x_1157, 1, x_1156);
x_1158 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1158, 0, x_2);
x_1159 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1159, 0, x_1157);
lean_ctor_set(x_1159, 1, x_1158);
x_1160 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1160, 0, x_1159);
lean_ctor_set(x_1160, 1, x_1154);
x_1161 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1162 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1161, x_1160, x_3, x_4, x_5, x_6, x_1151);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1163 = lean_ctor_get(x_1162, 1);
lean_inc(x_1163);
lean_dec(x_1162);
x_1164 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1163);
return x_1164;
}
}
}
}
else
{
lean_object* x_1189; uint8_t x_1190; 
lean_free_object(x_1142);
x_1189 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1145);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1190 = !lean_is_exclusive(x_1189);
if (x_1190 == 0)
{
lean_object* x_1191; uint8_t x_1192; lean_object* x_1193; 
x_1191 = lean_ctor_get(x_1189, 0);
lean_dec(x_1191);
x_1192 = 1;
x_1193 = lean_box(x_1192);
lean_ctor_set(x_1189, 0, x_1193);
return x_1189;
}
else
{
lean_object* x_1194; uint8_t x_1195; lean_object* x_1196; lean_object* x_1197; 
x_1194 = lean_ctor_get(x_1189, 1);
lean_inc(x_1194);
lean_dec(x_1189);
x_1195 = 1;
x_1196 = lean_box(x_1195);
x_1197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1197, 0, x_1196);
lean_ctor_set(x_1197, 1, x_1194);
return x_1197;
}
}
}
else
{
lean_object* x_1198; uint8_t x_1199; 
lean_dec(x_1146);
lean_free_object(x_1142);
x_1198 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1145);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1199 = !lean_is_exclusive(x_1198);
if (x_1199 == 0)
{
lean_object* x_1200; uint8_t x_1201; lean_object* x_1202; 
x_1200 = lean_ctor_get(x_1198, 0);
lean_dec(x_1200);
x_1201 = 1;
x_1202 = lean_box(x_1201);
lean_ctor_set(x_1198, 0, x_1202);
return x_1198;
}
else
{
lean_object* x_1203; uint8_t x_1204; lean_object* x_1205; lean_object* x_1206; 
x_1203 = lean_ctor_get(x_1198, 1);
lean_inc(x_1203);
lean_dec(x_1198);
x_1204 = 1;
x_1205 = lean_box(x_1204);
x_1206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1206, 0, x_1205);
lean_ctor_set(x_1206, 1, x_1203);
return x_1206;
}
}
}
else
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; uint8_t x_1210; 
x_1207 = lean_ctor_get(x_1142, 0);
x_1208 = lean_ctor_get(x_1142, 1);
lean_inc(x_1208);
lean_inc(x_1207);
lean_dec(x_1142);
x_1209 = lean_ctor_get(x_1207, 0);
lean_inc(x_1209);
lean_dec(x_1207);
lean_inc(x_1209);
x_1210 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1209, x_1);
if (x_1210 == 0)
{
uint8_t x_1211; 
x_1211 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1209, x_2);
if (x_1211 == 0)
{
lean_object* x_1212; lean_object* x_1242; uint8_t x_1243; 
x_1242 = lean_ctor_get(x_3, 0);
lean_inc(x_1242);
x_1243 = lean_ctor_get_uint8(x_1242, 4);
lean_dec(x_1242);
if (x_1243 == 0)
{
uint8_t x_1244; lean_object* x_1245; lean_object* x_1246; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1244 = 0;
x_1245 = lean_box(x_1244);
x_1246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1246, 0, x_1245);
lean_ctor_set(x_1246, 1, x_1208);
return x_1246;
}
else
{
uint8_t x_1247; 
x_1247 = l_Lean_Level_isMVar(x_1);
if (x_1247 == 0)
{
uint8_t x_1248; 
x_1248 = l_Lean_Level_isMVar(x_2);
if (x_1248 == 0)
{
uint8_t x_1249; lean_object* x_1250; lean_object* x_1251; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1249 = 0;
x_1250 = lean_box(x_1249);
x_1251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1251, 0, x_1250);
lean_ctor_set(x_1251, 1, x_1208);
return x_1251;
}
else
{
lean_object* x_1252; 
x_1252 = lean_box(0);
x_1212 = x_1252;
goto block_1241;
}
}
else
{
lean_object* x_1253; 
x_1253 = lean_box(0);
x_1212 = x_1253;
goto block_1241;
}
}
block_1241:
{
uint8_t x_1213; lean_object* x_1214; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; uint8_t x_1232; 
lean_dec(x_1212);
x_1229 = lean_st_ref_get(x_6, x_1208);
x_1230 = lean_ctor_get(x_1229, 0);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_1230, 3);
lean_inc(x_1231);
lean_dec(x_1230);
x_1232 = lean_ctor_get_uint8(x_1231, sizeof(void*)*1);
lean_dec(x_1231);
if (x_1232 == 0)
{
lean_object* x_1233; uint8_t x_1234; 
x_1233 = lean_ctor_get(x_1229, 1);
lean_inc(x_1233);
lean_dec(x_1229);
x_1234 = 0;
x_1213 = x_1234;
x_1214 = x_1233;
goto block_1228;
}
else
{
lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; uint8_t x_1240; 
x_1235 = lean_ctor_get(x_1229, 1);
lean_inc(x_1235);
lean_dec(x_1229);
x_1236 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1237 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1236, x_3, x_4, x_5, x_6, x_1235);
x_1238 = lean_ctor_get(x_1237, 0);
lean_inc(x_1238);
x_1239 = lean_ctor_get(x_1237, 1);
lean_inc(x_1239);
lean_dec(x_1237);
x_1240 = lean_unbox(x_1238);
lean_dec(x_1238);
x_1213 = x_1240;
x_1214 = x_1239;
goto block_1228;
}
block_1228:
{
if (x_1213 == 0)
{
lean_object* x_1215; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1215 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1214);
return x_1215;
}
else
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; 
x_1216 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1216, 0, x_1);
x_1217 = l_Lean_KernelException_toMessageData___closed__15;
x_1218 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1218, 0, x_1217);
lean_ctor_set(x_1218, 1, x_1216);
x_1219 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1220 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1220, 0, x_1218);
lean_ctor_set(x_1220, 1, x_1219);
x_1221 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1221, 0, x_2);
x_1222 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1222, 0, x_1220);
lean_ctor_set(x_1222, 1, x_1221);
x_1223 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1223, 0, x_1222);
lean_ctor_set(x_1223, 1, x_1217);
x_1224 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1225 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1224, x_1223, x_3, x_4, x_5, x_6, x_1214);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1226 = lean_ctor_get(x_1225, 1);
lean_inc(x_1226);
lean_dec(x_1225);
x_1227 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1226);
return x_1227;
}
}
}
}
else
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; uint8_t x_1257; lean_object* x_1258; lean_object* x_1259; 
x_1254 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1208);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1255 = lean_ctor_get(x_1254, 1);
lean_inc(x_1255);
if (lean_is_exclusive(x_1254)) {
 lean_ctor_release(x_1254, 0);
 lean_ctor_release(x_1254, 1);
 x_1256 = x_1254;
} else {
 lean_dec_ref(x_1254);
 x_1256 = lean_box(0);
}
x_1257 = 1;
x_1258 = lean_box(x_1257);
if (lean_is_scalar(x_1256)) {
 x_1259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1259 = x_1256;
}
lean_ctor_set(x_1259, 0, x_1258);
lean_ctor_set(x_1259, 1, x_1255);
return x_1259;
}
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; uint8_t x_1263; lean_object* x_1264; lean_object* x_1265; 
lean_dec(x_1209);
x_1260 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1208);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1261 = lean_ctor_get(x_1260, 1);
lean_inc(x_1261);
if (lean_is_exclusive(x_1260)) {
 lean_ctor_release(x_1260, 0);
 lean_ctor_release(x_1260, 1);
 x_1262 = x_1260;
} else {
 lean_dec_ref(x_1260);
 x_1262 = lean_box(0);
}
x_1263 = 1;
x_1264 = lean_box(x_1263);
if (lean_is_scalar(x_1262)) {
 x_1265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1265 = x_1262;
}
lean_ctor_set(x_1265, 0, x_1264);
lean_ctor_set(x_1265, 1, x_1261);
return x_1265;
}
}
}
}
else
{
lean_object* x_1266; lean_object* x_1267; uint8_t x_1268; uint8_t x_1269; 
x_1266 = lean_ctor_get(x_1130, 0);
x_1267 = lean_ctor_get(x_1130, 1);
lean_inc(x_1267);
lean_inc(x_1266);
lean_dec(x_1130);
x_1268 = lean_unbox(x_1266);
x_1269 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1268, x_1123);
if (x_1269 == 0)
{
uint8_t x_1270; uint8_t x_1271; uint8_t x_1272; lean_object* x_1273; lean_object* x_1274; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1270 = 1;
x_1271 = lean_unbox(x_1266);
lean_dec(x_1266);
x_1272 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1271, x_1270);
x_1273 = lean_box(x_1272);
x_1274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1274, 0, x_1273);
lean_ctor_set(x_1274, 1, x_1267);
return x_1274;
}
else
{
lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; uint8_t x_1282; 
lean_dec(x_1266);
x_1275 = lean_st_ref_get(x_6, x_1267);
x_1276 = lean_ctor_get(x_1275, 1);
lean_inc(x_1276);
lean_dec(x_1275);
x_1277 = lean_st_ref_get(x_4, x_1276);
x_1278 = lean_ctor_get(x_1277, 0);
lean_inc(x_1278);
x_1279 = lean_ctor_get(x_1277, 1);
lean_inc(x_1279);
if (lean_is_exclusive(x_1277)) {
 lean_ctor_release(x_1277, 0);
 lean_ctor_release(x_1277, 1);
 x_1280 = x_1277;
} else {
 lean_dec_ref(x_1277);
 x_1280 = lean_box(0);
}
x_1281 = lean_ctor_get(x_1278, 0);
lean_inc(x_1281);
lean_dec(x_1278);
lean_inc(x_1281);
x_1282 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1281, x_1);
if (x_1282 == 0)
{
uint8_t x_1283; 
x_1283 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1281, x_2);
if (x_1283 == 0)
{
lean_object* x_1284; lean_object* x_1314; uint8_t x_1315; 
x_1314 = lean_ctor_get(x_3, 0);
lean_inc(x_1314);
x_1315 = lean_ctor_get_uint8(x_1314, 4);
lean_dec(x_1314);
if (x_1315 == 0)
{
uint8_t x_1316; lean_object* x_1317; lean_object* x_1318; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1316 = 0;
x_1317 = lean_box(x_1316);
if (lean_is_scalar(x_1280)) {
 x_1318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1318 = x_1280;
}
lean_ctor_set(x_1318, 0, x_1317);
lean_ctor_set(x_1318, 1, x_1279);
return x_1318;
}
else
{
uint8_t x_1319; 
x_1319 = l_Lean_Level_isMVar(x_1);
if (x_1319 == 0)
{
uint8_t x_1320; 
x_1320 = l_Lean_Level_isMVar(x_2);
if (x_1320 == 0)
{
uint8_t x_1321; lean_object* x_1322; lean_object* x_1323; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1321 = 0;
x_1322 = lean_box(x_1321);
if (lean_is_scalar(x_1280)) {
 x_1323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1323 = x_1280;
}
lean_ctor_set(x_1323, 0, x_1322);
lean_ctor_set(x_1323, 1, x_1279);
return x_1323;
}
else
{
lean_object* x_1324; 
lean_dec(x_1280);
x_1324 = lean_box(0);
x_1284 = x_1324;
goto block_1313;
}
}
else
{
lean_object* x_1325; 
lean_dec(x_1280);
x_1325 = lean_box(0);
x_1284 = x_1325;
goto block_1313;
}
}
block_1313:
{
uint8_t x_1285; lean_object* x_1286; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; uint8_t x_1304; 
lean_dec(x_1284);
x_1301 = lean_st_ref_get(x_6, x_1279);
x_1302 = lean_ctor_get(x_1301, 0);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_1302, 3);
lean_inc(x_1303);
lean_dec(x_1302);
x_1304 = lean_ctor_get_uint8(x_1303, sizeof(void*)*1);
lean_dec(x_1303);
if (x_1304 == 0)
{
lean_object* x_1305; uint8_t x_1306; 
x_1305 = lean_ctor_get(x_1301, 1);
lean_inc(x_1305);
lean_dec(x_1301);
x_1306 = 0;
x_1285 = x_1306;
x_1286 = x_1305;
goto block_1300;
}
else
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; uint8_t x_1312; 
x_1307 = lean_ctor_get(x_1301, 1);
lean_inc(x_1307);
lean_dec(x_1301);
x_1308 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1309 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1308, x_3, x_4, x_5, x_6, x_1307);
x_1310 = lean_ctor_get(x_1309, 0);
lean_inc(x_1310);
x_1311 = lean_ctor_get(x_1309, 1);
lean_inc(x_1311);
lean_dec(x_1309);
x_1312 = lean_unbox(x_1310);
lean_dec(x_1310);
x_1285 = x_1312;
x_1286 = x_1311;
goto block_1300;
}
block_1300:
{
if (x_1285 == 0)
{
lean_object* x_1287; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1287 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1286);
return x_1287;
}
else
{
lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; 
x_1288 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1288, 0, x_1);
x_1289 = l_Lean_KernelException_toMessageData___closed__15;
x_1290 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1290, 0, x_1289);
lean_ctor_set(x_1290, 1, x_1288);
x_1291 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1292 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1292, 0, x_1290);
lean_ctor_set(x_1292, 1, x_1291);
x_1293 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1293, 0, x_2);
x_1294 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1294, 0, x_1292);
lean_ctor_set(x_1294, 1, x_1293);
x_1295 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1295, 0, x_1294);
lean_ctor_set(x_1295, 1, x_1289);
x_1296 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1297 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1296, x_1295, x_3, x_4, x_5, x_6, x_1286);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1298 = lean_ctor_get(x_1297, 1);
lean_inc(x_1298);
lean_dec(x_1297);
x_1299 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1298);
return x_1299;
}
}
}
}
else
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; uint8_t x_1329; lean_object* x_1330; lean_object* x_1331; 
lean_dec(x_1280);
x_1326 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1279);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1327 = lean_ctor_get(x_1326, 1);
lean_inc(x_1327);
if (lean_is_exclusive(x_1326)) {
 lean_ctor_release(x_1326, 0);
 lean_ctor_release(x_1326, 1);
 x_1328 = x_1326;
} else {
 lean_dec_ref(x_1326);
 x_1328 = lean_box(0);
}
x_1329 = 1;
x_1330 = lean_box(x_1329);
if (lean_is_scalar(x_1328)) {
 x_1331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1331 = x_1328;
}
lean_ctor_set(x_1331, 0, x_1330);
lean_ctor_set(x_1331, 1, x_1327);
return x_1331;
}
}
else
{
lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; uint8_t x_1335; lean_object* x_1336; lean_object* x_1337; 
lean_dec(x_1281);
lean_dec(x_1280);
x_1332 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1279);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1333 = lean_ctor_get(x_1332, 1);
lean_inc(x_1333);
if (lean_is_exclusive(x_1332)) {
 lean_ctor_release(x_1332, 0);
 lean_ctor_release(x_1332, 1);
 x_1334 = x_1332;
} else {
 lean_dec_ref(x_1332);
 x_1334 = lean_box(0);
}
x_1335 = 1;
x_1336 = lean_box(x_1335);
if (lean_is_scalar(x_1334)) {
 x_1337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1337 = x_1334;
}
lean_ctor_set(x_1337, 0, x_1336);
lean_ctor_set(x_1337, 1, x_1333);
return x_1337;
}
}
}
}
else
{
uint8_t x_1338; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1338 = !lean_is_exclusive(x_1130);
if (x_1338 == 0)
{
return x_1130;
}
else
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
x_1339 = lean_ctor_get(x_1130, 0);
x_1340 = lean_ctor_get(x_1130, 1);
lean_inc(x_1340);
lean_inc(x_1339);
lean_dec(x_1130);
x_1341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1341, 0, x_1339);
lean_ctor_set(x_1341, 1, x_1340);
return x_1341;
}
}
}
}
else
{
lean_object* x_1342; lean_object* x_1343; uint8_t x_1344; uint8_t x_1345; uint8_t x_1346; 
x_1342 = lean_ctor_get(x_1119, 0);
x_1343 = lean_ctor_get(x_1119, 1);
lean_inc(x_1343);
lean_inc(x_1342);
lean_dec(x_1119);
x_1344 = 2;
x_1345 = lean_unbox(x_1342);
x_1346 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1345, x_1344);
if (x_1346 == 0)
{
uint8_t x_1347; uint8_t x_1348; uint8_t x_1349; lean_object* x_1350; lean_object* x_1351; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1347 = 1;
x_1348 = lean_unbox(x_1342);
lean_dec(x_1342);
x_1349 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1348, x_1347);
x_1350 = lean_box(x_1349);
x_1351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1351, 0, x_1350);
lean_ctor_set(x_1351, 1, x_1343);
return x_1351;
}
else
{
lean_object* x_1352; 
lean_dec(x_1342);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_1352 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_1343);
if (lean_obj_tag(x_1352) == 0)
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; uint8_t x_1356; uint8_t x_1357; 
x_1353 = lean_ctor_get(x_1352, 0);
lean_inc(x_1353);
x_1354 = lean_ctor_get(x_1352, 1);
lean_inc(x_1354);
if (lean_is_exclusive(x_1352)) {
 lean_ctor_release(x_1352, 0);
 lean_ctor_release(x_1352, 1);
 x_1355 = x_1352;
} else {
 lean_dec_ref(x_1352);
 x_1355 = lean_box(0);
}
x_1356 = lean_unbox(x_1353);
x_1357 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1356, x_1344);
if (x_1357 == 0)
{
uint8_t x_1358; uint8_t x_1359; uint8_t x_1360; lean_object* x_1361; lean_object* x_1362; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1358 = 1;
x_1359 = lean_unbox(x_1353);
lean_dec(x_1353);
x_1360 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1359, x_1358);
x_1361 = lean_box(x_1360);
if (lean_is_scalar(x_1355)) {
 x_1362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1362 = x_1355;
}
lean_ctor_set(x_1362, 0, x_1361);
lean_ctor_set(x_1362, 1, x_1354);
return x_1362;
}
else
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; uint8_t x_1370; 
lean_dec(x_1355);
lean_dec(x_1353);
x_1363 = lean_st_ref_get(x_6, x_1354);
x_1364 = lean_ctor_get(x_1363, 1);
lean_inc(x_1364);
lean_dec(x_1363);
x_1365 = lean_st_ref_get(x_4, x_1364);
x_1366 = lean_ctor_get(x_1365, 0);
lean_inc(x_1366);
x_1367 = lean_ctor_get(x_1365, 1);
lean_inc(x_1367);
if (lean_is_exclusive(x_1365)) {
 lean_ctor_release(x_1365, 0);
 lean_ctor_release(x_1365, 1);
 x_1368 = x_1365;
} else {
 lean_dec_ref(x_1365);
 x_1368 = lean_box(0);
}
x_1369 = lean_ctor_get(x_1366, 0);
lean_inc(x_1369);
lean_dec(x_1366);
lean_inc(x_1369);
x_1370 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1369, x_1);
if (x_1370 == 0)
{
uint8_t x_1371; 
x_1371 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1369, x_2);
if (x_1371 == 0)
{
lean_object* x_1372; lean_object* x_1402; uint8_t x_1403; 
x_1402 = lean_ctor_get(x_3, 0);
lean_inc(x_1402);
x_1403 = lean_ctor_get_uint8(x_1402, 4);
lean_dec(x_1402);
if (x_1403 == 0)
{
uint8_t x_1404; lean_object* x_1405; lean_object* x_1406; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1404 = 0;
x_1405 = lean_box(x_1404);
if (lean_is_scalar(x_1368)) {
 x_1406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1406 = x_1368;
}
lean_ctor_set(x_1406, 0, x_1405);
lean_ctor_set(x_1406, 1, x_1367);
return x_1406;
}
else
{
uint8_t x_1407; 
x_1407 = l_Lean_Level_isMVar(x_1);
if (x_1407 == 0)
{
uint8_t x_1408; 
x_1408 = l_Lean_Level_isMVar(x_2);
if (x_1408 == 0)
{
uint8_t x_1409; lean_object* x_1410; lean_object* x_1411; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1409 = 0;
x_1410 = lean_box(x_1409);
if (lean_is_scalar(x_1368)) {
 x_1411 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1411 = x_1368;
}
lean_ctor_set(x_1411, 0, x_1410);
lean_ctor_set(x_1411, 1, x_1367);
return x_1411;
}
else
{
lean_object* x_1412; 
lean_dec(x_1368);
x_1412 = lean_box(0);
x_1372 = x_1412;
goto block_1401;
}
}
else
{
lean_object* x_1413; 
lean_dec(x_1368);
x_1413 = lean_box(0);
x_1372 = x_1413;
goto block_1401;
}
}
block_1401:
{
uint8_t x_1373; lean_object* x_1374; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; uint8_t x_1392; 
lean_dec(x_1372);
x_1389 = lean_st_ref_get(x_6, x_1367);
x_1390 = lean_ctor_get(x_1389, 0);
lean_inc(x_1390);
x_1391 = lean_ctor_get(x_1390, 3);
lean_inc(x_1391);
lean_dec(x_1390);
x_1392 = lean_ctor_get_uint8(x_1391, sizeof(void*)*1);
lean_dec(x_1391);
if (x_1392 == 0)
{
lean_object* x_1393; uint8_t x_1394; 
x_1393 = lean_ctor_get(x_1389, 1);
lean_inc(x_1393);
lean_dec(x_1389);
x_1394 = 0;
x_1373 = x_1394;
x_1374 = x_1393;
goto block_1388;
}
else
{
lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; uint8_t x_1400; 
x_1395 = lean_ctor_get(x_1389, 1);
lean_inc(x_1395);
lean_dec(x_1389);
x_1396 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1397 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1396, x_3, x_4, x_5, x_6, x_1395);
x_1398 = lean_ctor_get(x_1397, 0);
lean_inc(x_1398);
x_1399 = lean_ctor_get(x_1397, 1);
lean_inc(x_1399);
lean_dec(x_1397);
x_1400 = lean_unbox(x_1398);
lean_dec(x_1398);
x_1373 = x_1400;
x_1374 = x_1399;
goto block_1388;
}
block_1388:
{
if (x_1373 == 0)
{
lean_object* x_1375; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1375 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1374);
return x_1375;
}
else
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
x_1376 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1376, 0, x_1);
x_1377 = l_Lean_KernelException_toMessageData___closed__15;
x_1378 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1378, 0, x_1377);
lean_ctor_set(x_1378, 1, x_1376);
x_1379 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1380 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1380, 0, x_1378);
lean_ctor_set(x_1380, 1, x_1379);
x_1381 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1381, 0, x_2);
x_1382 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1382, 0, x_1380);
lean_ctor_set(x_1382, 1, x_1381);
x_1383 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1383, 0, x_1382);
lean_ctor_set(x_1383, 1, x_1377);
x_1384 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1385 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1384, x_1383, x_3, x_4, x_5, x_6, x_1374);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1386 = lean_ctor_get(x_1385, 1);
lean_inc(x_1386);
lean_dec(x_1385);
x_1387 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1386);
return x_1387;
}
}
}
}
else
{
lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; uint8_t x_1417; lean_object* x_1418; lean_object* x_1419; 
lean_dec(x_1368);
x_1414 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1367);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1415 = lean_ctor_get(x_1414, 1);
lean_inc(x_1415);
if (lean_is_exclusive(x_1414)) {
 lean_ctor_release(x_1414, 0);
 lean_ctor_release(x_1414, 1);
 x_1416 = x_1414;
} else {
 lean_dec_ref(x_1414);
 x_1416 = lean_box(0);
}
x_1417 = 1;
x_1418 = lean_box(x_1417);
if (lean_is_scalar(x_1416)) {
 x_1419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1419 = x_1416;
}
lean_ctor_set(x_1419, 0, x_1418);
lean_ctor_set(x_1419, 1, x_1415);
return x_1419;
}
}
else
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; uint8_t x_1423; lean_object* x_1424; lean_object* x_1425; 
lean_dec(x_1369);
lean_dec(x_1368);
x_1420 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1367);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1421 = lean_ctor_get(x_1420, 1);
lean_inc(x_1421);
if (lean_is_exclusive(x_1420)) {
 lean_ctor_release(x_1420, 0);
 lean_ctor_release(x_1420, 1);
 x_1422 = x_1420;
} else {
 lean_dec_ref(x_1420);
 x_1422 = lean_box(0);
}
x_1423 = 1;
x_1424 = lean_box(x_1423);
if (lean_is_scalar(x_1422)) {
 x_1425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1425 = x_1422;
}
lean_ctor_set(x_1425, 0, x_1424);
lean_ctor_set(x_1425, 1, x_1421);
return x_1425;
}
}
}
else
{
lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1426 = lean_ctor_get(x_1352, 0);
lean_inc(x_1426);
x_1427 = lean_ctor_get(x_1352, 1);
lean_inc(x_1427);
if (lean_is_exclusive(x_1352)) {
 lean_ctor_release(x_1352, 0);
 lean_ctor_release(x_1352, 1);
 x_1428 = x_1352;
} else {
 lean_dec_ref(x_1352);
 x_1428 = lean_box(0);
}
if (lean_is_scalar(x_1428)) {
 x_1429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1429 = x_1428;
}
lean_ctor_set(x_1429, 0, x_1426);
lean_ctor_set(x_1429, 1, x_1427);
return x_1429;
}
}
}
}
else
{
uint8_t x_1430; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1430 = !lean_is_exclusive(x_1119);
if (x_1430 == 0)
{
return x_1119;
}
else
{
lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; 
x_1431 = lean_ctor_get(x_1119, 0);
x_1432 = lean_ctor_get(x_1119, 1);
lean_inc(x_1432);
lean_inc(x_1431);
lean_dec(x_1119);
x_1433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1433, 0, x_1431);
lean_ctor_set(x_1433, 1, x_1432);
return x_1433;
}
}
}
}
}
block_1448:
{
if (x_1435 == 0)
{
x_1106 = x_1436;
goto block_1434;
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; 
lean_inc(x_1);
x_1437 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1437, 0, x_1);
x_1438 = l_Lean_KernelException_toMessageData___closed__15;
x_1439 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1439, 0, x_1438);
lean_ctor_set(x_1439, 1, x_1437);
x_1440 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1441 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1441, 0, x_1439);
lean_ctor_set(x_1441, 1, x_1440);
lean_inc(x_2);
x_1442 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1442, 0, x_2);
x_1443 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1443, 0, x_1441);
lean_ctor_set(x_1443, 1, x_1442);
x_1444 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1444, 0, x_1443);
lean_ctor_set(x_1444, 1, x_1438);
x_1445 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_1446 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1445, x_1444, x_3, x_4, x_5, x_6, x_1436);
x_1447 = lean_ctor_get(x_1446, 1);
lean_inc(x_1447);
lean_dec(x_1446);
x_1106 = x_1447;
goto block_1434;
}
}
}
else
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; uint8_t x_1464; lean_object* x_1465; lean_object* x_1466; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1461 = lean_unsigned_to_nat(0u);
x_1462 = l_Lean_Level_getOffsetAux(x_1, x_1461);
lean_dec(x_1);
x_1463 = l_Lean_Level_getOffsetAux(x_2, x_1461);
lean_dec(x_2);
x_1464 = lean_nat_dec_eq(x_1462, x_1463);
lean_dec(x_1463);
lean_dec(x_1462);
x_1465 = lean_box(x_1464);
x_1466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1466, 0, x_1465);
lean_ctor_set(x_1466, 1, x_7);
return x_1466;
}
}
case 4:
{
lean_object* x_1467; lean_object* x_1468; uint8_t x_1469; 
x_1467 = l_Lean_Level_getLevelOffset(x_1);
x_1468 = l_Lean_Level_getLevelOffset(x_2);
x_1469 = lean_level_eq(x_1467, x_1468);
lean_dec(x_1468);
lean_dec(x_1467);
if (x_1469 == 0)
{
lean_object* x_1470; uint8_t x_1799; lean_object* x_1800; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; uint8_t x_1816; 
x_1813 = lean_st_ref_get(x_6, x_7);
x_1814 = lean_ctor_get(x_1813, 0);
lean_inc(x_1814);
x_1815 = lean_ctor_get(x_1814, 3);
lean_inc(x_1815);
lean_dec(x_1814);
x_1816 = lean_ctor_get_uint8(x_1815, sizeof(void*)*1);
lean_dec(x_1815);
if (x_1816 == 0)
{
lean_object* x_1817; uint8_t x_1818; 
x_1817 = lean_ctor_get(x_1813, 1);
lean_inc(x_1817);
lean_dec(x_1813);
x_1818 = 0;
x_1799 = x_1818;
x_1800 = x_1817;
goto block_1812;
}
else
{
lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; uint8_t x_1824; 
x_1819 = lean_ctor_get(x_1813, 1);
lean_inc(x_1819);
lean_dec(x_1813);
x_1820 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_1821 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1820, x_3, x_4, x_5, x_6, x_1819);
x_1822 = lean_ctor_get(x_1821, 0);
lean_inc(x_1822);
x_1823 = lean_ctor_get(x_1821, 1);
lean_inc(x_1823);
lean_dec(x_1821);
x_1824 = lean_unbox(x_1822);
lean_dec(x_1822);
x_1799 = x_1824;
x_1800 = x_1823;
goto block_1812;
}
block_1798:
{
lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; uint8_t x_1479; 
lean_inc(x_1);
x_1471 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_1470);
x_1472 = lean_ctor_get(x_1471, 0);
lean_inc(x_1472);
x_1473 = lean_ctor_get(x_1471, 1);
lean_inc(x_1473);
lean_dec(x_1471);
x_1474 = l_Lean_Level_normalize(x_1472);
lean_dec(x_1472);
lean_inc(x_2);
x_1475 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_2, x_3, x_4, x_5, x_6, x_1473);
x_1476 = lean_ctor_get(x_1475, 0);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1475, 1);
lean_inc(x_1477);
lean_dec(x_1475);
x_1478 = l_Lean_Level_normalize(x_1476);
lean_dec(x_1476);
x_1479 = lean_level_eq(x_1, x_1474);
if (x_1479 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_1474;
x_2 = x_1478;
x_7 = x_1477;
goto _start;
}
else
{
uint8_t x_1481; 
x_1481 = lean_level_eq(x_2, x_1478);
if (x_1481 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_1474;
x_2 = x_1478;
x_7 = x_1477;
goto _start;
}
else
{
lean_object* x_1483; 
lean_dec(x_1478);
lean_dec(x_1474);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_1483 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_1477);
if (lean_obj_tag(x_1483) == 0)
{
uint8_t x_1484; 
x_1484 = !lean_is_exclusive(x_1483);
if (x_1484 == 0)
{
lean_object* x_1485; lean_object* x_1486; uint8_t x_1487; uint8_t x_1488; uint8_t x_1489; 
x_1485 = lean_ctor_get(x_1483, 0);
x_1486 = lean_ctor_get(x_1483, 1);
x_1487 = 2;
x_1488 = lean_unbox(x_1485);
x_1489 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1488, x_1487);
if (x_1489 == 0)
{
uint8_t x_1490; uint8_t x_1491; uint8_t x_1492; lean_object* x_1493; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1490 = 1;
x_1491 = lean_unbox(x_1485);
lean_dec(x_1485);
x_1492 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1491, x_1490);
x_1493 = lean_box(x_1492);
lean_ctor_set(x_1483, 0, x_1493);
return x_1483;
}
else
{
lean_object* x_1494; 
lean_free_object(x_1483);
lean_dec(x_1485);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_1494 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_1486);
if (lean_obj_tag(x_1494) == 0)
{
uint8_t x_1495; 
x_1495 = !lean_is_exclusive(x_1494);
if (x_1495 == 0)
{
lean_object* x_1496; lean_object* x_1497; uint8_t x_1498; uint8_t x_1499; 
x_1496 = lean_ctor_get(x_1494, 0);
x_1497 = lean_ctor_get(x_1494, 1);
x_1498 = lean_unbox(x_1496);
x_1499 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1498, x_1487);
if (x_1499 == 0)
{
uint8_t x_1500; uint8_t x_1501; uint8_t x_1502; lean_object* x_1503; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1500 = 1;
x_1501 = lean_unbox(x_1496);
lean_dec(x_1496);
x_1502 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1501, x_1500);
x_1503 = lean_box(x_1502);
lean_ctor_set(x_1494, 0, x_1503);
return x_1494;
}
else
{
lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; uint8_t x_1507; 
lean_free_object(x_1494);
lean_dec(x_1496);
x_1504 = lean_st_ref_get(x_6, x_1497);
x_1505 = lean_ctor_get(x_1504, 1);
lean_inc(x_1505);
lean_dec(x_1504);
x_1506 = lean_st_ref_get(x_4, x_1505);
x_1507 = !lean_is_exclusive(x_1506);
if (x_1507 == 0)
{
lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; uint8_t x_1511; 
x_1508 = lean_ctor_get(x_1506, 0);
x_1509 = lean_ctor_get(x_1506, 1);
x_1510 = lean_ctor_get(x_1508, 0);
lean_inc(x_1510);
lean_dec(x_1508);
lean_inc(x_1510);
x_1511 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1510, x_1);
if (x_1511 == 0)
{
uint8_t x_1512; 
x_1512 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1510, x_2);
if (x_1512 == 0)
{
lean_object* x_1513; lean_object* x_1543; uint8_t x_1544; 
x_1543 = lean_ctor_get(x_3, 0);
lean_inc(x_1543);
x_1544 = lean_ctor_get_uint8(x_1543, 4);
lean_dec(x_1543);
if (x_1544 == 0)
{
uint8_t x_1545; lean_object* x_1546; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1545 = 0;
x_1546 = lean_box(x_1545);
lean_ctor_set(x_1506, 0, x_1546);
return x_1506;
}
else
{
uint8_t x_1547; 
x_1547 = l_Lean_Level_isMVar(x_1);
if (x_1547 == 0)
{
uint8_t x_1548; 
x_1548 = l_Lean_Level_isMVar(x_2);
if (x_1548 == 0)
{
uint8_t x_1549; lean_object* x_1550; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1549 = 0;
x_1550 = lean_box(x_1549);
lean_ctor_set(x_1506, 0, x_1550);
return x_1506;
}
else
{
lean_object* x_1551; 
lean_free_object(x_1506);
x_1551 = lean_box(0);
x_1513 = x_1551;
goto block_1542;
}
}
else
{
lean_object* x_1552; 
lean_free_object(x_1506);
x_1552 = lean_box(0);
x_1513 = x_1552;
goto block_1542;
}
}
block_1542:
{
uint8_t x_1514; lean_object* x_1515; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; uint8_t x_1533; 
lean_dec(x_1513);
x_1530 = lean_st_ref_get(x_6, x_1509);
x_1531 = lean_ctor_get(x_1530, 0);
lean_inc(x_1531);
x_1532 = lean_ctor_get(x_1531, 3);
lean_inc(x_1532);
lean_dec(x_1531);
x_1533 = lean_ctor_get_uint8(x_1532, sizeof(void*)*1);
lean_dec(x_1532);
if (x_1533 == 0)
{
lean_object* x_1534; uint8_t x_1535; 
x_1534 = lean_ctor_get(x_1530, 1);
lean_inc(x_1534);
lean_dec(x_1530);
x_1535 = 0;
x_1514 = x_1535;
x_1515 = x_1534;
goto block_1529;
}
else
{
lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; uint8_t x_1541; 
x_1536 = lean_ctor_get(x_1530, 1);
lean_inc(x_1536);
lean_dec(x_1530);
x_1537 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1538 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1537, x_3, x_4, x_5, x_6, x_1536);
x_1539 = lean_ctor_get(x_1538, 0);
lean_inc(x_1539);
x_1540 = lean_ctor_get(x_1538, 1);
lean_inc(x_1540);
lean_dec(x_1538);
x_1541 = lean_unbox(x_1539);
lean_dec(x_1539);
x_1514 = x_1541;
x_1515 = x_1540;
goto block_1529;
}
block_1529:
{
if (x_1514 == 0)
{
lean_object* x_1516; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1516 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1515);
return x_1516;
}
else
{
lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; 
x_1517 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1517, 0, x_1);
x_1518 = l_Lean_KernelException_toMessageData___closed__15;
x_1519 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1519, 0, x_1518);
lean_ctor_set(x_1519, 1, x_1517);
x_1520 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1521 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1521, 0, x_1519);
lean_ctor_set(x_1521, 1, x_1520);
x_1522 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1522, 0, x_2);
x_1523 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1523, 0, x_1521);
lean_ctor_set(x_1523, 1, x_1522);
x_1524 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1524, 0, x_1523);
lean_ctor_set(x_1524, 1, x_1518);
x_1525 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1526 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1525, x_1524, x_3, x_4, x_5, x_6, x_1515);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1527 = lean_ctor_get(x_1526, 1);
lean_inc(x_1527);
lean_dec(x_1526);
x_1528 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1527);
return x_1528;
}
}
}
}
else
{
lean_object* x_1553; uint8_t x_1554; 
lean_free_object(x_1506);
x_1553 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1509);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1554 = !lean_is_exclusive(x_1553);
if (x_1554 == 0)
{
lean_object* x_1555; uint8_t x_1556; lean_object* x_1557; 
x_1555 = lean_ctor_get(x_1553, 0);
lean_dec(x_1555);
x_1556 = 1;
x_1557 = lean_box(x_1556);
lean_ctor_set(x_1553, 0, x_1557);
return x_1553;
}
else
{
lean_object* x_1558; uint8_t x_1559; lean_object* x_1560; lean_object* x_1561; 
x_1558 = lean_ctor_get(x_1553, 1);
lean_inc(x_1558);
lean_dec(x_1553);
x_1559 = 1;
x_1560 = lean_box(x_1559);
x_1561 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1561, 0, x_1560);
lean_ctor_set(x_1561, 1, x_1558);
return x_1561;
}
}
}
else
{
lean_object* x_1562; uint8_t x_1563; 
lean_dec(x_1510);
lean_free_object(x_1506);
x_1562 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1509);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1563 = !lean_is_exclusive(x_1562);
if (x_1563 == 0)
{
lean_object* x_1564; uint8_t x_1565; lean_object* x_1566; 
x_1564 = lean_ctor_get(x_1562, 0);
lean_dec(x_1564);
x_1565 = 1;
x_1566 = lean_box(x_1565);
lean_ctor_set(x_1562, 0, x_1566);
return x_1562;
}
else
{
lean_object* x_1567; uint8_t x_1568; lean_object* x_1569; lean_object* x_1570; 
x_1567 = lean_ctor_get(x_1562, 1);
lean_inc(x_1567);
lean_dec(x_1562);
x_1568 = 1;
x_1569 = lean_box(x_1568);
x_1570 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1570, 0, x_1569);
lean_ctor_set(x_1570, 1, x_1567);
return x_1570;
}
}
}
else
{
lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; uint8_t x_1574; 
x_1571 = lean_ctor_get(x_1506, 0);
x_1572 = lean_ctor_get(x_1506, 1);
lean_inc(x_1572);
lean_inc(x_1571);
lean_dec(x_1506);
x_1573 = lean_ctor_get(x_1571, 0);
lean_inc(x_1573);
lean_dec(x_1571);
lean_inc(x_1573);
x_1574 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1573, x_1);
if (x_1574 == 0)
{
uint8_t x_1575; 
x_1575 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1573, x_2);
if (x_1575 == 0)
{
lean_object* x_1576; lean_object* x_1606; uint8_t x_1607; 
x_1606 = lean_ctor_get(x_3, 0);
lean_inc(x_1606);
x_1607 = lean_ctor_get_uint8(x_1606, 4);
lean_dec(x_1606);
if (x_1607 == 0)
{
uint8_t x_1608; lean_object* x_1609; lean_object* x_1610; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1608 = 0;
x_1609 = lean_box(x_1608);
x_1610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1610, 0, x_1609);
lean_ctor_set(x_1610, 1, x_1572);
return x_1610;
}
else
{
uint8_t x_1611; 
x_1611 = l_Lean_Level_isMVar(x_1);
if (x_1611 == 0)
{
uint8_t x_1612; 
x_1612 = l_Lean_Level_isMVar(x_2);
if (x_1612 == 0)
{
uint8_t x_1613; lean_object* x_1614; lean_object* x_1615; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1613 = 0;
x_1614 = lean_box(x_1613);
x_1615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1615, 0, x_1614);
lean_ctor_set(x_1615, 1, x_1572);
return x_1615;
}
else
{
lean_object* x_1616; 
x_1616 = lean_box(0);
x_1576 = x_1616;
goto block_1605;
}
}
else
{
lean_object* x_1617; 
x_1617 = lean_box(0);
x_1576 = x_1617;
goto block_1605;
}
}
block_1605:
{
uint8_t x_1577; lean_object* x_1578; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; uint8_t x_1596; 
lean_dec(x_1576);
x_1593 = lean_st_ref_get(x_6, x_1572);
x_1594 = lean_ctor_get(x_1593, 0);
lean_inc(x_1594);
x_1595 = lean_ctor_get(x_1594, 3);
lean_inc(x_1595);
lean_dec(x_1594);
x_1596 = lean_ctor_get_uint8(x_1595, sizeof(void*)*1);
lean_dec(x_1595);
if (x_1596 == 0)
{
lean_object* x_1597; uint8_t x_1598; 
x_1597 = lean_ctor_get(x_1593, 1);
lean_inc(x_1597);
lean_dec(x_1593);
x_1598 = 0;
x_1577 = x_1598;
x_1578 = x_1597;
goto block_1592;
}
else
{
lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; uint8_t x_1604; 
x_1599 = lean_ctor_get(x_1593, 1);
lean_inc(x_1599);
lean_dec(x_1593);
x_1600 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1601 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1600, x_3, x_4, x_5, x_6, x_1599);
x_1602 = lean_ctor_get(x_1601, 0);
lean_inc(x_1602);
x_1603 = lean_ctor_get(x_1601, 1);
lean_inc(x_1603);
lean_dec(x_1601);
x_1604 = lean_unbox(x_1602);
lean_dec(x_1602);
x_1577 = x_1604;
x_1578 = x_1603;
goto block_1592;
}
block_1592:
{
if (x_1577 == 0)
{
lean_object* x_1579; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1579 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1578);
return x_1579;
}
else
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; 
x_1580 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1580, 0, x_1);
x_1581 = l_Lean_KernelException_toMessageData___closed__15;
x_1582 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1582, 0, x_1581);
lean_ctor_set(x_1582, 1, x_1580);
x_1583 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1584 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1584, 0, x_1582);
lean_ctor_set(x_1584, 1, x_1583);
x_1585 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1585, 0, x_2);
x_1586 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1586, 0, x_1584);
lean_ctor_set(x_1586, 1, x_1585);
x_1587 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1587, 0, x_1586);
lean_ctor_set(x_1587, 1, x_1581);
x_1588 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1589 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1588, x_1587, x_3, x_4, x_5, x_6, x_1578);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1590 = lean_ctor_get(x_1589, 1);
lean_inc(x_1590);
lean_dec(x_1589);
x_1591 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1590);
return x_1591;
}
}
}
}
else
{
lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; uint8_t x_1621; lean_object* x_1622; lean_object* x_1623; 
x_1618 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1572);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1619 = lean_ctor_get(x_1618, 1);
lean_inc(x_1619);
if (lean_is_exclusive(x_1618)) {
 lean_ctor_release(x_1618, 0);
 lean_ctor_release(x_1618, 1);
 x_1620 = x_1618;
} else {
 lean_dec_ref(x_1618);
 x_1620 = lean_box(0);
}
x_1621 = 1;
x_1622 = lean_box(x_1621);
if (lean_is_scalar(x_1620)) {
 x_1623 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1623 = x_1620;
}
lean_ctor_set(x_1623, 0, x_1622);
lean_ctor_set(x_1623, 1, x_1619);
return x_1623;
}
}
else
{
lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; uint8_t x_1627; lean_object* x_1628; lean_object* x_1629; 
lean_dec(x_1573);
x_1624 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1572);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1625 = lean_ctor_get(x_1624, 1);
lean_inc(x_1625);
if (lean_is_exclusive(x_1624)) {
 lean_ctor_release(x_1624, 0);
 lean_ctor_release(x_1624, 1);
 x_1626 = x_1624;
} else {
 lean_dec_ref(x_1624);
 x_1626 = lean_box(0);
}
x_1627 = 1;
x_1628 = lean_box(x_1627);
if (lean_is_scalar(x_1626)) {
 x_1629 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1629 = x_1626;
}
lean_ctor_set(x_1629, 0, x_1628);
lean_ctor_set(x_1629, 1, x_1625);
return x_1629;
}
}
}
}
else
{
lean_object* x_1630; lean_object* x_1631; uint8_t x_1632; uint8_t x_1633; 
x_1630 = lean_ctor_get(x_1494, 0);
x_1631 = lean_ctor_get(x_1494, 1);
lean_inc(x_1631);
lean_inc(x_1630);
lean_dec(x_1494);
x_1632 = lean_unbox(x_1630);
x_1633 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1632, x_1487);
if (x_1633 == 0)
{
uint8_t x_1634; uint8_t x_1635; uint8_t x_1636; lean_object* x_1637; lean_object* x_1638; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1634 = 1;
x_1635 = lean_unbox(x_1630);
lean_dec(x_1630);
x_1636 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1635, x_1634);
x_1637 = lean_box(x_1636);
x_1638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1638, 0, x_1637);
lean_ctor_set(x_1638, 1, x_1631);
return x_1638;
}
else
{
lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; uint8_t x_1646; 
lean_dec(x_1630);
x_1639 = lean_st_ref_get(x_6, x_1631);
x_1640 = lean_ctor_get(x_1639, 1);
lean_inc(x_1640);
lean_dec(x_1639);
x_1641 = lean_st_ref_get(x_4, x_1640);
x_1642 = lean_ctor_get(x_1641, 0);
lean_inc(x_1642);
x_1643 = lean_ctor_get(x_1641, 1);
lean_inc(x_1643);
if (lean_is_exclusive(x_1641)) {
 lean_ctor_release(x_1641, 0);
 lean_ctor_release(x_1641, 1);
 x_1644 = x_1641;
} else {
 lean_dec_ref(x_1641);
 x_1644 = lean_box(0);
}
x_1645 = lean_ctor_get(x_1642, 0);
lean_inc(x_1645);
lean_dec(x_1642);
lean_inc(x_1645);
x_1646 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1645, x_1);
if (x_1646 == 0)
{
uint8_t x_1647; 
x_1647 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1645, x_2);
if (x_1647 == 0)
{
lean_object* x_1648; lean_object* x_1678; uint8_t x_1679; 
x_1678 = lean_ctor_get(x_3, 0);
lean_inc(x_1678);
x_1679 = lean_ctor_get_uint8(x_1678, 4);
lean_dec(x_1678);
if (x_1679 == 0)
{
uint8_t x_1680; lean_object* x_1681; lean_object* x_1682; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1680 = 0;
x_1681 = lean_box(x_1680);
if (lean_is_scalar(x_1644)) {
 x_1682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1682 = x_1644;
}
lean_ctor_set(x_1682, 0, x_1681);
lean_ctor_set(x_1682, 1, x_1643);
return x_1682;
}
else
{
uint8_t x_1683; 
x_1683 = l_Lean_Level_isMVar(x_1);
if (x_1683 == 0)
{
uint8_t x_1684; 
x_1684 = l_Lean_Level_isMVar(x_2);
if (x_1684 == 0)
{
uint8_t x_1685; lean_object* x_1686; lean_object* x_1687; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1685 = 0;
x_1686 = lean_box(x_1685);
if (lean_is_scalar(x_1644)) {
 x_1687 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1687 = x_1644;
}
lean_ctor_set(x_1687, 0, x_1686);
lean_ctor_set(x_1687, 1, x_1643);
return x_1687;
}
else
{
lean_object* x_1688; 
lean_dec(x_1644);
x_1688 = lean_box(0);
x_1648 = x_1688;
goto block_1677;
}
}
else
{
lean_object* x_1689; 
lean_dec(x_1644);
x_1689 = lean_box(0);
x_1648 = x_1689;
goto block_1677;
}
}
block_1677:
{
uint8_t x_1649; lean_object* x_1650; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; uint8_t x_1668; 
lean_dec(x_1648);
x_1665 = lean_st_ref_get(x_6, x_1643);
x_1666 = lean_ctor_get(x_1665, 0);
lean_inc(x_1666);
x_1667 = lean_ctor_get(x_1666, 3);
lean_inc(x_1667);
lean_dec(x_1666);
x_1668 = lean_ctor_get_uint8(x_1667, sizeof(void*)*1);
lean_dec(x_1667);
if (x_1668 == 0)
{
lean_object* x_1669; uint8_t x_1670; 
x_1669 = lean_ctor_get(x_1665, 1);
lean_inc(x_1669);
lean_dec(x_1665);
x_1670 = 0;
x_1649 = x_1670;
x_1650 = x_1669;
goto block_1664;
}
else
{
lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; uint8_t x_1676; 
x_1671 = lean_ctor_get(x_1665, 1);
lean_inc(x_1671);
lean_dec(x_1665);
x_1672 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1673 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1672, x_3, x_4, x_5, x_6, x_1671);
x_1674 = lean_ctor_get(x_1673, 0);
lean_inc(x_1674);
x_1675 = lean_ctor_get(x_1673, 1);
lean_inc(x_1675);
lean_dec(x_1673);
x_1676 = lean_unbox(x_1674);
lean_dec(x_1674);
x_1649 = x_1676;
x_1650 = x_1675;
goto block_1664;
}
block_1664:
{
if (x_1649 == 0)
{
lean_object* x_1651; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1651 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1650);
return x_1651;
}
else
{
lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; 
x_1652 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1652, 0, x_1);
x_1653 = l_Lean_KernelException_toMessageData___closed__15;
x_1654 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1654, 0, x_1653);
lean_ctor_set(x_1654, 1, x_1652);
x_1655 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1656 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1656, 0, x_1654);
lean_ctor_set(x_1656, 1, x_1655);
x_1657 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1657, 0, x_2);
x_1658 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1658, 0, x_1656);
lean_ctor_set(x_1658, 1, x_1657);
x_1659 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1659, 0, x_1658);
lean_ctor_set(x_1659, 1, x_1653);
x_1660 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1661 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1660, x_1659, x_3, x_4, x_5, x_6, x_1650);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1662 = lean_ctor_get(x_1661, 1);
lean_inc(x_1662);
lean_dec(x_1661);
x_1663 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1662);
return x_1663;
}
}
}
}
else
{
lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; uint8_t x_1693; lean_object* x_1694; lean_object* x_1695; 
lean_dec(x_1644);
x_1690 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1643);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1691 = lean_ctor_get(x_1690, 1);
lean_inc(x_1691);
if (lean_is_exclusive(x_1690)) {
 lean_ctor_release(x_1690, 0);
 lean_ctor_release(x_1690, 1);
 x_1692 = x_1690;
} else {
 lean_dec_ref(x_1690);
 x_1692 = lean_box(0);
}
x_1693 = 1;
x_1694 = lean_box(x_1693);
if (lean_is_scalar(x_1692)) {
 x_1695 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1695 = x_1692;
}
lean_ctor_set(x_1695, 0, x_1694);
lean_ctor_set(x_1695, 1, x_1691);
return x_1695;
}
}
else
{
lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; uint8_t x_1699; lean_object* x_1700; lean_object* x_1701; 
lean_dec(x_1645);
lean_dec(x_1644);
x_1696 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1643);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1697 = lean_ctor_get(x_1696, 1);
lean_inc(x_1697);
if (lean_is_exclusive(x_1696)) {
 lean_ctor_release(x_1696, 0);
 lean_ctor_release(x_1696, 1);
 x_1698 = x_1696;
} else {
 lean_dec_ref(x_1696);
 x_1698 = lean_box(0);
}
x_1699 = 1;
x_1700 = lean_box(x_1699);
if (lean_is_scalar(x_1698)) {
 x_1701 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1701 = x_1698;
}
lean_ctor_set(x_1701, 0, x_1700);
lean_ctor_set(x_1701, 1, x_1697);
return x_1701;
}
}
}
}
else
{
uint8_t x_1702; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1702 = !lean_is_exclusive(x_1494);
if (x_1702 == 0)
{
return x_1494;
}
else
{
lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; 
x_1703 = lean_ctor_get(x_1494, 0);
x_1704 = lean_ctor_get(x_1494, 1);
lean_inc(x_1704);
lean_inc(x_1703);
lean_dec(x_1494);
x_1705 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1705, 0, x_1703);
lean_ctor_set(x_1705, 1, x_1704);
return x_1705;
}
}
}
}
else
{
lean_object* x_1706; lean_object* x_1707; uint8_t x_1708; uint8_t x_1709; uint8_t x_1710; 
x_1706 = lean_ctor_get(x_1483, 0);
x_1707 = lean_ctor_get(x_1483, 1);
lean_inc(x_1707);
lean_inc(x_1706);
lean_dec(x_1483);
x_1708 = 2;
x_1709 = lean_unbox(x_1706);
x_1710 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1709, x_1708);
if (x_1710 == 0)
{
uint8_t x_1711; uint8_t x_1712; uint8_t x_1713; lean_object* x_1714; lean_object* x_1715; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1711 = 1;
x_1712 = lean_unbox(x_1706);
lean_dec(x_1706);
x_1713 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1712, x_1711);
x_1714 = lean_box(x_1713);
x_1715 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1715, 0, x_1714);
lean_ctor_set(x_1715, 1, x_1707);
return x_1715;
}
else
{
lean_object* x_1716; 
lean_dec(x_1706);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_1716 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_1707);
if (lean_obj_tag(x_1716) == 0)
{
lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; uint8_t x_1720; uint8_t x_1721; 
x_1717 = lean_ctor_get(x_1716, 0);
lean_inc(x_1717);
x_1718 = lean_ctor_get(x_1716, 1);
lean_inc(x_1718);
if (lean_is_exclusive(x_1716)) {
 lean_ctor_release(x_1716, 0);
 lean_ctor_release(x_1716, 1);
 x_1719 = x_1716;
} else {
 lean_dec_ref(x_1716);
 x_1719 = lean_box(0);
}
x_1720 = lean_unbox(x_1717);
x_1721 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1720, x_1708);
if (x_1721 == 0)
{
uint8_t x_1722; uint8_t x_1723; uint8_t x_1724; lean_object* x_1725; lean_object* x_1726; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1722 = 1;
x_1723 = lean_unbox(x_1717);
lean_dec(x_1717);
x_1724 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1723, x_1722);
x_1725 = lean_box(x_1724);
if (lean_is_scalar(x_1719)) {
 x_1726 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1726 = x_1719;
}
lean_ctor_set(x_1726, 0, x_1725);
lean_ctor_set(x_1726, 1, x_1718);
return x_1726;
}
else
{
lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; uint8_t x_1734; 
lean_dec(x_1719);
lean_dec(x_1717);
x_1727 = lean_st_ref_get(x_6, x_1718);
x_1728 = lean_ctor_get(x_1727, 1);
lean_inc(x_1728);
lean_dec(x_1727);
x_1729 = lean_st_ref_get(x_4, x_1728);
x_1730 = lean_ctor_get(x_1729, 0);
lean_inc(x_1730);
x_1731 = lean_ctor_get(x_1729, 1);
lean_inc(x_1731);
if (lean_is_exclusive(x_1729)) {
 lean_ctor_release(x_1729, 0);
 lean_ctor_release(x_1729, 1);
 x_1732 = x_1729;
} else {
 lean_dec_ref(x_1729);
 x_1732 = lean_box(0);
}
x_1733 = lean_ctor_get(x_1730, 0);
lean_inc(x_1733);
lean_dec(x_1730);
lean_inc(x_1733);
x_1734 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1733, x_1);
if (x_1734 == 0)
{
uint8_t x_1735; 
x_1735 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1733, x_2);
if (x_1735 == 0)
{
lean_object* x_1736; lean_object* x_1766; uint8_t x_1767; 
x_1766 = lean_ctor_get(x_3, 0);
lean_inc(x_1766);
x_1767 = lean_ctor_get_uint8(x_1766, 4);
lean_dec(x_1766);
if (x_1767 == 0)
{
uint8_t x_1768; lean_object* x_1769; lean_object* x_1770; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1768 = 0;
x_1769 = lean_box(x_1768);
if (lean_is_scalar(x_1732)) {
 x_1770 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1770 = x_1732;
}
lean_ctor_set(x_1770, 0, x_1769);
lean_ctor_set(x_1770, 1, x_1731);
return x_1770;
}
else
{
uint8_t x_1771; 
x_1771 = l_Lean_Level_isMVar(x_1);
if (x_1771 == 0)
{
uint8_t x_1772; 
x_1772 = l_Lean_Level_isMVar(x_2);
if (x_1772 == 0)
{
uint8_t x_1773; lean_object* x_1774; lean_object* x_1775; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1773 = 0;
x_1774 = lean_box(x_1773);
if (lean_is_scalar(x_1732)) {
 x_1775 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1775 = x_1732;
}
lean_ctor_set(x_1775, 0, x_1774);
lean_ctor_set(x_1775, 1, x_1731);
return x_1775;
}
else
{
lean_object* x_1776; 
lean_dec(x_1732);
x_1776 = lean_box(0);
x_1736 = x_1776;
goto block_1765;
}
}
else
{
lean_object* x_1777; 
lean_dec(x_1732);
x_1777 = lean_box(0);
x_1736 = x_1777;
goto block_1765;
}
}
block_1765:
{
uint8_t x_1737; lean_object* x_1738; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; uint8_t x_1756; 
lean_dec(x_1736);
x_1753 = lean_st_ref_get(x_6, x_1731);
x_1754 = lean_ctor_get(x_1753, 0);
lean_inc(x_1754);
x_1755 = lean_ctor_get(x_1754, 3);
lean_inc(x_1755);
lean_dec(x_1754);
x_1756 = lean_ctor_get_uint8(x_1755, sizeof(void*)*1);
lean_dec(x_1755);
if (x_1756 == 0)
{
lean_object* x_1757; uint8_t x_1758; 
x_1757 = lean_ctor_get(x_1753, 1);
lean_inc(x_1757);
lean_dec(x_1753);
x_1758 = 0;
x_1737 = x_1758;
x_1738 = x_1757;
goto block_1752;
}
else
{
lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; uint8_t x_1764; 
x_1759 = lean_ctor_get(x_1753, 1);
lean_inc(x_1759);
lean_dec(x_1753);
x_1760 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1761 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1760, x_3, x_4, x_5, x_6, x_1759);
x_1762 = lean_ctor_get(x_1761, 0);
lean_inc(x_1762);
x_1763 = lean_ctor_get(x_1761, 1);
lean_inc(x_1763);
lean_dec(x_1761);
x_1764 = lean_unbox(x_1762);
lean_dec(x_1762);
x_1737 = x_1764;
x_1738 = x_1763;
goto block_1752;
}
block_1752:
{
if (x_1737 == 0)
{
lean_object* x_1739; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1739 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1738);
return x_1739;
}
else
{
lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; 
x_1740 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1740, 0, x_1);
x_1741 = l_Lean_KernelException_toMessageData___closed__15;
x_1742 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1742, 0, x_1741);
lean_ctor_set(x_1742, 1, x_1740);
x_1743 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1744 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1744, 0, x_1742);
lean_ctor_set(x_1744, 1, x_1743);
x_1745 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1745, 0, x_2);
x_1746 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1746, 0, x_1744);
lean_ctor_set(x_1746, 1, x_1745);
x_1747 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1747, 0, x_1746);
lean_ctor_set(x_1747, 1, x_1741);
x_1748 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1749 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1748, x_1747, x_3, x_4, x_5, x_6, x_1738);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1750 = lean_ctor_get(x_1749, 1);
lean_inc(x_1750);
lean_dec(x_1749);
x_1751 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1750);
return x_1751;
}
}
}
}
else
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; uint8_t x_1781; lean_object* x_1782; lean_object* x_1783; 
lean_dec(x_1732);
x_1778 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1731);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1779 = lean_ctor_get(x_1778, 1);
lean_inc(x_1779);
if (lean_is_exclusive(x_1778)) {
 lean_ctor_release(x_1778, 0);
 lean_ctor_release(x_1778, 1);
 x_1780 = x_1778;
} else {
 lean_dec_ref(x_1778);
 x_1780 = lean_box(0);
}
x_1781 = 1;
x_1782 = lean_box(x_1781);
if (lean_is_scalar(x_1780)) {
 x_1783 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1783 = x_1780;
}
lean_ctor_set(x_1783, 0, x_1782);
lean_ctor_set(x_1783, 1, x_1779);
return x_1783;
}
}
else
{
lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; uint8_t x_1787; lean_object* x_1788; lean_object* x_1789; 
lean_dec(x_1733);
lean_dec(x_1732);
x_1784 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1731);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1785 = lean_ctor_get(x_1784, 1);
lean_inc(x_1785);
if (lean_is_exclusive(x_1784)) {
 lean_ctor_release(x_1784, 0);
 lean_ctor_release(x_1784, 1);
 x_1786 = x_1784;
} else {
 lean_dec_ref(x_1784);
 x_1786 = lean_box(0);
}
x_1787 = 1;
x_1788 = lean_box(x_1787);
if (lean_is_scalar(x_1786)) {
 x_1789 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1789 = x_1786;
}
lean_ctor_set(x_1789, 0, x_1788);
lean_ctor_set(x_1789, 1, x_1785);
return x_1789;
}
}
}
else
{
lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1790 = lean_ctor_get(x_1716, 0);
lean_inc(x_1790);
x_1791 = lean_ctor_get(x_1716, 1);
lean_inc(x_1791);
if (lean_is_exclusive(x_1716)) {
 lean_ctor_release(x_1716, 0);
 lean_ctor_release(x_1716, 1);
 x_1792 = x_1716;
} else {
 lean_dec_ref(x_1716);
 x_1792 = lean_box(0);
}
if (lean_is_scalar(x_1792)) {
 x_1793 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1793 = x_1792;
}
lean_ctor_set(x_1793, 0, x_1790);
lean_ctor_set(x_1793, 1, x_1791);
return x_1793;
}
}
}
}
else
{
uint8_t x_1794; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1794 = !lean_is_exclusive(x_1483);
if (x_1794 == 0)
{
return x_1483;
}
else
{
lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; 
x_1795 = lean_ctor_get(x_1483, 0);
x_1796 = lean_ctor_get(x_1483, 1);
lean_inc(x_1796);
lean_inc(x_1795);
lean_dec(x_1483);
x_1797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1797, 0, x_1795);
lean_ctor_set(x_1797, 1, x_1796);
return x_1797;
}
}
}
}
}
block_1812:
{
if (x_1799 == 0)
{
x_1470 = x_1800;
goto block_1798;
}
else
{
lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; 
lean_inc(x_1);
x_1801 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1801, 0, x_1);
x_1802 = l_Lean_KernelException_toMessageData___closed__15;
x_1803 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1803, 0, x_1802);
lean_ctor_set(x_1803, 1, x_1801);
x_1804 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1805 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1805, 0, x_1803);
lean_ctor_set(x_1805, 1, x_1804);
lean_inc(x_2);
x_1806 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1806, 0, x_2);
x_1807 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1807, 0, x_1805);
lean_ctor_set(x_1807, 1, x_1806);
x_1808 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1808, 0, x_1807);
lean_ctor_set(x_1808, 1, x_1802);
x_1809 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_1810 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1809, x_1808, x_3, x_4, x_5, x_6, x_1800);
x_1811 = lean_ctor_get(x_1810, 1);
lean_inc(x_1811);
lean_dec(x_1810);
x_1470 = x_1811;
goto block_1798;
}
}
}
else
{
lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; uint8_t x_1828; lean_object* x_1829; lean_object* x_1830; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1825 = lean_unsigned_to_nat(0u);
x_1826 = l_Lean_Level_getOffsetAux(x_1, x_1825);
lean_dec(x_1);
x_1827 = l_Lean_Level_getOffsetAux(x_2, x_1825);
lean_dec(x_2);
x_1828 = lean_nat_dec_eq(x_1826, x_1827);
lean_dec(x_1827);
lean_dec(x_1826);
x_1829 = lean_box(x_1828);
x_1830 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1830, 0, x_1829);
lean_ctor_set(x_1830, 1, x_7);
return x_1830;
}
}
default: 
{
lean_object* x_1831; lean_object* x_1832; uint8_t x_1833; 
x_1831 = l_Lean_Level_getLevelOffset(x_1);
x_1832 = l_Lean_Level_getLevelOffset(x_2);
x_1833 = lean_level_eq(x_1831, x_1832);
lean_dec(x_1832);
lean_dec(x_1831);
if (x_1833 == 0)
{
lean_object* x_1834; uint8_t x_2163; lean_object* x_2164; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; uint8_t x_2180; 
x_2177 = lean_st_ref_get(x_6, x_7);
x_2178 = lean_ctor_get(x_2177, 0);
lean_inc(x_2178);
x_2179 = lean_ctor_get(x_2178, 3);
lean_inc(x_2179);
lean_dec(x_2178);
x_2180 = lean_ctor_get_uint8(x_2179, sizeof(void*)*1);
lean_dec(x_2179);
if (x_2180 == 0)
{
lean_object* x_2181; uint8_t x_2182; 
x_2181 = lean_ctor_get(x_2177, 1);
lean_inc(x_2181);
lean_dec(x_2177);
x_2182 = 0;
x_2163 = x_2182;
x_2164 = x_2181;
goto block_2176;
}
else
{
lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; uint8_t x_2188; 
x_2183 = lean_ctor_get(x_2177, 1);
lean_inc(x_2183);
lean_dec(x_2177);
x_2184 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_2185 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2184, x_3, x_4, x_5, x_6, x_2183);
x_2186 = lean_ctor_get(x_2185, 0);
lean_inc(x_2186);
x_2187 = lean_ctor_get(x_2185, 1);
lean_inc(x_2187);
lean_dec(x_2185);
x_2188 = lean_unbox(x_2186);
lean_dec(x_2186);
x_2163 = x_2188;
x_2164 = x_2187;
goto block_2176;
}
block_2162:
{
lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; uint8_t x_1843; 
lean_inc(x_1);
x_1835 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_1834);
x_1836 = lean_ctor_get(x_1835, 0);
lean_inc(x_1836);
x_1837 = lean_ctor_get(x_1835, 1);
lean_inc(x_1837);
lean_dec(x_1835);
x_1838 = l_Lean_Level_normalize(x_1836);
lean_dec(x_1836);
lean_inc(x_2);
x_1839 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_2, x_3, x_4, x_5, x_6, x_1837);
x_1840 = lean_ctor_get(x_1839, 0);
lean_inc(x_1840);
x_1841 = lean_ctor_get(x_1839, 1);
lean_inc(x_1841);
lean_dec(x_1839);
x_1842 = l_Lean_Level_normalize(x_1840);
lean_dec(x_1840);
x_1843 = lean_level_eq(x_1, x_1838);
if (x_1843 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_1838;
x_2 = x_1842;
x_7 = x_1841;
goto _start;
}
else
{
uint8_t x_1845; 
x_1845 = lean_level_eq(x_2, x_1842);
if (x_1845 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_1838;
x_2 = x_1842;
x_7 = x_1841;
goto _start;
}
else
{
lean_object* x_1847; 
lean_dec(x_1842);
lean_dec(x_1838);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_1847 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_1841);
if (lean_obj_tag(x_1847) == 0)
{
uint8_t x_1848; 
x_1848 = !lean_is_exclusive(x_1847);
if (x_1848 == 0)
{
lean_object* x_1849; lean_object* x_1850; uint8_t x_1851; uint8_t x_1852; uint8_t x_1853; 
x_1849 = lean_ctor_get(x_1847, 0);
x_1850 = lean_ctor_get(x_1847, 1);
x_1851 = 2;
x_1852 = lean_unbox(x_1849);
x_1853 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1852, x_1851);
if (x_1853 == 0)
{
uint8_t x_1854; uint8_t x_1855; uint8_t x_1856; lean_object* x_1857; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1854 = 1;
x_1855 = lean_unbox(x_1849);
lean_dec(x_1849);
x_1856 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1855, x_1854);
x_1857 = lean_box(x_1856);
lean_ctor_set(x_1847, 0, x_1857);
return x_1847;
}
else
{
lean_object* x_1858; 
lean_free_object(x_1847);
lean_dec(x_1849);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_1858 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_1850);
if (lean_obj_tag(x_1858) == 0)
{
uint8_t x_1859; 
x_1859 = !lean_is_exclusive(x_1858);
if (x_1859 == 0)
{
lean_object* x_1860; lean_object* x_1861; uint8_t x_1862; uint8_t x_1863; 
x_1860 = lean_ctor_get(x_1858, 0);
x_1861 = lean_ctor_get(x_1858, 1);
x_1862 = lean_unbox(x_1860);
x_1863 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1862, x_1851);
if (x_1863 == 0)
{
uint8_t x_1864; uint8_t x_1865; uint8_t x_1866; lean_object* x_1867; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1864 = 1;
x_1865 = lean_unbox(x_1860);
lean_dec(x_1860);
x_1866 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1865, x_1864);
x_1867 = lean_box(x_1866);
lean_ctor_set(x_1858, 0, x_1867);
return x_1858;
}
else
{
lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; uint8_t x_1871; 
lean_free_object(x_1858);
lean_dec(x_1860);
x_1868 = lean_st_ref_get(x_6, x_1861);
x_1869 = lean_ctor_get(x_1868, 1);
lean_inc(x_1869);
lean_dec(x_1868);
x_1870 = lean_st_ref_get(x_4, x_1869);
x_1871 = !lean_is_exclusive(x_1870);
if (x_1871 == 0)
{
lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; uint8_t x_1875; 
x_1872 = lean_ctor_get(x_1870, 0);
x_1873 = lean_ctor_get(x_1870, 1);
x_1874 = lean_ctor_get(x_1872, 0);
lean_inc(x_1874);
lean_dec(x_1872);
lean_inc(x_1874);
x_1875 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1874, x_1);
if (x_1875 == 0)
{
uint8_t x_1876; 
x_1876 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1874, x_2);
if (x_1876 == 0)
{
lean_object* x_1877; lean_object* x_1907; uint8_t x_1908; 
x_1907 = lean_ctor_get(x_3, 0);
lean_inc(x_1907);
x_1908 = lean_ctor_get_uint8(x_1907, 4);
lean_dec(x_1907);
if (x_1908 == 0)
{
uint8_t x_1909; lean_object* x_1910; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1909 = 0;
x_1910 = lean_box(x_1909);
lean_ctor_set(x_1870, 0, x_1910);
return x_1870;
}
else
{
uint8_t x_1911; 
x_1911 = l_Lean_Level_isMVar(x_1);
if (x_1911 == 0)
{
uint8_t x_1912; 
x_1912 = l_Lean_Level_isMVar(x_2);
if (x_1912 == 0)
{
uint8_t x_1913; lean_object* x_1914; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1913 = 0;
x_1914 = lean_box(x_1913);
lean_ctor_set(x_1870, 0, x_1914);
return x_1870;
}
else
{
lean_object* x_1915; 
lean_free_object(x_1870);
x_1915 = lean_box(0);
x_1877 = x_1915;
goto block_1906;
}
}
else
{
lean_object* x_1916; 
lean_free_object(x_1870);
x_1916 = lean_box(0);
x_1877 = x_1916;
goto block_1906;
}
}
block_1906:
{
uint8_t x_1878; lean_object* x_1879; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; uint8_t x_1897; 
lean_dec(x_1877);
x_1894 = lean_st_ref_get(x_6, x_1873);
x_1895 = lean_ctor_get(x_1894, 0);
lean_inc(x_1895);
x_1896 = lean_ctor_get(x_1895, 3);
lean_inc(x_1896);
lean_dec(x_1895);
x_1897 = lean_ctor_get_uint8(x_1896, sizeof(void*)*1);
lean_dec(x_1896);
if (x_1897 == 0)
{
lean_object* x_1898; uint8_t x_1899; 
x_1898 = lean_ctor_get(x_1894, 1);
lean_inc(x_1898);
lean_dec(x_1894);
x_1899 = 0;
x_1878 = x_1899;
x_1879 = x_1898;
goto block_1893;
}
else
{
lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; uint8_t x_1905; 
x_1900 = lean_ctor_get(x_1894, 1);
lean_inc(x_1900);
lean_dec(x_1894);
x_1901 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1902 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1901, x_3, x_4, x_5, x_6, x_1900);
x_1903 = lean_ctor_get(x_1902, 0);
lean_inc(x_1903);
x_1904 = lean_ctor_get(x_1902, 1);
lean_inc(x_1904);
lean_dec(x_1902);
x_1905 = lean_unbox(x_1903);
lean_dec(x_1903);
x_1878 = x_1905;
x_1879 = x_1904;
goto block_1893;
}
block_1893:
{
if (x_1878 == 0)
{
lean_object* x_1880; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1880 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1879);
return x_1880;
}
else
{
lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; 
x_1881 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1881, 0, x_1);
x_1882 = l_Lean_KernelException_toMessageData___closed__15;
x_1883 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1883, 0, x_1882);
lean_ctor_set(x_1883, 1, x_1881);
x_1884 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1885 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1885, 0, x_1883);
lean_ctor_set(x_1885, 1, x_1884);
x_1886 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1886, 0, x_2);
x_1887 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1887, 0, x_1885);
lean_ctor_set(x_1887, 1, x_1886);
x_1888 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1888, 0, x_1887);
lean_ctor_set(x_1888, 1, x_1882);
x_1889 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1890 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1889, x_1888, x_3, x_4, x_5, x_6, x_1879);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1891 = lean_ctor_get(x_1890, 1);
lean_inc(x_1891);
lean_dec(x_1890);
x_1892 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1891);
return x_1892;
}
}
}
}
else
{
lean_object* x_1917; uint8_t x_1918; 
lean_free_object(x_1870);
x_1917 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1873);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1918 = !lean_is_exclusive(x_1917);
if (x_1918 == 0)
{
lean_object* x_1919; uint8_t x_1920; lean_object* x_1921; 
x_1919 = lean_ctor_get(x_1917, 0);
lean_dec(x_1919);
x_1920 = 1;
x_1921 = lean_box(x_1920);
lean_ctor_set(x_1917, 0, x_1921);
return x_1917;
}
else
{
lean_object* x_1922; uint8_t x_1923; lean_object* x_1924; lean_object* x_1925; 
x_1922 = lean_ctor_get(x_1917, 1);
lean_inc(x_1922);
lean_dec(x_1917);
x_1923 = 1;
x_1924 = lean_box(x_1923);
x_1925 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1925, 0, x_1924);
lean_ctor_set(x_1925, 1, x_1922);
return x_1925;
}
}
}
else
{
lean_object* x_1926; uint8_t x_1927; 
lean_dec(x_1874);
lean_free_object(x_1870);
x_1926 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1873);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1927 = !lean_is_exclusive(x_1926);
if (x_1927 == 0)
{
lean_object* x_1928; uint8_t x_1929; lean_object* x_1930; 
x_1928 = lean_ctor_get(x_1926, 0);
lean_dec(x_1928);
x_1929 = 1;
x_1930 = lean_box(x_1929);
lean_ctor_set(x_1926, 0, x_1930);
return x_1926;
}
else
{
lean_object* x_1931; uint8_t x_1932; lean_object* x_1933; lean_object* x_1934; 
x_1931 = lean_ctor_get(x_1926, 1);
lean_inc(x_1931);
lean_dec(x_1926);
x_1932 = 1;
x_1933 = lean_box(x_1932);
x_1934 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1934, 0, x_1933);
lean_ctor_set(x_1934, 1, x_1931);
return x_1934;
}
}
}
else
{
lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; uint8_t x_1938; 
x_1935 = lean_ctor_get(x_1870, 0);
x_1936 = lean_ctor_get(x_1870, 1);
lean_inc(x_1936);
lean_inc(x_1935);
lean_dec(x_1870);
x_1937 = lean_ctor_get(x_1935, 0);
lean_inc(x_1937);
lean_dec(x_1935);
lean_inc(x_1937);
x_1938 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1937, x_1);
if (x_1938 == 0)
{
uint8_t x_1939; 
x_1939 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1937, x_2);
if (x_1939 == 0)
{
lean_object* x_1940; lean_object* x_1970; uint8_t x_1971; 
x_1970 = lean_ctor_get(x_3, 0);
lean_inc(x_1970);
x_1971 = lean_ctor_get_uint8(x_1970, 4);
lean_dec(x_1970);
if (x_1971 == 0)
{
uint8_t x_1972; lean_object* x_1973; lean_object* x_1974; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1972 = 0;
x_1973 = lean_box(x_1972);
x_1974 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1974, 0, x_1973);
lean_ctor_set(x_1974, 1, x_1936);
return x_1974;
}
else
{
uint8_t x_1975; 
x_1975 = l_Lean_Level_isMVar(x_1);
if (x_1975 == 0)
{
uint8_t x_1976; 
x_1976 = l_Lean_Level_isMVar(x_2);
if (x_1976 == 0)
{
uint8_t x_1977; lean_object* x_1978; lean_object* x_1979; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1977 = 0;
x_1978 = lean_box(x_1977);
x_1979 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1979, 0, x_1978);
lean_ctor_set(x_1979, 1, x_1936);
return x_1979;
}
else
{
lean_object* x_1980; 
x_1980 = lean_box(0);
x_1940 = x_1980;
goto block_1969;
}
}
else
{
lean_object* x_1981; 
x_1981 = lean_box(0);
x_1940 = x_1981;
goto block_1969;
}
}
block_1969:
{
uint8_t x_1941; lean_object* x_1942; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; uint8_t x_1960; 
lean_dec(x_1940);
x_1957 = lean_st_ref_get(x_6, x_1936);
x_1958 = lean_ctor_get(x_1957, 0);
lean_inc(x_1958);
x_1959 = lean_ctor_get(x_1958, 3);
lean_inc(x_1959);
lean_dec(x_1958);
x_1960 = lean_ctor_get_uint8(x_1959, sizeof(void*)*1);
lean_dec(x_1959);
if (x_1960 == 0)
{
lean_object* x_1961; uint8_t x_1962; 
x_1961 = lean_ctor_get(x_1957, 1);
lean_inc(x_1961);
lean_dec(x_1957);
x_1962 = 0;
x_1941 = x_1962;
x_1942 = x_1961;
goto block_1956;
}
else
{
lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; uint8_t x_1968; 
x_1963 = lean_ctor_get(x_1957, 1);
lean_inc(x_1963);
lean_dec(x_1957);
x_1964 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1965 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1964, x_3, x_4, x_5, x_6, x_1963);
x_1966 = lean_ctor_get(x_1965, 0);
lean_inc(x_1966);
x_1967 = lean_ctor_get(x_1965, 1);
lean_inc(x_1967);
lean_dec(x_1965);
x_1968 = lean_unbox(x_1966);
lean_dec(x_1966);
x_1941 = x_1968;
x_1942 = x_1967;
goto block_1956;
}
block_1956:
{
if (x_1941 == 0)
{
lean_object* x_1943; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1943 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1942);
return x_1943;
}
else
{
lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; 
x_1944 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1944, 0, x_1);
x_1945 = l_Lean_KernelException_toMessageData___closed__15;
x_1946 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1946, 0, x_1945);
lean_ctor_set(x_1946, 1, x_1944);
x_1947 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_1948 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1948, 0, x_1946);
lean_ctor_set(x_1948, 1, x_1947);
x_1949 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1949, 0, x_2);
x_1950 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1950, 0, x_1948);
lean_ctor_set(x_1950, 1, x_1949);
x_1951 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1951, 0, x_1950);
lean_ctor_set(x_1951, 1, x_1945);
x_1952 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_1953 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1952, x_1951, x_3, x_4, x_5, x_6, x_1942);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1954 = lean_ctor_get(x_1953, 1);
lean_inc(x_1954);
lean_dec(x_1953);
x_1955 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_1954);
return x_1955;
}
}
}
}
else
{
lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; uint8_t x_1985; lean_object* x_1986; lean_object* x_1987; 
x_1982 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1936);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1983 = lean_ctor_get(x_1982, 1);
lean_inc(x_1983);
if (lean_is_exclusive(x_1982)) {
 lean_ctor_release(x_1982, 0);
 lean_ctor_release(x_1982, 1);
 x_1984 = x_1982;
} else {
 lean_dec_ref(x_1982);
 x_1984 = lean_box(0);
}
x_1985 = 1;
x_1986 = lean_box(x_1985);
if (lean_is_scalar(x_1984)) {
 x_1987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1987 = x_1984;
}
lean_ctor_set(x_1987, 0, x_1986);
lean_ctor_set(x_1987, 1, x_1983);
return x_1987;
}
}
else
{
lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; uint8_t x_1991; lean_object* x_1992; lean_object* x_1993; 
lean_dec(x_1937);
x_1988 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_1936);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1989 = lean_ctor_get(x_1988, 1);
lean_inc(x_1989);
if (lean_is_exclusive(x_1988)) {
 lean_ctor_release(x_1988, 0);
 lean_ctor_release(x_1988, 1);
 x_1990 = x_1988;
} else {
 lean_dec_ref(x_1988);
 x_1990 = lean_box(0);
}
x_1991 = 1;
x_1992 = lean_box(x_1991);
if (lean_is_scalar(x_1990)) {
 x_1993 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1993 = x_1990;
}
lean_ctor_set(x_1993, 0, x_1992);
lean_ctor_set(x_1993, 1, x_1989);
return x_1993;
}
}
}
}
else
{
lean_object* x_1994; lean_object* x_1995; uint8_t x_1996; uint8_t x_1997; 
x_1994 = lean_ctor_get(x_1858, 0);
x_1995 = lean_ctor_get(x_1858, 1);
lean_inc(x_1995);
lean_inc(x_1994);
lean_dec(x_1858);
x_1996 = lean_unbox(x_1994);
x_1997 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1996, x_1851);
if (x_1997 == 0)
{
uint8_t x_1998; uint8_t x_1999; uint8_t x_2000; lean_object* x_2001; lean_object* x_2002; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1998 = 1;
x_1999 = lean_unbox(x_1994);
lean_dec(x_1994);
x_2000 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_1999, x_1998);
x_2001 = lean_box(x_2000);
x_2002 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2002, 0, x_2001);
lean_ctor_set(x_2002, 1, x_1995);
return x_2002;
}
else
{
lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; uint8_t x_2010; 
lean_dec(x_1994);
x_2003 = lean_st_ref_get(x_6, x_1995);
x_2004 = lean_ctor_get(x_2003, 1);
lean_inc(x_2004);
lean_dec(x_2003);
x_2005 = lean_st_ref_get(x_4, x_2004);
x_2006 = lean_ctor_get(x_2005, 0);
lean_inc(x_2006);
x_2007 = lean_ctor_get(x_2005, 1);
lean_inc(x_2007);
if (lean_is_exclusive(x_2005)) {
 lean_ctor_release(x_2005, 0);
 lean_ctor_release(x_2005, 1);
 x_2008 = x_2005;
} else {
 lean_dec_ref(x_2005);
 x_2008 = lean_box(0);
}
x_2009 = lean_ctor_get(x_2006, 0);
lean_inc(x_2009);
lean_dec(x_2006);
lean_inc(x_2009);
x_2010 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2009, x_1);
if (x_2010 == 0)
{
uint8_t x_2011; 
x_2011 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2009, x_2);
if (x_2011 == 0)
{
lean_object* x_2012; lean_object* x_2042; uint8_t x_2043; 
x_2042 = lean_ctor_get(x_3, 0);
lean_inc(x_2042);
x_2043 = lean_ctor_get_uint8(x_2042, 4);
lean_dec(x_2042);
if (x_2043 == 0)
{
uint8_t x_2044; lean_object* x_2045; lean_object* x_2046; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2044 = 0;
x_2045 = lean_box(x_2044);
if (lean_is_scalar(x_2008)) {
 x_2046 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2046 = x_2008;
}
lean_ctor_set(x_2046, 0, x_2045);
lean_ctor_set(x_2046, 1, x_2007);
return x_2046;
}
else
{
uint8_t x_2047; 
x_2047 = l_Lean_Level_isMVar(x_1);
if (x_2047 == 0)
{
uint8_t x_2048; 
x_2048 = l_Lean_Level_isMVar(x_2);
if (x_2048 == 0)
{
uint8_t x_2049; lean_object* x_2050; lean_object* x_2051; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2049 = 0;
x_2050 = lean_box(x_2049);
if (lean_is_scalar(x_2008)) {
 x_2051 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2051 = x_2008;
}
lean_ctor_set(x_2051, 0, x_2050);
lean_ctor_set(x_2051, 1, x_2007);
return x_2051;
}
else
{
lean_object* x_2052; 
lean_dec(x_2008);
x_2052 = lean_box(0);
x_2012 = x_2052;
goto block_2041;
}
}
else
{
lean_object* x_2053; 
lean_dec(x_2008);
x_2053 = lean_box(0);
x_2012 = x_2053;
goto block_2041;
}
}
block_2041:
{
uint8_t x_2013; lean_object* x_2014; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; uint8_t x_2032; 
lean_dec(x_2012);
x_2029 = lean_st_ref_get(x_6, x_2007);
x_2030 = lean_ctor_get(x_2029, 0);
lean_inc(x_2030);
x_2031 = lean_ctor_get(x_2030, 3);
lean_inc(x_2031);
lean_dec(x_2030);
x_2032 = lean_ctor_get_uint8(x_2031, sizeof(void*)*1);
lean_dec(x_2031);
if (x_2032 == 0)
{
lean_object* x_2033; uint8_t x_2034; 
x_2033 = lean_ctor_get(x_2029, 1);
lean_inc(x_2033);
lean_dec(x_2029);
x_2034 = 0;
x_2013 = x_2034;
x_2014 = x_2033;
goto block_2028;
}
else
{
lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; uint8_t x_2040; 
x_2035 = lean_ctor_get(x_2029, 1);
lean_inc(x_2035);
lean_dec(x_2029);
x_2036 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2037 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2036, x_3, x_4, x_5, x_6, x_2035);
x_2038 = lean_ctor_get(x_2037, 0);
lean_inc(x_2038);
x_2039 = lean_ctor_get(x_2037, 1);
lean_inc(x_2039);
lean_dec(x_2037);
x_2040 = lean_unbox(x_2038);
lean_dec(x_2038);
x_2013 = x_2040;
x_2014 = x_2039;
goto block_2028;
}
block_2028:
{
if (x_2013 == 0)
{
lean_object* x_2015; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2015 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2014);
return x_2015;
}
else
{
lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; 
x_2016 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2016, 0, x_1);
x_2017 = l_Lean_KernelException_toMessageData___closed__15;
x_2018 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2018, 0, x_2017);
lean_ctor_set(x_2018, 1, x_2016);
x_2019 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2020 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2020, 0, x_2018);
lean_ctor_set(x_2020, 1, x_2019);
x_2021 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2021, 0, x_2);
x_2022 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2022, 0, x_2020);
lean_ctor_set(x_2022, 1, x_2021);
x_2023 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2023, 0, x_2022);
lean_ctor_set(x_2023, 1, x_2017);
x_2024 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2025 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2024, x_2023, x_3, x_4, x_5, x_6, x_2014);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2026 = lean_ctor_get(x_2025, 1);
lean_inc(x_2026);
lean_dec(x_2025);
x_2027 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2026);
return x_2027;
}
}
}
}
else
{
lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; uint8_t x_2057; lean_object* x_2058; lean_object* x_2059; 
lean_dec(x_2008);
x_2054 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2007);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2055 = lean_ctor_get(x_2054, 1);
lean_inc(x_2055);
if (lean_is_exclusive(x_2054)) {
 lean_ctor_release(x_2054, 0);
 lean_ctor_release(x_2054, 1);
 x_2056 = x_2054;
} else {
 lean_dec_ref(x_2054);
 x_2056 = lean_box(0);
}
x_2057 = 1;
x_2058 = lean_box(x_2057);
if (lean_is_scalar(x_2056)) {
 x_2059 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2059 = x_2056;
}
lean_ctor_set(x_2059, 0, x_2058);
lean_ctor_set(x_2059, 1, x_2055);
return x_2059;
}
}
else
{
lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; uint8_t x_2063; lean_object* x_2064; lean_object* x_2065; 
lean_dec(x_2009);
lean_dec(x_2008);
x_2060 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2007);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2061 = lean_ctor_get(x_2060, 1);
lean_inc(x_2061);
if (lean_is_exclusive(x_2060)) {
 lean_ctor_release(x_2060, 0);
 lean_ctor_release(x_2060, 1);
 x_2062 = x_2060;
} else {
 lean_dec_ref(x_2060);
 x_2062 = lean_box(0);
}
x_2063 = 1;
x_2064 = lean_box(x_2063);
if (lean_is_scalar(x_2062)) {
 x_2065 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2065 = x_2062;
}
lean_ctor_set(x_2065, 0, x_2064);
lean_ctor_set(x_2065, 1, x_2061);
return x_2065;
}
}
}
}
else
{
uint8_t x_2066; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2066 = !lean_is_exclusive(x_1858);
if (x_2066 == 0)
{
return x_1858;
}
else
{
lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; 
x_2067 = lean_ctor_get(x_1858, 0);
x_2068 = lean_ctor_get(x_1858, 1);
lean_inc(x_2068);
lean_inc(x_2067);
lean_dec(x_1858);
x_2069 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2069, 0, x_2067);
lean_ctor_set(x_2069, 1, x_2068);
return x_2069;
}
}
}
}
else
{
lean_object* x_2070; lean_object* x_2071; uint8_t x_2072; uint8_t x_2073; uint8_t x_2074; 
x_2070 = lean_ctor_get(x_1847, 0);
x_2071 = lean_ctor_get(x_1847, 1);
lean_inc(x_2071);
lean_inc(x_2070);
lean_dec(x_1847);
x_2072 = 2;
x_2073 = lean_unbox(x_2070);
x_2074 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2073, x_2072);
if (x_2074 == 0)
{
uint8_t x_2075; uint8_t x_2076; uint8_t x_2077; lean_object* x_2078; lean_object* x_2079; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2075 = 1;
x_2076 = lean_unbox(x_2070);
lean_dec(x_2070);
x_2077 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2076, x_2075);
x_2078 = lean_box(x_2077);
x_2079 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2079, 0, x_2078);
lean_ctor_set(x_2079, 1, x_2071);
return x_2079;
}
else
{
lean_object* x_2080; 
lean_dec(x_2070);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_2080 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_2071);
if (lean_obj_tag(x_2080) == 0)
{
lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; uint8_t x_2084; uint8_t x_2085; 
x_2081 = lean_ctor_get(x_2080, 0);
lean_inc(x_2081);
x_2082 = lean_ctor_get(x_2080, 1);
lean_inc(x_2082);
if (lean_is_exclusive(x_2080)) {
 lean_ctor_release(x_2080, 0);
 lean_ctor_release(x_2080, 1);
 x_2083 = x_2080;
} else {
 lean_dec_ref(x_2080);
 x_2083 = lean_box(0);
}
x_2084 = lean_unbox(x_2081);
x_2085 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2084, x_2072);
if (x_2085 == 0)
{
uint8_t x_2086; uint8_t x_2087; uint8_t x_2088; lean_object* x_2089; lean_object* x_2090; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2086 = 1;
x_2087 = lean_unbox(x_2081);
lean_dec(x_2081);
x_2088 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2087, x_2086);
x_2089 = lean_box(x_2088);
if (lean_is_scalar(x_2083)) {
 x_2090 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2090 = x_2083;
}
lean_ctor_set(x_2090, 0, x_2089);
lean_ctor_set(x_2090, 1, x_2082);
return x_2090;
}
else
{
lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; uint8_t x_2098; 
lean_dec(x_2083);
lean_dec(x_2081);
x_2091 = lean_st_ref_get(x_6, x_2082);
x_2092 = lean_ctor_get(x_2091, 1);
lean_inc(x_2092);
lean_dec(x_2091);
x_2093 = lean_st_ref_get(x_4, x_2092);
x_2094 = lean_ctor_get(x_2093, 0);
lean_inc(x_2094);
x_2095 = lean_ctor_get(x_2093, 1);
lean_inc(x_2095);
if (lean_is_exclusive(x_2093)) {
 lean_ctor_release(x_2093, 0);
 lean_ctor_release(x_2093, 1);
 x_2096 = x_2093;
} else {
 lean_dec_ref(x_2093);
 x_2096 = lean_box(0);
}
x_2097 = lean_ctor_get(x_2094, 0);
lean_inc(x_2097);
lean_dec(x_2094);
lean_inc(x_2097);
x_2098 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2097, x_1);
if (x_2098 == 0)
{
uint8_t x_2099; 
x_2099 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2097, x_2);
if (x_2099 == 0)
{
lean_object* x_2100; lean_object* x_2130; uint8_t x_2131; 
x_2130 = lean_ctor_get(x_3, 0);
lean_inc(x_2130);
x_2131 = lean_ctor_get_uint8(x_2130, 4);
lean_dec(x_2130);
if (x_2131 == 0)
{
uint8_t x_2132; lean_object* x_2133; lean_object* x_2134; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2132 = 0;
x_2133 = lean_box(x_2132);
if (lean_is_scalar(x_2096)) {
 x_2134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2134 = x_2096;
}
lean_ctor_set(x_2134, 0, x_2133);
lean_ctor_set(x_2134, 1, x_2095);
return x_2134;
}
else
{
uint8_t x_2135; 
x_2135 = l_Lean_Level_isMVar(x_1);
if (x_2135 == 0)
{
uint8_t x_2136; 
x_2136 = l_Lean_Level_isMVar(x_2);
if (x_2136 == 0)
{
uint8_t x_2137; lean_object* x_2138; lean_object* x_2139; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2137 = 0;
x_2138 = lean_box(x_2137);
if (lean_is_scalar(x_2096)) {
 x_2139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2139 = x_2096;
}
lean_ctor_set(x_2139, 0, x_2138);
lean_ctor_set(x_2139, 1, x_2095);
return x_2139;
}
else
{
lean_object* x_2140; 
lean_dec(x_2096);
x_2140 = lean_box(0);
x_2100 = x_2140;
goto block_2129;
}
}
else
{
lean_object* x_2141; 
lean_dec(x_2096);
x_2141 = lean_box(0);
x_2100 = x_2141;
goto block_2129;
}
}
block_2129:
{
uint8_t x_2101; lean_object* x_2102; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; uint8_t x_2120; 
lean_dec(x_2100);
x_2117 = lean_st_ref_get(x_6, x_2095);
x_2118 = lean_ctor_get(x_2117, 0);
lean_inc(x_2118);
x_2119 = lean_ctor_get(x_2118, 3);
lean_inc(x_2119);
lean_dec(x_2118);
x_2120 = lean_ctor_get_uint8(x_2119, sizeof(void*)*1);
lean_dec(x_2119);
if (x_2120 == 0)
{
lean_object* x_2121; uint8_t x_2122; 
x_2121 = lean_ctor_get(x_2117, 1);
lean_inc(x_2121);
lean_dec(x_2117);
x_2122 = 0;
x_2101 = x_2122;
x_2102 = x_2121;
goto block_2116;
}
else
{
lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; uint8_t x_2128; 
x_2123 = lean_ctor_get(x_2117, 1);
lean_inc(x_2123);
lean_dec(x_2117);
x_2124 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2125 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2124, x_3, x_4, x_5, x_6, x_2123);
x_2126 = lean_ctor_get(x_2125, 0);
lean_inc(x_2126);
x_2127 = lean_ctor_get(x_2125, 1);
lean_inc(x_2127);
lean_dec(x_2125);
x_2128 = lean_unbox(x_2126);
lean_dec(x_2126);
x_2101 = x_2128;
x_2102 = x_2127;
goto block_2116;
}
block_2116:
{
if (x_2101 == 0)
{
lean_object* x_2103; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2103 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2102);
return x_2103;
}
else
{
lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; 
x_2104 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2104, 0, x_1);
x_2105 = l_Lean_KernelException_toMessageData___closed__15;
x_2106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2106, 0, x_2105);
lean_ctor_set(x_2106, 1, x_2104);
x_2107 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2108, 0, x_2106);
lean_ctor_set(x_2108, 1, x_2107);
x_2109 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2109, 0, x_2);
x_2110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2110, 0, x_2108);
lean_ctor_set(x_2110, 1, x_2109);
x_2111 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2111, 0, x_2110);
lean_ctor_set(x_2111, 1, x_2105);
x_2112 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2113 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2112, x_2111, x_3, x_4, x_5, x_6, x_2102);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2114 = lean_ctor_get(x_2113, 1);
lean_inc(x_2114);
lean_dec(x_2113);
x_2115 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2114);
return x_2115;
}
}
}
}
else
{
lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; uint8_t x_2145; lean_object* x_2146; lean_object* x_2147; 
lean_dec(x_2096);
x_2142 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2095);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2143 = lean_ctor_get(x_2142, 1);
lean_inc(x_2143);
if (lean_is_exclusive(x_2142)) {
 lean_ctor_release(x_2142, 0);
 lean_ctor_release(x_2142, 1);
 x_2144 = x_2142;
} else {
 lean_dec_ref(x_2142);
 x_2144 = lean_box(0);
}
x_2145 = 1;
x_2146 = lean_box(x_2145);
if (lean_is_scalar(x_2144)) {
 x_2147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2147 = x_2144;
}
lean_ctor_set(x_2147, 0, x_2146);
lean_ctor_set(x_2147, 1, x_2143);
return x_2147;
}
}
else
{
lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; uint8_t x_2151; lean_object* x_2152; lean_object* x_2153; 
lean_dec(x_2097);
lean_dec(x_2096);
x_2148 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2095);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2149 = lean_ctor_get(x_2148, 1);
lean_inc(x_2149);
if (lean_is_exclusive(x_2148)) {
 lean_ctor_release(x_2148, 0);
 lean_ctor_release(x_2148, 1);
 x_2150 = x_2148;
} else {
 lean_dec_ref(x_2148);
 x_2150 = lean_box(0);
}
x_2151 = 1;
x_2152 = lean_box(x_2151);
if (lean_is_scalar(x_2150)) {
 x_2153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2153 = x_2150;
}
lean_ctor_set(x_2153, 0, x_2152);
lean_ctor_set(x_2153, 1, x_2149);
return x_2153;
}
}
}
else
{
lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2154 = lean_ctor_get(x_2080, 0);
lean_inc(x_2154);
x_2155 = lean_ctor_get(x_2080, 1);
lean_inc(x_2155);
if (lean_is_exclusive(x_2080)) {
 lean_ctor_release(x_2080, 0);
 lean_ctor_release(x_2080, 1);
 x_2156 = x_2080;
} else {
 lean_dec_ref(x_2080);
 x_2156 = lean_box(0);
}
if (lean_is_scalar(x_2156)) {
 x_2157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2157 = x_2156;
}
lean_ctor_set(x_2157, 0, x_2154);
lean_ctor_set(x_2157, 1, x_2155);
return x_2157;
}
}
}
}
else
{
uint8_t x_2158; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2158 = !lean_is_exclusive(x_1847);
if (x_2158 == 0)
{
return x_1847;
}
else
{
lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; 
x_2159 = lean_ctor_get(x_1847, 0);
x_2160 = lean_ctor_get(x_1847, 1);
lean_inc(x_2160);
lean_inc(x_2159);
lean_dec(x_1847);
x_2161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2161, 0, x_2159);
lean_ctor_set(x_2161, 1, x_2160);
return x_2161;
}
}
}
}
}
block_2176:
{
if (x_2163 == 0)
{
x_1834 = x_2164;
goto block_2162;
}
else
{
lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; 
lean_inc(x_1);
x_2165 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2165, 0, x_1);
x_2166 = l_Lean_KernelException_toMessageData___closed__15;
x_2167 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2167, 0, x_2166);
lean_ctor_set(x_2167, 1, x_2165);
x_2168 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2169 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2169, 0, x_2167);
lean_ctor_set(x_2169, 1, x_2168);
lean_inc(x_2);
x_2170 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2170, 0, x_2);
x_2171 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2171, 0, x_2169);
lean_ctor_set(x_2171, 1, x_2170);
x_2172 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2172, 0, x_2171);
lean_ctor_set(x_2172, 1, x_2166);
x_2173 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_2174 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2173, x_2172, x_3, x_4, x_5, x_6, x_2164);
x_2175 = lean_ctor_get(x_2174, 1);
lean_inc(x_2175);
lean_dec(x_2174);
x_1834 = x_2175;
goto block_2162;
}
}
}
else
{
lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; uint8_t x_2192; lean_object* x_2193; lean_object* x_2194; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2189 = lean_unsigned_to_nat(0u);
x_2190 = l_Lean_Level_getOffsetAux(x_1, x_2189);
lean_dec(x_1);
x_2191 = l_Lean_Level_getOffsetAux(x_2, x_2189);
lean_dec(x_2);
x_2192 = lean_nat_dec_eq(x_2190, x_2191);
lean_dec(x_2191);
lean_dec(x_2190);
x_2193 = lean_box(x_2192);
x_2194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2194, 0, x_2193);
lean_ctor_set(x_2194, 1, x_7);
return x_2194;
}
}
}
}
case 2:
{
lean_object* x_2195; lean_object* x_2196; uint8_t x_2197; 
x_2195 = l_Lean_Level_getLevelOffset(x_1);
x_2196 = l_Lean_Level_getLevelOffset(x_2);
x_2197 = lean_level_eq(x_2195, x_2196);
lean_dec(x_2196);
lean_dec(x_2195);
if (x_2197 == 0)
{
lean_object* x_2198; uint8_t x_2527; lean_object* x_2528; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; uint8_t x_2544; 
x_2541 = lean_st_ref_get(x_6, x_7);
x_2542 = lean_ctor_get(x_2541, 0);
lean_inc(x_2542);
x_2543 = lean_ctor_get(x_2542, 3);
lean_inc(x_2543);
lean_dec(x_2542);
x_2544 = lean_ctor_get_uint8(x_2543, sizeof(void*)*1);
lean_dec(x_2543);
if (x_2544 == 0)
{
lean_object* x_2545; uint8_t x_2546; 
x_2545 = lean_ctor_get(x_2541, 1);
lean_inc(x_2545);
lean_dec(x_2541);
x_2546 = 0;
x_2527 = x_2546;
x_2528 = x_2545;
goto block_2540;
}
else
{
lean_object* x_2547; lean_object* x_2548; lean_object* x_2549; lean_object* x_2550; lean_object* x_2551; uint8_t x_2552; 
x_2547 = lean_ctor_get(x_2541, 1);
lean_inc(x_2547);
lean_dec(x_2541);
x_2548 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_2549 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2548, x_3, x_4, x_5, x_6, x_2547);
x_2550 = lean_ctor_get(x_2549, 0);
lean_inc(x_2550);
x_2551 = lean_ctor_get(x_2549, 1);
lean_inc(x_2551);
lean_dec(x_2549);
x_2552 = lean_unbox(x_2550);
lean_dec(x_2550);
x_2527 = x_2552;
x_2528 = x_2551;
goto block_2540;
}
block_2526:
{
lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; uint8_t x_2207; 
lean_inc(x_1);
x_2199 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_2198);
x_2200 = lean_ctor_get(x_2199, 0);
lean_inc(x_2200);
x_2201 = lean_ctor_get(x_2199, 1);
lean_inc(x_2201);
lean_dec(x_2199);
x_2202 = l_Lean_Level_normalize(x_2200);
lean_dec(x_2200);
lean_inc(x_2);
x_2203 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_2, x_3, x_4, x_5, x_6, x_2201);
x_2204 = lean_ctor_get(x_2203, 0);
lean_inc(x_2204);
x_2205 = lean_ctor_get(x_2203, 1);
lean_inc(x_2205);
lean_dec(x_2203);
x_2206 = l_Lean_Level_normalize(x_2204);
lean_dec(x_2204);
x_2207 = lean_level_eq(x_1, x_2202);
if (x_2207 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_2202;
x_2 = x_2206;
x_7 = x_2205;
goto _start;
}
else
{
uint8_t x_2209; 
x_2209 = lean_level_eq(x_2, x_2206);
if (x_2209 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_2202;
x_2 = x_2206;
x_7 = x_2205;
goto _start;
}
else
{
lean_object* x_2211; 
lean_dec(x_2206);
lean_dec(x_2202);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_2211 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_2205);
if (lean_obj_tag(x_2211) == 0)
{
uint8_t x_2212; 
x_2212 = !lean_is_exclusive(x_2211);
if (x_2212 == 0)
{
lean_object* x_2213; lean_object* x_2214; uint8_t x_2215; uint8_t x_2216; uint8_t x_2217; 
x_2213 = lean_ctor_get(x_2211, 0);
x_2214 = lean_ctor_get(x_2211, 1);
x_2215 = 2;
x_2216 = lean_unbox(x_2213);
x_2217 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2216, x_2215);
if (x_2217 == 0)
{
uint8_t x_2218; uint8_t x_2219; uint8_t x_2220; lean_object* x_2221; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2218 = 1;
x_2219 = lean_unbox(x_2213);
lean_dec(x_2213);
x_2220 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2219, x_2218);
x_2221 = lean_box(x_2220);
lean_ctor_set(x_2211, 0, x_2221);
return x_2211;
}
else
{
lean_object* x_2222; 
lean_free_object(x_2211);
lean_dec(x_2213);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_2222 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_2214);
if (lean_obj_tag(x_2222) == 0)
{
uint8_t x_2223; 
x_2223 = !lean_is_exclusive(x_2222);
if (x_2223 == 0)
{
lean_object* x_2224; lean_object* x_2225; uint8_t x_2226; uint8_t x_2227; 
x_2224 = lean_ctor_get(x_2222, 0);
x_2225 = lean_ctor_get(x_2222, 1);
x_2226 = lean_unbox(x_2224);
x_2227 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2226, x_2215);
if (x_2227 == 0)
{
uint8_t x_2228; uint8_t x_2229; uint8_t x_2230; lean_object* x_2231; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2228 = 1;
x_2229 = lean_unbox(x_2224);
lean_dec(x_2224);
x_2230 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2229, x_2228);
x_2231 = lean_box(x_2230);
lean_ctor_set(x_2222, 0, x_2231);
return x_2222;
}
else
{
lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; uint8_t x_2235; 
lean_free_object(x_2222);
lean_dec(x_2224);
x_2232 = lean_st_ref_get(x_6, x_2225);
x_2233 = lean_ctor_get(x_2232, 1);
lean_inc(x_2233);
lean_dec(x_2232);
x_2234 = lean_st_ref_get(x_4, x_2233);
x_2235 = !lean_is_exclusive(x_2234);
if (x_2235 == 0)
{
lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; uint8_t x_2239; 
x_2236 = lean_ctor_get(x_2234, 0);
x_2237 = lean_ctor_get(x_2234, 1);
x_2238 = lean_ctor_get(x_2236, 0);
lean_inc(x_2238);
lean_dec(x_2236);
lean_inc(x_2238);
x_2239 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2238, x_1);
if (x_2239 == 0)
{
uint8_t x_2240; 
x_2240 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2238, x_2);
if (x_2240 == 0)
{
lean_object* x_2241; lean_object* x_2271; uint8_t x_2272; 
x_2271 = lean_ctor_get(x_3, 0);
lean_inc(x_2271);
x_2272 = lean_ctor_get_uint8(x_2271, 4);
lean_dec(x_2271);
if (x_2272 == 0)
{
uint8_t x_2273; lean_object* x_2274; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2273 = 0;
x_2274 = lean_box(x_2273);
lean_ctor_set(x_2234, 0, x_2274);
return x_2234;
}
else
{
uint8_t x_2275; 
x_2275 = l_Lean_Level_isMVar(x_1);
if (x_2275 == 0)
{
uint8_t x_2276; 
x_2276 = l_Lean_Level_isMVar(x_2);
if (x_2276 == 0)
{
uint8_t x_2277; lean_object* x_2278; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2277 = 0;
x_2278 = lean_box(x_2277);
lean_ctor_set(x_2234, 0, x_2278);
return x_2234;
}
else
{
lean_object* x_2279; 
lean_free_object(x_2234);
x_2279 = lean_box(0);
x_2241 = x_2279;
goto block_2270;
}
}
else
{
lean_object* x_2280; 
lean_free_object(x_2234);
x_2280 = lean_box(0);
x_2241 = x_2280;
goto block_2270;
}
}
block_2270:
{
uint8_t x_2242; lean_object* x_2243; lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; uint8_t x_2261; 
lean_dec(x_2241);
x_2258 = lean_st_ref_get(x_6, x_2237);
x_2259 = lean_ctor_get(x_2258, 0);
lean_inc(x_2259);
x_2260 = lean_ctor_get(x_2259, 3);
lean_inc(x_2260);
lean_dec(x_2259);
x_2261 = lean_ctor_get_uint8(x_2260, sizeof(void*)*1);
lean_dec(x_2260);
if (x_2261 == 0)
{
lean_object* x_2262; uint8_t x_2263; 
x_2262 = lean_ctor_get(x_2258, 1);
lean_inc(x_2262);
lean_dec(x_2258);
x_2263 = 0;
x_2242 = x_2263;
x_2243 = x_2262;
goto block_2257;
}
else
{
lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; uint8_t x_2269; 
x_2264 = lean_ctor_get(x_2258, 1);
lean_inc(x_2264);
lean_dec(x_2258);
x_2265 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2266 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2265, x_3, x_4, x_5, x_6, x_2264);
x_2267 = lean_ctor_get(x_2266, 0);
lean_inc(x_2267);
x_2268 = lean_ctor_get(x_2266, 1);
lean_inc(x_2268);
lean_dec(x_2266);
x_2269 = lean_unbox(x_2267);
lean_dec(x_2267);
x_2242 = x_2269;
x_2243 = x_2268;
goto block_2257;
}
block_2257:
{
if (x_2242 == 0)
{
lean_object* x_2244; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2244 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2243);
return x_2244;
}
else
{
lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; 
x_2245 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2245, 0, x_1);
x_2246 = l_Lean_KernelException_toMessageData___closed__15;
x_2247 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2247, 0, x_2246);
lean_ctor_set(x_2247, 1, x_2245);
x_2248 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2249 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2249, 0, x_2247);
lean_ctor_set(x_2249, 1, x_2248);
x_2250 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2250, 0, x_2);
x_2251 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2251, 0, x_2249);
lean_ctor_set(x_2251, 1, x_2250);
x_2252 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2252, 0, x_2251);
lean_ctor_set(x_2252, 1, x_2246);
x_2253 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2254 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2253, x_2252, x_3, x_4, x_5, x_6, x_2243);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2255 = lean_ctor_get(x_2254, 1);
lean_inc(x_2255);
lean_dec(x_2254);
x_2256 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2255);
return x_2256;
}
}
}
}
else
{
lean_object* x_2281; uint8_t x_2282; 
lean_free_object(x_2234);
x_2281 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2237);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2282 = !lean_is_exclusive(x_2281);
if (x_2282 == 0)
{
lean_object* x_2283; uint8_t x_2284; lean_object* x_2285; 
x_2283 = lean_ctor_get(x_2281, 0);
lean_dec(x_2283);
x_2284 = 1;
x_2285 = lean_box(x_2284);
lean_ctor_set(x_2281, 0, x_2285);
return x_2281;
}
else
{
lean_object* x_2286; uint8_t x_2287; lean_object* x_2288; lean_object* x_2289; 
x_2286 = lean_ctor_get(x_2281, 1);
lean_inc(x_2286);
lean_dec(x_2281);
x_2287 = 1;
x_2288 = lean_box(x_2287);
x_2289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2289, 0, x_2288);
lean_ctor_set(x_2289, 1, x_2286);
return x_2289;
}
}
}
else
{
lean_object* x_2290; uint8_t x_2291; 
lean_dec(x_2238);
lean_free_object(x_2234);
x_2290 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2237);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2291 = !lean_is_exclusive(x_2290);
if (x_2291 == 0)
{
lean_object* x_2292; uint8_t x_2293; lean_object* x_2294; 
x_2292 = lean_ctor_get(x_2290, 0);
lean_dec(x_2292);
x_2293 = 1;
x_2294 = lean_box(x_2293);
lean_ctor_set(x_2290, 0, x_2294);
return x_2290;
}
else
{
lean_object* x_2295; uint8_t x_2296; lean_object* x_2297; lean_object* x_2298; 
x_2295 = lean_ctor_get(x_2290, 1);
lean_inc(x_2295);
lean_dec(x_2290);
x_2296 = 1;
x_2297 = lean_box(x_2296);
x_2298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2298, 0, x_2297);
lean_ctor_set(x_2298, 1, x_2295);
return x_2298;
}
}
}
else
{
lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; uint8_t x_2302; 
x_2299 = lean_ctor_get(x_2234, 0);
x_2300 = lean_ctor_get(x_2234, 1);
lean_inc(x_2300);
lean_inc(x_2299);
lean_dec(x_2234);
x_2301 = lean_ctor_get(x_2299, 0);
lean_inc(x_2301);
lean_dec(x_2299);
lean_inc(x_2301);
x_2302 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2301, x_1);
if (x_2302 == 0)
{
uint8_t x_2303; 
x_2303 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2301, x_2);
if (x_2303 == 0)
{
lean_object* x_2304; lean_object* x_2334; uint8_t x_2335; 
x_2334 = lean_ctor_get(x_3, 0);
lean_inc(x_2334);
x_2335 = lean_ctor_get_uint8(x_2334, 4);
lean_dec(x_2334);
if (x_2335 == 0)
{
uint8_t x_2336; lean_object* x_2337; lean_object* x_2338; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2336 = 0;
x_2337 = lean_box(x_2336);
x_2338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2338, 0, x_2337);
lean_ctor_set(x_2338, 1, x_2300);
return x_2338;
}
else
{
uint8_t x_2339; 
x_2339 = l_Lean_Level_isMVar(x_1);
if (x_2339 == 0)
{
uint8_t x_2340; 
x_2340 = l_Lean_Level_isMVar(x_2);
if (x_2340 == 0)
{
uint8_t x_2341; lean_object* x_2342; lean_object* x_2343; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2341 = 0;
x_2342 = lean_box(x_2341);
x_2343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2343, 0, x_2342);
lean_ctor_set(x_2343, 1, x_2300);
return x_2343;
}
else
{
lean_object* x_2344; 
x_2344 = lean_box(0);
x_2304 = x_2344;
goto block_2333;
}
}
else
{
lean_object* x_2345; 
x_2345 = lean_box(0);
x_2304 = x_2345;
goto block_2333;
}
}
block_2333:
{
uint8_t x_2305; lean_object* x_2306; lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; uint8_t x_2324; 
lean_dec(x_2304);
x_2321 = lean_st_ref_get(x_6, x_2300);
x_2322 = lean_ctor_get(x_2321, 0);
lean_inc(x_2322);
x_2323 = lean_ctor_get(x_2322, 3);
lean_inc(x_2323);
lean_dec(x_2322);
x_2324 = lean_ctor_get_uint8(x_2323, sizeof(void*)*1);
lean_dec(x_2323);
if (x_2324 == 0)
{
lean_object* x_2325; uint8_t x_2326; 
x_2325 = lean_ctor_get(x_2321, 1);
lean_inc(x_2325);
lean_dec(x_2321);
x_2326 = 0;
x_2305 = x_2326;
x_2306 = x_2325;
goto block_2320;
}
else
{
lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; lean_object* x_2330; lean_object* x_2331; uint8_t x_2332; 
x_2327 = lean_ctor_get(x_2321, 1);
lean_inc(x_2327);
lean_dec(x_2321);
x_2328 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2329 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2328, x_3, x_4, x_5, x_6, x_2327);
x_2330 = lean_ctor_get(x_2329, 0);
lean_inc(x_2330);
x_2331 = lean_ctor_get(x_2329, 1);
lean_inc(x_2331);
lean_dec(x_2329);
x_2332 = lean_unbox(x_2330);
lean_dec(x_2330);
x_2305 = x_2332;
x_2306 = x_2331;
goto block_2320;
}
block_2320:
{
if (x_2305 == 0)
{
lean_object* x_2307; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2307 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2306);
return x_2307;
}
else
{
lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; lean_object* x_2313; lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; 
x_2308 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2308, 0, x_1);
x_2309 = l_Lean_KernelException_toMessageData___closed__15;
x_2310 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2310, 0, x_2309);
lean_ctor_set(x_2310, 1, x_2308);
x_2311 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2312 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2312, 0, x_2310);
lean_ctor_set(x_2312, 1, x_2311);
x_2313 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2313, 0, x_2);
x_2314 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2314, 0, x_2312);
lean_ctor_set(x_2314, 1, x_2313);
x_2315 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2315, 0, x_2314);
lean_ctor_set(x_2315, 1, x_2309);
x_2316 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2317 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2316, x_2315, x_3, x_4, x_5, x_6, x_2306);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2318 = lean_ctor_get(x_2317, 1);
lean_inc(x_2318);
lean_dec(x_2317);
x_2319 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2318);
return x_2319;
}
}
}
}
else
{
lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; uint8_t x_2349; lean_object* x_2350; lean_object* x_2351; 
x_2346 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2300);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2347 = lean_ctor_get(x_2346, 1);
lean_inc(x_2347);
if (lean_is_exclusive(x_2346)) {
 lean_ctor_release(x_2346, 0);
 lean_ctor_release(x_2346, 1);
 x_2348 = x_2346;
} else {
 lean_dec_ref(x_2346);
 x_2348 = lean_box(0);
}
x_2349 = 1;
x_2350 = lean_box(x_2349);
if (lean_is_scalar(x_2348)) {
 x_2351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2351 = x_2348;
}
lean_ctor_set(x_2351, 0, x_2350);
lean_ctor_set(x_2351, 1, x_2347);
return x_2351;
}
}
else
{
lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; uint8_t x_2355; lean_object* x_2356; lean_object* x_2357; 
lean_dec(x_2301);
x_2352 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2300);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2353 = lean_ctor_get(x_2352, 1);
lean_inc(x_2353);
if (lean_is_exclusive(x_2352)) {
 lean_ctor_release(x_2352, 0);
 lean_ctor_release(x_2352, 1);
 x_2354 = x_2352;
} else {
 lean_dec_ref(x_2352);
 x_2354 = lean_box(0);
}
x_2355 = 1;
x_2356 = lean_box(x_2355);
if (lean_is_scalar(x_2354)) {
 x_2357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2357 = x_2354;
}
lean_ctor_set(x_2357, 0, x_2356);
lean_ctor_set(x_2357, 1, x_2353);
return x_2357;
}
}
}
}
else
{
lean_object* x_2358; lean_object* x_2359; uint8_t x_2360; uint8_t x_2361; 
x_2358 = lean_ctor_get(x_2222, 0);
x_2359 = lean_ctor_get(x_2222, 1);
lean_inc(x_2359);
lean_inc(x_2358);
lean_dec(x_2222);
x_2360 = lean_unbox(x_2358);
x_2361 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2360, x_2215);
if (x_2361 == 0)
{
uint8_t x_2362; uint8_t x_2363; uint8_t x_2364; lean_object* x_2365; lean_object* x_2366; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2362 = 1;
x_2363 = lean_unbox(x_2358);
lean_dec(x_2358);
x_2364 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2363, x_2362);
x_2365 = lean_box(x_2364);
x_2366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2366, 0, x_2365);
lean_ctor_set(x_2366, 1, x_2359);
return x_2366;
}
else
{
lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; uint8_t x_2374; 
lean_dec(x_2358);
x_2367 = lean_st_ref_get(x_6, x_2359);
x_2368 = lean_ctor_get(x_2367, 1);
lean_inc(x_2368);
lean_dec(x_2367);
x_2369 = lean_st_ref_get(x_4, x_2368);
x_2370 = lean_ctor_get(x_2369, 0);
lean_inc(x_2370);
x_2371 = lean_ctor_get(x_2369, 1);
lean_inc(x_2371);
if (lean_is_exclusive(x_2369)) {
 lean_ctor_release(x_2369, 0);
 lean_ctor_release(x_2369, 1);
 x_2372 = x_2369;
} else {
 lean_dec_ref(x_2369);
 x_2372 = lean_box(0);
}
x_2373 = lean_ctor_get(x_2370, 0);
lean_inc(x_2373);
lean_dec(x_2370);
lean_inc(x_2373);
x_2374 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2373, x_1);
if (x_2374 == 0)
{
uint8_t x_2375; 
x_2375 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2373, x_2);
if (x_2375 == 0)
{
lean_object* x_2376; lean_object* x_2406; uint8_t x_2407; 
x_2406 = lean_ctor_get(x_3, 0);
lean_inc(x_2406);
x_2407 = lean_ctor_get_uint8(x_2406, 4);
lean_dec(x_2406);
if (x_2407 == 0)
{
uint8_t x_2408; lean_object* x_2409; lean_object* x_2410; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2408 = 0;
x_2409 = lean_box(x_2408);
if (lean_is_scalar(x_2372)) {
 x_2410 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2410 = x_2372;
}
lean_ctor_set(x_2410, 0, x_2409);
lean_ctor_set(x_2410, 1, x_2371);
return x_2410;
}
else
{
uint8_t x_2411; 
x_2411 = l_Lean_Level_isMVar(x_1);
if (x_2411 == 0)
{
uint8_t x_2412; 
x_2412 = l_Lean_Level_isMVar(x_2);
if (x_2412 == 0)
{
uint8_t x_2413; lean_object* x_2414; lean_object* x_2415; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2413 = 0;
x_2414 = lean_box(x_2413);
if (lean_is_scalar(x_2372)) {
 x_2415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2415 = x_2372;
}
lean_ctor_set(x_2415, 0, x_2414);
lean_ctor_set(x_2415, 1, x_2371);
return x_2415;
}
else
{
lean_object* x_2416; 
lean_dec(x_2372);
x_2416 = lean_box(0);
x_2376 = x_2416;
goto block_2405;
}
}
else
{
lean_object* x_2417; 
lean_dec(x_2372);
x_2417 = lean_box(0);
x_2376 = x_2417;
goto block_2405;
}
}
block_2405:
{
uint8_t x_2377; lean_object* x_2378; lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; uint8_t x_2396; 
lean_dec(x_2376);
x_2393 = lean_st_ref_get(x_6, x_2371);
x_2394 = lean_ctor_get(x_2393, 0);
lean_inc(x_2394);
x_2395 = lean_ctor_get(x_2394, 3);
lean_inc(x_2395);
lean_dec(x_2394);
x_2396 = lean_ctor_get_uint8(x_2395, sizeof(void*)*1);
lean_dec(x_2395);
if (x_2396 == 0)
{
lean_object* x_2397; uint8_t x_2398; 
x_2397 = lean_ctor_get(x_2393, 1);
lean_inc(x_2397);
lean_dec(x_2393);
x_2398 = 0;
x_2377 = x_2398;
x_2378 = x_2397;
goto block_2392;
}
else
{
lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; uint8_t x_2404; 
x_2399 = lean_ctor_get(x_2393, 1);
lean_inc(x_2399);
lean_dec(x_2393);
x_2400 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2401 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2400, x_3, x_4, x_5, x_6, x_2399);
x_2402 = lean_ctor_get(x_2401, 0);
lean_inc(x_2402);
x_2403 = lean_ctor_get(x_2401, 1);
lean_inc(x_2403);
lean_dec(x_2401);
x_2404 = lean_unbox(x_2402);
lean_dec(x_2402);
x_2377 = x_2404;
x_2378 = x_2403;
goto block_2392;
}
block_2392:
{
if (x_2377 == 0)
{
lean_object* x_2379; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2379 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2378);
return x_2379;
}
else
{
lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; lean_object* x_2384; lean_object* x_2385; lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; 
x_2380 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2380, 0, x_1);
x_2381 = l_Lean_KernelException_toMessageData___closed__15;
x_2382 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2382, 0, x_2381);
lean_ctor_set(x_2382, 1, x_2380);
x_2383 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2384 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2384, 0, x_2382);
lean_ctor_set(x_2384, 1, x_2383);
x_2385 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2385, 0, x_2);
x_2386 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2386, 0, x_2384);
lean_ctor_set(x_2386, 1, x_2385);
x_2387 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2387, 0, x_2386);
lean_ctor_set(x_2387, 1, x_2381);
x_2388 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2389 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2388, x_2387, x_3, x_4, x_5, x_6, x_2378);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2390 = lean_ctor_get(x_2389, 1);
lean_inc(x_2390);
lean_dec(x_2389);
x_2391 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2390);
return x_2391;
}
}
}
}
else
{
lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; uint8_t x_2421; lean_object* x_2422; lean_object* x_2423; 
lean_dec(x_2372);
x_2418 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2371);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2419 = lean_ctor_get(x_2418, 1);
lean_inc(x_2419);
if (lean_is_exclusive(x_2418)) {
 lean_ctor_release(x_2418, 0);
 lean_ctor_release(x_2418, 1);
 x_2420 = x_2418;
} else {
 lean_dec_ref(x_2418);
 x_2420 = lean_box(0);
}
x_2421 = 1;
x_2422 = lean_box(x_2421);
if (lean_is_scalar(x_2420)) {
 x_2423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2423 = x_2420;
}
lean_ctor_set(x_2423, 0, x_2422);
lean_ctor_set(x_2423, 1, x_2419);
return x_2423;
}
}
else
{
lean_object* x_2424; lean_object* x_2425; lean_object* x_2426; uint8_t x_2427; lean_object* x_2428; lean_object* x_2429; 
lean_dec(x_2373);
lean_dec(x_2372);
x_2424 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2371);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2425 = lean_ctor_get(x_2424, 1);
lean_inc(x_2425);
if (lean_is_exclusive(x_2424)) {
 lean_ctor_release(x_2424, 0);
 lean_ctor_release(x_2424, 1);
 x_2426 = x_2424;
} else {
 lean_dec_ref(x_2424);
 x_2426 = lean_box(0);
}
x_2427 = 1;
x_2428 = lean_box(x_2427);
if (lean_is_scalar(x_2426)) {
 x_2429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2429 = x_2426;
}
lean_ctor_set(x_2429, 0, x_2428);
lean_ctor_set(x_2429, 1, x_2425);
return x_2429;
}
}
}
}
else
{
uint8_t x_2430; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2430 = !lean_is_exclusive(x_2222);
if (x_2430 == 0)
{
return x_2222;
}
else
{
lean_object* x_2431; lean_object* x_2432; lean_object* x_2433; 
x_2431 = lean_ctor_get(x_2222, 0);
x_2432 = lean_ctor_get(x_2222, 1);
lean_inc(x_2432);
lean_inc(x_2431);
lean_dec(x_2222);
x_2433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2433, 0, x_2431);
lean_ctor_set(x_2433, 1, x_2432);
return x_2433;
}
}
}
}
else
{
lean_object* x_2434; lean_object* x_2435; uint8_t x_2436; uint8_t x_2437; uint8_t x_2438; 
x_2434 = lean_ctor_get(x_2211, 0);
x_2435 = lean_ctor_get(x_2211, 1);
lean_inc(x_2435);
lean_inc(x_2434);
lean_dec(x_2211);
x_2436 = 2;
x_2437 = lean_unbox(x_2434);
x_2438 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2437, x_2436);
if (x_2438 == 0)
{
uint8_t x_2439; uint8_t x_2440; uint8_t x_2441; lean_object* x_2442; lean_object* x_2443; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2439 = 1;
x_2440 = lean_unbox(x_2434);
lean_dec(x_2434);
x_2441 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2440, x_2439);
x_2442 = lean_box(x_2441);
x_2443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2443, 0, x_2442);
lean_ctor_set(x_2443, 1, x_2435);
return x_2443;
}
else
{
lean_object* x_2444; 
lean_dec(x_2434);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_2444 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_2435);
if (lean_obj_tag(x_2444) == 0)
{
lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; uint8_t x_2448; uint8_t x_2449; 
x_2445 = lean_ctor_get(x_2444, 0);
lean_inc(x_2445);
x_2446 = lean_ctor_get(x_2444, 1);
lean_inc(x_2446);
if (lean_is_exclusive(x_2444)) {
 lean_ctor_release(x_2444, 0);
 lean_ctor_release(x_2444, 1);
 x_2447 = x_2444;
} else {
 lean_dec_ref(x_2444);
 x_2447 = lean_box(0);
}
x_2448 = lean_unbox(x_2445);
x_2449 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2448, x_2436);
if (x_2449 == 0)
{
uint8_t x_2450; uint8_t x_2451; uint8_t x_2452; lean_object* x_2453; lean_object* x_2454; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2450 = 1;
x_2451 = lean_unbox(x_2445);
lean_dec(x_2445);
x_2452 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2451, x_2450);
x_2453 = lean_box(x_2452);
if (lean_is_scalar(x_2447)) {
 x_2454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2454 = x_2447;
}
lean_ctor_set(x_2454, 0, x_2453);
lean_ctor_set(x_2454, 1, x_2446);
return x_2454;
}
else
{
lean_object* x_2455; lean_object* x_2456; lean_object* x_2457; lean_object* x_2458; lean_object* x_2459; lean_object* x_2460; lean_object* x_2461; uint8_t x_2462; 
lean_dec(x_2447);
lean_dec(x_2445);
x_2455 = lean_st_ref_get(x_6, x_2446);
x_2456 = lean_ctor_get(x_2455, 1);
lean_inc(x_2456);
lean_dec(x_2455);
x_2457 = lean_st_ref_get(x_4, x_2456);
x_2458 = lean_ctor_get(x_2457, 0);
lean_inc(x_2458);
x_2459 = lean_ctor_get(x_2457, 1);
lean_inc(x_2459);
if (lean_is_exclusive(x_2457)) {
 lean_ctor_release(x_2457, 0);
 lean_ctor_release(x_2457, 1);
 x_2460 = x_2457;
} else {
 lean_dec_ref(x_2457);
 x_2460 = lean_box(0);
}
x_2461 = lean_ctor_get(x_2458, 0);
lean_inc(x_2461);
lean_dec(x_2458);
lean_inc(x_2461);
x_2462 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2461, x_1);
if (x_2462 == 0)
{
uint8_t x_2463; 
x_2463 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2461, x_2);
if (x_2463 == 0)
{
lean_object* x_2464; lean_object* x_2494; uint8_t x_2495; 
x_2494 = lean_ctor_get(x_3, 0);
lean_inc(x_2494);
x_2495 = lean_ctor_get_uint8(x_2494, 4);
lean_dec(x_2494);
if (x_2495 == 0)
{
uint8_t x_2496; lean_object* x_2497; lean_object* x_2498; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2496 = 0;
x_2497 = lean_box(x_2496);
if (lean_is_scalar(x_2460)) {
 x_2498 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2498 = x_2460;
}
lean_ctor_set(x_2498, 0, x_2497);
lean_ctor_set(x_2498, 1, x_2459);
return x_2498;
}
else
{
uint8_t x_2499; 
x_2499 = l_Lean_Level_isMVar(x_1);
if (x_2499 == 0)
{
uint8_t x_2500; 
x_2500 = l_Lean_Level_isMVar(x_2);
if (x_2500 == 0)
{
uint8_t x_2501; lean_object* x_2502; lean_object* x_2503; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2501 = 0;
x_2502 = lean_box(x_2501);
if (lean_is_scalar(x_2460)) {
 x_2503 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2503 = x_2460;
}
lean_ctor_set(x_2503, 0, x_2502);
lean_ctor_set(x_2503, 1, x_2459);
return x_2503;
}
else
{
lean_object* x_2504; 
lean_dec(x_2460);
x_2504 = lean_box(0);
x_2464 = x_2504;
goto block_2493;
}
}
else
{
lean_object* x_2505; 
lean_dec(x_2460);
x_2505 = lean_box(0);
x_2464 = x_2505;
goto block_2493;
}
}
block_2493:
{
uint8_t x_2465; lean_object* x_2466; lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; uint8_t x_2484; 
lean_dec(x_2464);
x_2481 = lean_st_ref_get(x_6, x_2459);
x_2482 = lean_ctor_get(x_2481, 0);
lean_inc(x_2482);
x_2483 = lean_ctor_get(x_2482, 3);
lean_inc(x_2483);
lean_dec(x_2482);
x_2484 = lean_ctor_get_uint8(x_2483, sizeof(void*)*1);
lean_dec(x_2483);
if (x_2484 == 0)
{
lean_object* x_2485; uint8_t x_2486; 
x_2485 = lean_ctor_get(x_2481, 1);
lean_inc(x_2485);
lean_dec(x_2481);
x_2486 = 0;
x_2465 = x_2486;
x_2466 = x_2485;
goto block_2480;
}
else
{
lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; lean_object* x_2490; lean_object* x_2491; uint8_t x_2492; 
x_2487 = lean_ctor_get(x_2481, 1);
lean_inc(x_2487);
lean_dec(x_2481);
x_2488 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2489 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2488, x_3, x_4, x_5, x_6, x_2487);
x_2490 = lean_ctor_get(x_2489, 0);
lean_inc(x_2490);
x_2491 = lean_ctor_get(x_2489, 1);
lean_inc(x_2491);
lean_dec(x_2489);
x_2492 = lean_unbox(x_2490);
lean_dec(x_2490);
x_2465 = x_2492;
x_2466 = x_2491;
goto block_2480;
}
block_2480:
{
if (x_2465 == 0)
{
lean_object* x_2467; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2467 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2466);
return x_2467;
}
else
{
lean_object* x_2468; lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; 
x_2468 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2468, 0, x_1);
x_2469 = l_Lean_KernelException_toMessageData___closed__15;
x_2470 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2470, 0, x_2469);
lean_ctor_set(x_2470, 1, x_2468);
x_2471 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2472 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2472, 0, x_2470);
lean_ctor_set(x_2472, 1, x_2471);
x_2473 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2473, 0, x_2);
x_2474 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2474, 0, x_2472);
lean_ctor_set(x_2474, 1, x_2473);
x_2475 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2475, 0, x_2474);
lean_ctor_set(x_2475, 1, x_2469);
x_2476 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2477 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2476, x_2475, x_3, x_4, x_5, x_6, x_2466);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2478 = lean_ctor_get(x_2477, 1);
lean_inc(x_2478);
lean_dec(x_2477);
x_2479 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2478);
return x_2479;
}
}
}
}
else
{
lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; uint8_t x_2509; lean_object* x_2510; lean_object* x_2511; 
lean_dec(x_2460);
x_2506 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2459);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2507 = lean_ctor_get(x_2506, 1);
lean_inc(x_2507);
if (lean_is_exclusive(x_2506)) {
 lean_ctor_release(x_2506, 0);
 lean_ctor_release(x_2506, 1);
 x_2508 = x_2506;
} else {
 lean_dec_ref(x_2506);
 x_2508 = lean_box(0);
}
x_2509 = 1;
x_2510 = lean_box(x_2509);
if (lean_is_scalar(x_2508)) {
 x_2511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2511 = x_2508;
}
lean_ctor_set(x_2511, 0, x_2510);
lean_ctor_set(x_2511, 1, x_2507);
return x_2511;
}
}
else
{
lean_object* x_2512; lean_object* x_2513; lean_object* x_2514; uint8_t x_2515; lean_object* x_2516; lean_object* x_2517; 
lean_dec(x_2461);
lean_dec(x_2460);
x_2512 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2459);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2513 = lean_ctor_get(x_2512, 1);
lean_inc(x_2513);
if (lean_is_exclusive(x_2512)) {
 lean_ctor_release(x_2512, 0);
 lean_ctor_release(x_2512, 1);
 x_2514 = x_2512;
} else {
 lean_dec_ref(x_2512);
 x_2514 = lean_box(0);
}
x_2515 = 1;
x_2516 = lean_box(x_2515);
if (lean_is_scalar(x_2514)) {
 x_2517 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2517 = x_2514;
}
lean_ctor_set(x_2517, 0, x_2516);
lean_ctor_set(x_2517, 1, x_2513);
return x_2517;
}
}
}
else
{
lean_object* x_2518; lean_object* x_2519; lean_object* x_2520; lean_object* x_2521; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2518 = lean_ctor_get(x_2444, 0);
lean_inc(x_2518);
x_2519 = lean_ctor_get(x_2444, 1);
lean_inc(x_2519);
if (lean_is_exclusive(x_2444)) {
 lean_ctor_release(x_2444, 0);
 lean_ctor_release(x_2444, 1);
 x_2520 = x_2444;
} else {
 lean_dec_ref(x_2444);
 x_2520 = lean_box(0);
}
if (lean_is_scalar(x_2520)) {
 x_2521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2521 = x_2520;
}
lean_ctor_set(x_2521, 0, x_2518);
lean_ctor_set(x_2521, 1, x_2519);
return x_2521;
}
}
}
}
else
{
uint8_t x_2522; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2522 = !lean_is_exclusive(x_2211);
if (x_2522 == 0)
{
return x_2211;
}
else
{
lean_object* x_2523; lean_object* x_2524; lean_object* x_2525; 
x_2523 = lean_ctor_get(x_2211, 0);
x_2524 = lean_ctor_get(x_2211, 1);
lean_inc(x_2524);
lean_inc(x_2523);
lean_dec(x_2211);
x_2525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2525, 0, x_2523);
lean_ctor_set(x_2525, 1, x_2524);
return x_2525;
}
}
}
}
}
block_2540:
{
if (x_2527 == 0)
{
x_2198 = x_2528;
goto block_2526;
}
else
{
lean_object* x_2529; lean_object* x_2530; lean_object* x_2531; lean_object* x_2532; lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; 
lean_inc(x_1);
x_2529 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2529, 0, x_1);
x_2530 = l_Lean_KernelException_toMessageData___closed__15;
x_2531 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2531, 0, x_2530);
lean_ctor_set(x_2531, 1, x_2529);
x_2532 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2533 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2533, 0, x_2531);
lean_ctor_set(x_2533, 1, x_2532);
lean_inc(x_2);
x_2534 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2534, 0, x_2);
x_2535 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2535, 0, x_2533);
lean_ctor_set(x_2535, 1, x_2534);
x_2536 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2536, 0, x_2535);
lean_ctor_set(x_2536, 1, x_2530);
x_2537 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_2538 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2537, x_2536, x_3, x_4, x_5, x_6, x_2528);
x_2539 = lean_ctor_get(x_2538, 1);
lean_inc(x_2539);
lean_dec(x_2538);
x_2198 = x_2539;
goto block_2526;
}
}
}
else
{
lean_object* x_2553; lean_object* x_2554; lean_object* x_2555; uint8_t x_2556; lean_object* x_2557; lean_object* x_2558; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2553 = lean_unsigned_to_nat(0u);
x_2554 = l_Lean_Level_getOffsetAux(x_1, x_2553);
lean_dec(x_1);
x_2555 = l_Lean_Level_getOffsetAux(x_2, x_2553);
lean_dec(x_2);
x_2556 = lean_nat_dec_eq(x_2554, x_2555);
lean_dec(x_2555);
lean_dec(x_2554);
x_2557 = lean_box(x_2556);
x_2558 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2558, 0, x_2557);
lean_ctor_set(x_2558, 1, x_7);
return x_2558;
}
}
case 3:
{
lean_object* x_2559; lean_object* x_2560; uint8_t x_2561; 
x_2559 = l_Lean_Level_getLevelOffset(x_1);
x_2560 = l_Lean_Level_getLevelOffset(x_2);
x_2561 = lean_level_eq(x_2559, x_2560);
lean_dec(x_2560);
lean_dec(x_2559);
if (x_2561 == 0)
{
lean_object* x_2562; uint8_t x_2891; lean_object* x_2892; lean_object* x_2905; lean_object* x_2906; lean_object* x_2907; uint8_t x_2908; 
x_2905 = lean_st_ref_get(x_6, x_7);
x_2906 = lean_ctor_get(x_2905, 0);
lean_inc(x_2906);
x_2907 = lean_ctor_get(x_2906, 3);
lean_inc(x_2907);
lean_dec(x_2906);
x_2908 = lean_ctor_get_uint8(x_2907, sizeof(void*)*1);
lean_dec(x_2907);
if (x_2908 == 0)
{
lean_object* x_2909; uint8_t x_2910; 
x_2909 = lean_ctor_get(x_2905, 1);
lean_inc(x_2909);
lean_dec(x_2905);
x_2910 = 0;
x_2891 = x_2910;
x_2892 = x_2909;
goto block_2904;
}
else
{
lean_object* x_2911; lean_object* x_2912; lean_object* x_2913; lean_object* x_2914; lean_object* x_2915; uint8_t x_2916; 
x_2911 = lean_ctor_get(x_2905, 1);
lean_inc(x_2911);
lean_dec(x_2905);
x_2912 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_2913 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2912, x_3, x_4, x_5, x_6, x_2911);
x_2914 = lean_ctor_get(x_2913, 0);
lean_inc(x_2914);
x_2915 = lean_ctor_get(x_2913, 1);
lean_inc(x_2915);
lean_dec(x_2913);
x_2916 = lean_unbox(x_2914);
lean_dec(x_2914);
x_2891 = x_2916;
x_2892 = x_2915;
goto block_2904;
}
block_2890:
{
lean_object* x_2563; lean_object* x_2564; lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; uint8_t x_2571; 
lean_inc(x_1);
x_2563 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_2562);
x_2564 = lean_ctor_get(x_2563, 0);
lean_inc(x_2564);
x_2565 = lean_ctor_get(x_2563, 1);
lean_inc(x_2565);
lean_dec(x_2563);
x_2566 = l_Lean_Level_normalize(x_2564);
lean_dec(x_2564);
lean_inc(x_2);
x_2567 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_2, x_3, x_4, x_5, x_6, x_2565);
x_2568 = lean_ctor_get(x_2567, 0);
lean_inc(x_2568);
x_2569 = lean_ctor_get(x_2567, 1);
lean_inc(x_2569);
lean_dec(x_2567);
x_2570 = l_Lean_Level_normalize(x_2568);
lean_dec(x_2568);
x_2571 = lean_level_eq(x_1, x_2566);
if (x_2571 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_2566;
x_2 = x_2570;
x_7 = x_2569;
goto _start;
}
else
{
uint8_t x_2573; 
x_2573 = lean_level_eq(x_2, x_2570);
if (x_2573 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_2566;
x_2 = x_2570;
x_7 = x_2569;
goto _start;
}
else
{
lean_object* x_2575; 
lean_dec(x_2570);
lean_dec(x_2566);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_2575 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_2569);
if (lean_obj_tag(x_2575) == 0)
{
uint8_t x_2576; 
x_2576 = !lean_is_exclusive(x_2575);
if (x_2576 == 0)
{
lean_object* x_2577; lean_object* x_2578; uint8_t x_2579; uint8_t x_2580; uint8_t x_2581; 
x_2577 = lean_ctor_get(x_2575, 0);
x_2578 = lean_ctor_get(x_2575, 1);
x_2579 = 2;
x_2580 = lean_unbox(x_2577);
x_2581 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2580, x_2579);
if (x_2581 == 0)
{
uint8_t x_2582; uint8_t x_2583; uint8_t x_2584; lean_object* x_2585; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2582 = 1;
x_2583 = lean_unbox(x_2577);
lean_dec(x_2577);
x_2584 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2583, x_2582);
x_2585 = lean_box(x_2584);
lean_ctor_set(x_2575, 0, x_2585);
return x_2575;
}
else
{
lean_object* x_2586; 
lean_free_object(x_2575);
lean_dec(x_2577);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_2586 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_2578);
if (lean_obj_tag(x_2586) == 0)
{
uint8_t x_2587; 
x_2587 = !lean_is_exclusive(x_2586);
if (x_2587 == 0)
{
lean_object* x_2588; lean_object* x_2589; uint8_t x_2590; uint8_t x_2591; 
x_2588 = lean_ctor_get(x_2586, 0);
x_2589 = lean_ctor_get(x_2586, 1);
x_2590 = lean_unbox(x_2588);
x_2591 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2590, x_2579);
if (x_2591 == 0)
{
uint8_t x_2592; uint8_t x_2593; uint8_t x_2594; lean_object* x_2595; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2592 = 1;
x_2593 = lean_unbox(x_2588);
lean_dec(x_2588);
x_2594 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2593, x_2592);
x_2595 = lean_box(x_2594);
lean_ctor_set(x_2586, 0, x_2595);
return x_2586;
}
else
{
lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; uint8_t x_2599; 
lean_free_object(x_2586);
lean_dec(x_2588);
x_2596 = lean_st_ref_get(x_6, x_2589);
x_2597 = lean_ctor_get(x_2596, 1);
lean_inc(x_2597);
lean_dec(x_2596);
x_2598 = lean_st_ref_get(x_4, x_2597);
x_2599 = !lean_is_exclusive(x_2598);
if (x_2599 == 0)
{
lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; uint8_t x_2603; 
x_2600 = lean_ctor_get(x_2598, 0);
x_2601 = lean_ctor_get(x_2598, 1);
x_2602 = lean_ctor_get(x_2600, 0);
lean_inc(x_2602);
lean_dec(x_2600);
lean_inc(x_2602);
x_2603 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2602, x_1);
if (x_2603 == 0)
{
uint8_t x_2604; 
x_2604 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2602, x_2);
if (x_2604 == 0)
{
lean_object* x_2605; lean_object* x_2635; uint8_t x_2636; 
x_2635 = lean_ctor_get(x_3, 0);
lean_inc(x_2635);
x_2636 = lean_ctor_get_uint8(x_2635, 4);
lean_dec(x_2635);
if (x_2636 == 0)
{
uint8_t x_2637; lean_object* x_2638; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2637 = 0;
x_2638 = lean_box(x_2637);
lean_ctor_set(x_2598, 0, x_2638);
return x_2598;
}
else
{
uint8_t x_2639; 
x_2639 = l_Lean_Level_isMVar(x_1);
if (x_2639 == 0)
{
uint8_t x_2640; 
x_2640 = l_Lean_Level_isMVar(x_2);
if (x_2640 == 0)
{
uint8_t x_2641; lean_object* x_2642; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2641 = 0;
x_2642 = lean_box(x_2641);
lean_ctor_set(x_2598, 0, x_2642);
return x_2598;
}
else
{
lean_object* x_2643; 
lean_free_object(x_2598);
x_2643 = lean_box(0);
x_2605 = x_2643;
goto block_2634;
}
}
else
{
lean_object* x_2644; 
lean_free_object(x_2598);
x_2644 = lean_box(0);
x_2605 = x_2644;
goto block_2634;
}
}
block_2634:
{
uint8_t x_2606; lean_object* x_2607; lean_object* x_2622; lean_object* x_2623; lean_object* x_2624; uint8_t x_2625; 
lean_dec(x_2605);
x_2622 = lean_st_ref_get(x_6, x_2601);
x_2623 = lean_ctor_get(x_2622, 0);
lean_inc(x_2623);
x_2624 = lean_ctor_get(x_2623, 3);
lean_inc(x_2624);
lean_dec(x_2623);
x_2625 = lean_ctor_get_uint8(x_2624, sizeof(void*)*1);
lean_dec(x_2624);
if (x_2625 == 0)
{
lean_object* x_2626; uint8_t x_2627; 
x_2626 = lean_ctor_get(x_2622, 1);
lean_inc(x_2626);
lean_dec(x_2622);
x_2627 = 0;
x_2606 = x_2627;
x_2607 = x_2626;
goto block_2621;
}
else
{
lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; uint8_t x_2633; 
x_2628 = lean_ctor_get(x_2622, 1);
lean_inc(x_2628);
lean_dec(x_2622);
x_2629 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2630 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2629, x_3, x_4, x_5, x_6, x_2628);
x_2631 = lean_ctor_get(x_2630, 0);
lean_inc(x_2631);
x_2632 = lean_ctor_get(x_2630, 1);
lean_inc(x_2632);
lean_dec(x_2630);
x_2633 = lean_unbox(x_2631);
lean_dec(x_2631);
x_2606 = x_2633;
x_2607 = x_2632;
goto block_2621;
}
block_2621:
{
if (x_2606 == 0)
{
lean_object* x_2608; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2608 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2607);
return x_2608;
}
else
{
lean_object* x_2609; lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; lean_object* x_2613; lean_object* x_2614; lean_object* x_2615; lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; lean_object* x_2620; 
x_2609 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2609, 0, x_1);
x_2610 = l_Lean_KernelException_toMessageData___closed__15;
x_2611 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2611, 0, x_2610);
lean_ctor_set(x_2611, 1, x_2609);
x_2612 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2613 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2613, 0, x_2611);
lean_ctor_set(x_2613, 1, x_2612);
x_2614 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2614, 0, x_2);
x_2615 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2615, 0, x_2613);
lean_ctor_set(x_2615, 1, x_2614);
x_2616 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2616, 0, x_2615);
lean_ctor_set(x_2616, 1, x_2610);
x_2617 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2618 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2617, x_2616, x_3, x_4, x_5, x_6, x_2607);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2619 = lean_ctor_get(x_2618, 1);
lean_inc(x_2619);
lean_dec(x_2618);
x_2620 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2619);
return x_2620;
}
}
}
}
else
{
lean_object* x_2645; uint8_t x_2646; 
lean_free_object(x_2598);
x_2645 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2601);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2646 = !lean_is_exclusive(x_2645);
if (x_2646 == 0)
{
lean_object* x_2647; uint8_t x_2648; lean_object* x_2649; 
x_2647 = lean_ctor_get(x_2645, 0);
lean_dec(x_2647);
x_2648 = 1;
x_2649 = lean_box(x_2648);
lean_ctor_set(x_2645, 0, x_2649);
return x_2645;
}
else
{
lean_object* x_2650; uint8_t x_2651; lean_object* x_2652; lean_object* x_2653; 
x_2650 = lean_ctor_get(x_2645, 1);
lean_inc(x_2650);
lean_dec(x_2645);
x_2651 = 1;
x_2652 = lean_box(x_2651);
x_2653 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2653, 0, x_2652);
lean_ctor_set(x_2653, 1, x_2650);
return x_2653;
}
}
}
else
{
lean_object* x_2654; uint8_t x_2655; 
lean_dec(x_2602);
lean_free_object(x_2598);
x_2654 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2601);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2655 = !lean_is_exclusive(x_2654);
if (x_2655 == 0)
{
lean_object* x_2656; uint8_t x_2657; lean_object* x_2658; 
x_2656 = lean_ctor_get(x_2654, 0);
lean_dec(x_2656);
x_2657 = 1;
x_2658 = lean_box(x_2657);
lean_ctor_set(x_2654, 0, x_2658);
return x_2654;
}
else
{
lean_object* x_2659; uint8_t x_2660; lean_object* x_2661; lean_object* x_2662; 
x_2659 = lean_ctor_get(x_2654, 1);
lean_inc(x_2659);
lean_dec(x_2654);
x_2660 = 1;
x_2661 = lean_box(x_2660);
x_2662 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2662, 0, x_2661);
lean_ctor_set(x_2662, 1, x_2659);
return x_2662;
}
}
}
else
{
lean_object* x_2663; lean_object* x_2664; lean_object* x_2665; uint8_t x_2666; 
x_2663 = lean_ctor_get(x_2598, 0);
x_2664 = lean_ctor_get(x_2598, 1);
lean_inc(x_2664);
lean_inc(x_2663);
lean_dec(x_2598);
x_2665 = lean_ctor_get(x_2663, 0);
lean_inc(x_2665);
lean_dec(x_2663);
lean_inc(x_2665);
x_2666 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2665, x_1);
if (x_2666 == 0)
{
uint8_t x_2667; 
x_2667 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2665, x_2);
if (x_2667 == 0)
{
lean_object* x_2668; lean_object* x_2698; uint8_t x_2699; 
x_2698 = lean_ctor_get(x_3, 0);
lean_inc(x_2698);
x_2699 = lean_ctor_get_uint8(x_2698, 4);
lean_dec(x_2698);
if (x_2699 == 0)
{
uint8_t x_2700; lean_object* x_2701; lean_object* x_2702; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2700 = 0;
x_2701 = lean_box(x_2700);
x_2702 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2702, 0, x_2701);
lean_ctor_set(x_2702, 1, x_2664);
return x_2702;
}
else
{
uint8_t x_2703; 
x_2703 = l_Lean_Level_isMVar(x_1);
if (x_2703 == 0)
{
uint8_t x_2704; 
x_2704 = l_Lean_Level_isMVar(x_2);
if (x_2704 == 0)
{
uint8_t x_2705; lean_object* x_2706; lean_object* x_2707; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2705 = 0;
x_2706 = lean_box(x_2705);
x_2707 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2707, 0, x_2706);
lean_ctor_set(x_2707, 1, x_2664);
return x_2707;
}
else
{
lean_object* x_2708; 
x_2708 = lean_box(0);
x_2668 = x_2708;
goto block_2697;
}
}
else
{
lean_object* x_2709; 
x_2709 = lean_box(0);
x_2668 = x_2709;
goto block_2697;
}
}
block_2697:
{
uint8_t x_2669; lean_object* x_2670; lean_object* x_2685; lean_object* x_2686; lean_object* x_2687; uint8_t x_2688; 
lean_dec(x_2668);
x_2685 = lean_st_ref_get(x_6, x_2664);
x_2686 = lean_ctor_get(x_2685, 0);
lean_inc(x_2686);
x_2687 = lean_ctor_get(x_2686, 3);
lean_inc(x_2687);
lean_dec(x_2686);
x_2688 = lean_ctor_get_uint8(x_2687, sizeof(void*)*1);
lean_dec(x_2687);
if (x_2688 == 0)
{
lean_object* x_2689; uint8_t x_2690; 
x_2689 = lean_ctor_get(x_2685, 1);
lean_inc(x_2689);
lean_dec(x_2685);
x_2690 = 0;
x_2669 = x_2690;
x_2670 = x_2689;
goto block_2684;
}
else
{
lean_object* x_2691; lean_object* x_2692; lean_object* x_2693; lean_object* x_2694; lean_object* x_2695; uint8_t x_2696; 
x_2691 = lean_ctor_get(x_2685, 1);
lean_inc(x_2691);
lean_dec(x_2685);
x_2692 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2693 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2692, x_3, x_4, x_5, x_6, x_2691);
x_2694 = lean_ctor_get(x_2693, 0);
lean_inc(x_2694);
x_2695 = lean_ctor_get(x_2693, 1);
lean_inc(x_2695);
lean_dec(x_2693);
x_2696 = lean_unbox(x_2694);
lean_dec(x_2694);
x_2669 = x_2696;
x_2670 = x_2695;
goto block_2684;
}
block_2684:
{
if (x_2669 == 0)
{
lean_object* x_2671; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2671 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2670);
return x_2671;
}
else
{
lean_object* x_2672; lean_object* x_2673; lean_object* x_2674; lean_object* x_2675; lean_object* x_2676; lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; lean_object* x_2681; lean_object* x_2682; lean_object* x_2683; 
x_2672 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2672, 0, x_1);
x_2673 = l_Lean_KernelException_toMessageData___closed__15;
x_2674 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2674, 0, x_2673);
lean_ctor_set(x_2674, 1, x_2672);
x_2675 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2676 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2676, 0, x_2674);
lean_ctor_set(x_2676, 1, x_2675);
x_2677 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2677, 0, x_2);
x_2678 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2678, 0, x_2676);
lean_ctor_set(x_2678, 1, x_2677);
x_2679 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2679, 0, x_2678);
lean_ctor_set(x_2679, 1, x_2673);
x_2680 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2681 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2680, x_2679, x_3, x_4, x_5, x_6, x_2670);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2682 = lean_ctor_get(x_2681, 1);
lean_inc(x_2682);
lean_dec(x_2681);
x_2683 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2682);
return x_2683;
}
}
}
}
else
{
lean_object* x_2710; lean_object* x_2711; lean_object* x_2712; uint8_t x_2713; lean_object* x_2714; lean_object* x_2715; 
x_2710 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2664);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2711 = lean_ctor_get(x_2710, 1);
lean_inc(x_2711);
if (lean_is_exclusive(x_2710)) {
 lean_ctor_release(x_2710, 0);
 lean_ctor_release(x_2710, 1);
 x_2712 = x_2710;
} else {
 lean_dec_ref(x_2710);
 x_2712 = lean_box(0);
}
x_2713 = 1;
x_2714 = lean_box(x_2713);
if (lean_is_scalar(x_2712)) {
 x_2715 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2715 = x_2712;
}
lean_ctor_set(x_2715, 0, x_2714);
lean_ctor_set(x_2715, 1, x_2711);
return x_2715;
}
}
else
{
lean_object* x_2716; lean_object* x_2717; lean_object* x_2718; uint8_t x_2719; lean_object* x_2720; lean_object* x_2721; 
lean_dec(x_2665);
x_2716 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2664);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2717 = lean_ctor_get(x_2716, 1);
lean_inc(x_2717);
if (lean_is_exclusive(x_2716)) {
 lean_ctor_release(x_2716, 0);
 lean_ctor_release(x_2716, 1);
 x_2718 = x_2716;
} else {
 lean_dec_ref(x_2716);
 x_2718 = lean_box(0);
}
x_2719 = 1;
x_2720 = lean_box(x_2719);
if (lean_is_scalar(x_2718)) {
 x_2721 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2721 = x_2718;
}
lean_ctor_set(x_2721, 0, x_2720);
lean_ctor_set(x_2721, 1, x_2717);
return x_2721;
}
}
}
}
else
{
lean_object* x_2722; lean_object* x_2723; uint8_t x_2724; uint8_t x_2725; 
x_2722 = lean_ctor_get(x_2586, 0);
x_2723 = lean_ctor_get(x_2586, 1);
lean_inc(x_2723);
lean_inc(x_2722);
lean_dec(x_2586);
x_2724 = lean_unbox(x_2722);
x_2725 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2724, x_2579);
if (x_2725 == 0)
{
uint8_t x_2726; uint8_t x_2727; uint8_t x_2728; lean_object* x_2729; lean_object* x_2730; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2726 = 1;
x_2727 = lean_unbox(x_2722);
lean_dec(x_2722);
x_2728 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2727, x_2726);
x_2729 = lean_box(x_2728);
x_2730 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2730, 0, x_2729);
lean_ctor_set(x_2730, 1, x_2723);
return x_2730;
}
else
{
lean_object* x_2731; lean_object* x_2732; lean_object* x_2733; lean_object* x_2734; lean_object* x_2735; lean_object* x_2736; lean_object* x_2737; uint8_t x_2738; 
lean_dec(x_2722);
x_2731 = lean_st_ref_get(x_6, x_2723);
x_2732 = lean_ctor_get(x_2731, 1);
lean_inc(x_2732);
lean_dec(x_2731);
x_2733 = lean_st_ref_get(x_4, x_2732);
x_2734 = lean_ctor_get(x_2733, 0);
lean_inc(x_2734);
x_2735 = lean_ctor_get(x_2733, 1);
lean_inc(x_2735);
if (lean_is_exclusive(x_2733)) {
 lean_ctor_release(x_2733, 0);
 lean_ctor_release(x_2733, 1);
 x_2736 = x_2733;
} else {
 lean_dec_ref(x_2733);
 x_2736 = lean_box(0);
}
x_2737 = lean_ctor_get(x_2734, 0);
lean_inc(x_2737);
lean_dec(x_2734);
lean_inc(x_2737);
x_2738 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2737, x_1);
if (x_2738 == 0)
{
uint8_t x_2739; 
x_2739 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2737, x_2);
if (x_2739 == 0)
{
lean_object* x_2740; lean_object* x_2770; uint8_t x_2771; 
x_2770 = lean_ctor_get(x_3, 0);
lean_inc(x_2770);
x_2771 = lean_ctor_get_uint8(x_2770, 4);
lean_dec(x_2770);
if (x_2771 == 0)
{
uint8_t x_2772; lean_object* x_2773; lean_object* x_2774; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2772 = 0;
x_2773 = lean_box(x_2772);
if (lean_is_scalar(x_2736)) {
 x_2774 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2774 = x_2736;
}
lean_ctor_set(x_2774, 0, x_2773);
lean_ctor_set(x_2774, 1, x_2735);
return x_2774;
}
else
{
uint8_t x_2775; 
x_2775 = l_Lean_Level_isMVar(x_1);
if (x_2775 == 0)
{
uint8_t x_2776; 
x_2776 = l_Lean_Level_isMVar(x_2);
if (x_2776 == 0)
{
uint8_t x_2777; lean_object* x_2778; lean_object* x_2779; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2777 = 0;
x_2778 = lean_box(x_2777);
if (lean_is_scalar(x_2736)) {
 x_2779 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2779 = x_2736;
}
lean_ctor_set(x_2779, 0, x_2778);
lean_ctor_set(x_2779, 1, x_2735);
return x_2779;
}
else
{
lean_object* x_2780; 
lean_dec(x_2736);
x_2780 = lean_box(0);
x_2740 = x_2780;
goto block_2769;
}
}
else
{
lean_object* x_2781; 
lean_dec(x_2736);
x_2781 = lean_box(0);
x_2740 = x_2781;
goto block_2769;
}
}
block_2769:
{
uint8_t x_2741; lean_object* x_2742; lean_object* x_2757; lean_object* x_2758; lean_object* x_2759; uint8_t x_2760; 
lean_dec(x_2740);
x_2757 = lean_st_ref_get(x_6, x_2735);
x_2758 = lean_ctor_get(x_2757, 0);
lean_inc(x_2758);
x_2759 = lean_ctor_get(x_2758, 3);
lean_inc(x_2759);
lean_dec(x_2758);
x_2760 = lean_ctor_get_uint8(x_2759, sizeof(void*)*1);
lean_dec(x_2759);
if (x_2760 == 0)
{
lean_object* x_2761; uint8_t x_2762; 
x_2761 = lean_ctor_get(x_2757, 1);
lean_inc(x_2761);
lean_dec(x_2757);
x_2762 = 0;
x_2741 = x_2762;
x_2742 = x_2761;
goto block_2756;
}
else
{
lean_object* x_2763; lean_object* x_2764; lean_object* x_2765; lean_object* x_2766; lean_object* x_2767; uint8_t x_2768; 
x_2763 = lean_ctor_get(x_2757, 1);
lean_inc(x_2763);
lean_dec(x_2757);
x_2764 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2765 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2764, x_3, x_4, x_5, x_6, x_2763);
x_2766 = lean_ctor_get(x_2765, 0);
lean_inc(x_2766);
x_2767 = lean_ctor_get(x_2765, 1);
lean_inc(x_2767);
lean_dec(x_2765);
x_2768 = lean_unbox(x_2766);
lean_dec(x_2766);
x_2741 = x_2768;
x_2742 = x_2767;
goto block_2756;
}
block_2756:
{
if (x_2741 == 0)
{
lean_object* x_2743; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2743 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2742);
return x_2743;
}
else
{
lean_object* x_2744; lean_object* x_2745; lean_object* x_2746; lean_object* x_2747; lean_object* x_2748; lean_object* x_2749; lean_object* x_2750; lean_object* x_2751; lean_object* x_2752; lean_object* x_2753; lean_object* x_2754; lean_object* x_2755; 
x_2744 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2744, 0, x_1);
x_2745 = l_Lean_KernelException_toMessageData___closed__15;
x_2746 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2746, 0, x_2745);
lean_ctor_set(x_2746, 1, x_2744);
x_2747 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2748 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2748, 0, x_2746);
lean_ctor_set(x_2748, 1, x_2747);
x_2749 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2749, 0, x_2);
x_2750 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2750, 0, x_2748);
lean_ctor_set(x_2750, 1, x_2749);
x_2751 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2751, 0, x_2750);
lean_ctor_set(x_2751, 1, x_2745);
x_2752 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2753 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2752, x_2751, x_3, x_4, x_5, x_6, x_2742);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2754 = lean_ctor_get(x_2753, 1);
lean_inc(x_2754);
lean_dec(x_2753);
x_2755 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2754);
return x_2755;
}
}
}
}
else
{
lean_object* x_2782; lean_object* x_2783; lean_object* x_2784; uint8_t x_2785; lean_object* x_2786; lean_object* x_2787; 
lean_dec(x_2736);
x_2782 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2735);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2783 = lean_ctor_get(x_2782, 1);
lean_inc(x_2783);
if (lean_is_exclusive(x_2782)) {
 lean_ctor_release(x_2782, 0);
 lean_ctor_release(x_2782, 1);
 x_2784 = x_2782;
} else {
 lean_dec_ref(x_2782);
 x_2784 = lean_box(0);
}
x_2785 = 1;
x_2786 = lean_box(x_2785);
if (lean_is_scalar(x_2784)) {
 x_2787 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2787 = x_2784;
}
lean_ctor_set(x_2787, 0, x_2786);
lean_ctor_set(x_2787, 1, x_2783);
return x_2787;
}
}
else
{
lean_object* x_2788; lean_object* x_2789; lean_object* x_2790; uint8_t x_2791; lean_object* x_2792; lean_object* x_2793; 
lean_dec(x_2737);
lean_dec(x_2736);
x_2788 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2735);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2789 = lean_ctor_get(x_2788, 1);
lean_inc(x_2789);
if (lean_is_exclusive(x_2788)) {
 lean_ctor_release(x_2788, 0);
 lean_ctor_release(x_2788, 1);
 x_2790 = x_2788;
} else {
 lean_dec_ref(x_2788);
 x_2790 = lean_box(0);
}
x_2791 = 1;
x_2792 = lean_box(x_2791);
if (lean_is_scalar(x_2790)) {
 x_2793 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2793 = x_2790;
}
lean_ctor_set(x_2793, 0, x_2792);
lean_ctor_set(x_2793, 1, x_2789);
return x_2793;
}
}
}
}
else
{
uint8_t x_2794; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2794 = !lean_is_exclusive(x_2586);
if (x_2794 == 0)
{
return x_2586;
}
else
{
lean_object* x_2795; lean_object* x_2796; lean_object* x_2797; 
x_2795 = lean_ctor_get(x_2586, 0);
x_2796 = lean_ctor_get(x_2586, 1);
lean_inc(x_2796);
lean_inc(x_2795);
lean_dec(x_2586);
x_2797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2797, 0, x_2795);
lean_ctor_set(x_2797, 1, x_2796);
return x_2797;
}
}
}
}
else
{
lean_object* x_2798; lean_object* x_2799; uint8_t x_2800; uint8_t x_2801; uint8_t x_2802; 
x_2798 = lean_ctor_get(x_2575, 0);
x_2799 = lean_ctor_get(x_2575, 1);
lean_inc(x_2799);
lean_inc(x_2798);
lean_dec(x_2575);
x_2800 = 2;
x_2801 = lean_unbox(x_2798);
x_2802 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2801, x_2800);
if (x_2802 == 0)
{
uint8_t x_2803; uint8_t x_2804; uint8_t x_2805; lean_object* x_2806; lean_object* x_2807; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2803 = 1;
x_2804 = lean_unbox(x_2798);
lean_dec(x_2798);
x_2805 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2804, x_2803);
x_2806 = lean_box(x_2805);
x_2807 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2807, 0, x_2806);
lean_ctor_set(x_2807, 1, x_2799);
return x_2807;
}
else
{
lean_object* x_2808; 
lean_dec(x_2798);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_2808 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_2799);
if (lean_obj_tag(x_2808) == 0)
{
lean_object* x_2809; lean_object* x_2810; lean_object* x_2811; uint8_t x_2812; uint8_t x_2813; 
x_2809 = lean_ctor_get(x_2808, 0);
lean_inc(x_2809);
x_2810 = lean_ctor_get(x_2808, 1);
lean_inc(x_2810);
if (lean_is_exclusive(x_2808)) {
 lean_ctor_release(x_2808, 0);
 lean_ctor_release(x_2808, 1);
 x_2811 = x_2808;
} else {
 lean_dec_ref(x_2808);
 x_2811 = lean_box(0);
}
x_2812 = lean_unbox(x_2809);
x_2813 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2812, x_2800);
if (x_2813 == 0)
{
uint8_t x_2814; uint8_t x_2815; uint8_t x_2816; lean_object* x_2817; lean_object* x_2818; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2814 = 1;
x_2815 = lean_unbox(x_2809);
lean_dec(x_2809);
x_2816 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2815, x_2814);
x_2817 = lean_box(x_2816);
if (lean_is_scalar(x_2811)) {
 x_2818 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2818 = x_2811;
}
lean_ctor_set(x_2818, 0, x_2817);
lean_ctor_set(x_2818, 1, x_2810);
return x_2818;
}
else
{
lean_object* x_2819; lean_object* x_2820; lean_object* x_2821; lean_object* x_2822; lean_object* x_2823; lean_object* x_2824; lean_object* x_2825; uint8_t x_2826; 
lean_dec(x_2811);
lean_dec(x_2809);
x_2819 = lean_st_ref_get(x_6, x_2810);
x_2820 = lean_ctor_get(x_2819, 1);
lean_inc(x_2820);
lean_dec(x_2819);
x_2821 = lean_st_ref_get(x_4, x_2820);
x_2822 = lean_ctor_get(x_2821, 0);
lean_inc(x_2822);
x_2823 = lean_ctor_get(x_2821, 1);
lean_inc(x_2823);
if (lean_is_exclusive(x_2821)) {
 lean_ctor_release(x_2821, 0);
 lean_ctor_release(x_2821, 1);
 x_2824 = x_2821;
} else {
 lean_dec_ref(x_2821);
 x_2824 = lean_box(0);
}
x_2825 = lean_ctor_get(x_2822, 0);
lean_inc(x_2825);
lean_dec(x_2822);
lean_inc(x_2825);
x_2826 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2825, x_1);
if (x_2826 == 0)
{
uint8_t x_2827; 
x_2827 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2825, x_2);
if (x_2827 == 0)
{
lean_object* x_2828; lean_object* x_2858; uint8_t x_2859; 
x_2858 = lean_ctor_get(x_3, 0);
lean_inc(x_2858);
x_2859 = lean_ctor_get_uint8(x_2858, 4);
lean_dec(x_2858);
if (x_2859 == 0)
{
uint8_t x_2860; lean_object* x_2861; lean_object* x_2862; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2860 = 0;
x_2861 = lean_box(x_2860);
if (lean_is_scalar(x_2824)) {
 x_2862 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2862 = x_2824;
}
lean_ctor_set(x_2862, 0, x_2861);
lean_ctor_set(x_2862, 1, x_2823);
return x_2862;
}
else
{
uint8_t x_2863; 
x_2863 = l_Lean_Level_isMVar(x_1);
if (x_2863 == 0)
{
uint8_t x_2864; 
x_2864 = l_Lean_Level_isMVar(x_2);
if (x_2864 == 0)
{
uint8_t x_2865; lean_object* x_2866; lean_object* x_2867; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2865 = 0;
x_2866 = lean_box(x_2865);
if (lean_is_scalar(x_2824)) {
 x_2867 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2867 = x_2824;
}
lean_ctor_set(x_2867, 0, x_2866);
lean_ctor_set(x_2867, 1, x_2823);
return x_2867;
}
else
{
lean_object* x_2868; 
lean_dec(x_2824);
x_2868 = lean_box(0);
x_2828 = x_2868;
goto block_2857;
}
}
else
{
lean_object* x_2869; 
lean_dec(x_2824);
x_2869 = lean_box(0);
x_2828 = x_2869;
goto block_2857;
}
}
block_2857:
{
uint8_t x_2829; lean_object* x_2830; lean_object* x_2845; lean_object* x_2846; lean_object* x_2847; uint8_t x_2848; 
lean_dec(x_2828);
x_2845 = lean_st_ref_get(x_6, x_2823);
x_2846 = lean_ctor_get(x_2845, 0);
lean_inc(x_2846);
x_2847 = lean_ctor_get(x_2846, 3);
lean_inc(x_2847);
lean_dec(x_2846);
x_2848 = lean_ctor_get_uint8(x_2847, sizeof(void*)*1);
lean_dec(x_2847);
if (x_2848 == 0)
{
lean_object* x_2849; uint8_t x_2850; 
x_2849 = lean_ctor_get(x_2845, 1);
lean_inc(x_2849);
lean_dec(x_2845);
x_2850 = 0;
x_2829 = x_2850;
x_2830 = x_2849;
goto block_2844;
}
else
{
lean_object* x_2851; lean_object* x_2852; lean_object* x_2853; lean_object* x_2854; lean_object* x_2855; uint8_t x_2856; 
x_2851 = lean_ctor_get(x_2845, 1);
lean_inc(x_2851);
lean_dec(x_2845);
x_2852 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2853 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2852, x_3, x_4, x_5, x_6, x_2851);
x_2854 = lean_ctor_get(x_2853, 0);
lean_inc(x_2854);
x_2855 = lean_ctor_get(x_2853, 1);
lean_inc(x_2855);
lean_dec(x_2853);
x_2856 = lean_unbox(x_2854);
lean_dec(x_2854);
x_2829 = x_2856;
x_2830 = x_2855;
goto block_2844;
}
block_2844:
{
if (x_2829 == 0)
{
lean_object* x_2831; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2831 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2830);
return x_2831;
}
else
{
lean_object* x_2832; lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; lean_object* x_2836; lean_object* x_2837; lean_object* x_2838; lean_object* x_2839; lean_object* x_2840; lean_object* x_2841; lean_object* x_2842; lean_object* x_2843; 
x_2832 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2832, 0, x_1);
x_2833 = l_Lean_KernelException_toMessageData___closed__15;
x_2834 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2834, 0, x_2833);
lean_ctor_set(x_2834, 1, x_2832);
x_2835 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2836 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2836, 0, x_2834);
lean_ctor_set(x_2836, 1, x_2835);
x_2837 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2837, 0, x_2);
x_2838 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2838, 0, x_2836);
lean_ctor_set(x_2838, 1, x_2837);
x_2839 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2839, 0, x_2838);
lean_ctor_set(x_2839, 1, x_2833);
x_2840 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2841 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2840, x_2839, x_3, x_4, x_5, x_6, x_2830);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2842 = lean_ctor_get(x_2841, 1);
lean_inc(x_2842);
lean_dec(x_2841);
x_2843 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2842);
return x_2843;
}
}
}
}
else
{
lean_object* x_2870; lean_object* x_2871; lean_object* x_2872; uint8_t x_2873; lean_object* x_2874; lean_object* x_2875; 
lean_dec(x_2824);
x_2870 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2823);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2871 = lean_ctor_get(x_2870, 1);
lean_inc(x_2871);
if (lean_is_exclusive(x_2870)) {
 lean_ctor_release(x_2870, 0);
 lean_ctor_release(x_2870, 1);
 x_2872 = x_2870;
} else {
 lean_dec_ref(x_2870);
 x_2872 = lean_box(0);
}
x_2873 = 1;
x_2874 = lean_box(x_2873);
if (lean_is_scalar(x_2872)) {
 x_2875 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2875 = x_2872;
}
lean_ctor_set(x_2875, 0, x_2874);
lean_ctor_set(x_2875, 1, x_2871);
return x_2875;
}
}
else
{
lean_object* x_2876; lean_object* x_2877; lean_object* x_2878; uint8_t x_2879; lean_object* x_2880; lean_object* x_2881; 
lean_dec(x_2825);
lean_dec(x_2824);
x_2876 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2823);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2877 = lean_ctor_get(x_2876, 1);
lean_inc(x_2877);
if (lean_is_exclusive(x_2876)) {
 lean_ctor_release(x_2876, 0);
 lean_ctor_release(x_2876, 1);
 x_2878 = x_2876;
} else {
 lean_dec_ref(x_2876);
 x_2878 = lean_box(0);
}
x_2879 = 1;
x_2880 = lean_box(x_2879);
if (lean_is_scalar(x_2878)) {
 x_2881 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2881 = x_2878;
}
lean_ctor_set(x_2881, 0, x_2880);
lean_ctor_set(x_2881, 1, x_2877);
return x_2881;
}
}
}
else
{
lean_object* x_2882; lean_object* x_2883; lean_object* x_2884; lean_object* x_2885; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2882 = lean_ctor_get(x_2808, 0);
lean_inc(x_2882);
x_2883 = lean_ctor_get(x_2808, 1);
lean_inc(x_2883);
if (lean_is_exclusive(x_2808)) {
 lean_ctor_release(x_2808, 0);
 lean_ctor_release(x_2808, 1);
 x_2884 = x_2808;
} else {
 lean_dec_ref(x_2808);
 x_2884 = lean_box(0);
}
if (lean_is_scalar(x_2884)) {
 x_2885 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2885 = x_2884;
}
lean_ctor_set(x_2885, 0, x_2882);
lean_ctor_set(x_2885, 1, x_2883);
return x_2885;
}
}
}
}
else
{
uint8_t x_2886; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2886 = !lean_is_exclusive(x_2575);
if (x_2886 == 0)
{
return x_2575;
}
else
{
lean_object* x_2887; lean_object* x_2888; lean_object* x_2889; 
x_2887 = lean_ctor_get(x_2575, 0);
x_2888 = lean_ctor_get(x_2575, 1);
lean_inc(x_2888);
lean_inc(x_2887);
lean_dec(x_2575);
x_2889 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2889, 0, x_2887);
lean_ctor_set(x_2889, 1, x_2888);
return x_2889;
}
}
}
}
}
block_2904:
{
if (x_2891 == 0)
{
x_2562 = x_2892;
goto block_2890;
}
else
{
lean_object* x_2893; lean_object* x_2894; lean_object* x_2895; lean_object* x_2896; lean_object* x_2897; lean_object* x_2898; lean_object* x_2899; lean_object* x_2900; lean_object* x_2901; lean_object* x_2902; lean_object* x_2903; 
lean_inc(x_1);
x_2893 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2893, 0, x_1);
x_2894 = l_Lean_KernelException_toMessageData___closed__15;
x_2895 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2895, 0, x_2894);
lean_ctor_set(x_2895, 1, x_2893);
x_2896 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2897 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2897, 0, x_2895);
lean_ctor_set(x_2897, 1, x_2896);
lean_inc(x_2);
x_2898 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2898, 0, x_2);
x_2899 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2899, 0, x_2897);
lean_ctor_set(x_2899, 1, x_2898);
x_2900 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2900, 0, x_2899);
lean_ctor_set(x_2900, 1, x_2894);
x_2901 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_2902 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2901, x_2900, x_3, x_4, x_5, x_6, x_2892);
x_2903 = lean_ctor_get(x_2902, 1);
lean_inc(x_2903);
lean_dec(x_2902);
x_2562 = x_2903;
goto block_2890;
}
}
}
else
{
lean_object* x_2917; lean_object* x_2918; lean_object* x_2919; uint8_t x_2920; lean_object* x_2921; lean_object* x_2922; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2917 = lean_unsigned_to_nat(0u);
x_2918 = l_Lean_Level_getOffsetAux(x_1, x_2917);
lean_dec(x_1);
x_2919 = l_Lean_Level_getOffsetAux(x_2, x_2917);
lean_dec(x_2);
x_2920 = lean_nat_dec_eq(x_2918, x_2919);
lean_dec(x_2919);
lean_dec(x_2918);
x_2921 = lean_box(x_2920);
x_2922 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2922, 0, x_2921);
lean_ctor_set(x_2922, 1, x_7);
return x_2922;
}
}
case 4:
{
lean_object* x_2923; lean_object* x_2924; uint8_t x_2925; 
x_2923 = l_Lean_Level_getLevelOffset(x_1);
x_2924 = l_Lean_Level_getLevelOffset(x_2);
x_2925 = lean_level_eq(x_2923, x_2924);
lean_dec(x_2924);
lean_dec(x_2923);
if (x_2925 == 0)
{
lean_object* x_2926; uint8_t x_3255; lean_object* x_3256; lean_object* x_3269; lean_object* x_3270; lean_object* x_3271; uint8_t x_3272; 
x_3269 = lean_st_ref_get(x_6, x_7);
x_3270 = lean_ctor_get(x_3269, 0);
lean_inc(x_3270);
x_3271 = lean_ctor_get(x_3270, 3);
lean_inc(x_3271);
lean_dec(x_3270);
x_3272 = lean_ctor_get_uint8(x_3271, sizeof(void*)*1);
lean_dec(x_3271);
if (x_3272 == 0)
{
lean_object* x_3273; uint8_t x_3274; 
x_3273 = lean_ctor_get(x_3269, 1);
lean_inc(x_3273);
lean_dec(x_3269);
x_3274 = 0;
x_3255 = x_3274;
x_3256 = x_3273;
goto block_3268;
}
else
{
lean_object* x_3275; lean_object* x_3276; lean_object* x_3277; lean_object* x_3278; lean_object* x_3279; uint8_t x_3280; 
x_3275 = lean_ctor_get(x_3269, 1);
lean_inc(x_3275);
lean_dec(x_3269);
x_3276 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_3277 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_3276, x_3, x_4, x_5, x_6, x_3275);
x_3278 = lean_ctor_get(x_3277, 0);
lean_inc(x_3278);
x_3279 = lean_ctor_get(x_3277, 1);
lean_inc(x_3279);
lean_dec(x_3277);
x_3280 = lean_unbox(x_3278);
lean_dec(x_3278);
x_3255 = x_3280;
x_3256 = x_3279;
goto block_3268;
}
block_3254:
{
lean_object* x_2927; lean_object* x_2928; lean_object* x_2929; lean_object* x_2930; lean_object* x_2931; lean_object* x_2932; lean_object* x_2933; lean_object* x_2934; uint8_t x_2935; 
lean_inc(x_1);
x_2927 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_2926);
x_2928 = lean_ctor_get(x_2927, 0);
lean_inc(x_2928);
x_2929 = lean_ctor_get(x_2927, 1);
lean_inc(x_2929);
lean_dec(x_2927);
x_2930 = l_Lean_Level_normalize(x_2928);
lean_dec(x_2928);
lean_inc(x_2);
x_2931 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_2, x_3, x_4, x_5, x_6, x_2929);
x_2932 = lean_ctor_get(x_2931, 0);
lean_inc(x_2932);
x_2933 = lean_ctor_get(x_2931, 1);
lean_inc(x_2933);
lean_dec(x_2931);
x_2934 = l_Lean_Level_normalize(x_2932);
lean_dec(x_2932);
x_2935 = lean_level_eq(x_1, x_2930);
if (x_2935 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_2930;
x_2 = x_2934;
x_7 = x_2933;
goto _start;
}
else
{
uint8_t x_2937; 
x_2937 = lean_level_eq(x_2, x_2934);
if (x_2937 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_2930;
x_2 = x_2934;
x_7 = x_2933;
goto _start;
}
else
{
lean_object* x_2939; 
lean_dec(x_2934);
lean_dec(x_2930);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_2939 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_2933);
if (lean_obj_tag(x_2939) == 0)
{
uint8_t x_2940; 
x_2940 = !lean_is_exclusive(x_2939);
if (x_2940 == 0)
{
lean_object* x_2941; lean_object* x_2942; uint8_t x_2943; uint8_t x_2944; uint8_t x_2945; 
x_2941 = lean_ctor_get(x_2939, 0);
x_2942 = lean_ctor_get(x_2939, 1);
x_2943 = 2;
x_2944 = lean_unbox(x_2941);
x_2945 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2944, x_2943);
if (x_2945 == 0)
{
uint8_t x_2946; uint8_t x_2947; uint8_t x_2948; lean_object* x_2949; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2946 = 1;
x_2947 = lean_unbox(x_2941);
lean_dec(x_2941);
x_2948 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2947, x_2946);
x_2949 = lean_box(x_2948);
lean_ctor_set(x_2939, 0, x_2949);
return x_2939;
}
else
{
lean_object* x_2950; 
lean_free_object(x_2939);
lean_dec(x_2941);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_2950 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_2942);
if (lean_obj_tag(x_2950) == 0)
{
uint8_t x_2951; 
x_2951 = !lean_is_exclusive(x_2950);
if (x_2951 == 0)
{
lean_object* x_2952; lean_object* x_2953; uint8_t x_2954; uint8_t x_2955; 
x_2952 = lean_ctor_get(x_2950, 0);
x_2953 = lean_ctor_get(x_2950, 1);
x_2954 = lean_unbox(x_2952);
x_2955 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2954, x_2943);
if (x_2955 == 0)
{
uint8_t x_2956; uint8_t x_2957; uint8_t x_2958; lean_object* x_2959; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2956 = 1;
x_2957 = lean_unbox(x_2952);
lean_dec(x_2952);
x_2958 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_2957, x_2956);
x_2959 = lean_box(x_2958);
lean_ctor_set(x_2950, 0, x_2959);
return x_2950;
}
else
{
lean_object* x_2960; lean_object* x_2961; lean_object* x_2962; uint8_t x_2963; 
lean_free_object(x_2950);
lean_dec(x_2952);
x_2960 = lean_st_ref_get(x_6, x_2953);
x_2961 = lean_ctor_get(x_2960, 1);
lean_inc(x_2961);
lean_dec(x_2960);
x_2962 = lean_st_ref_get(x_4, x_2961);
x_2963 = !lean_is_exclusive(x_2962);
if (x_2963 == 0)
{
lean_object* x_2964; lean_object* x_2965; lean_object* x_2966; uint8_t x_2967; 
x_2964 = lean_ctor_get(x_2962, 0);
x_2965 = lean_ctor_get(x_2962, 1);
x_2966 = lean_ctor_get(x_2964, 0);
lean_inc(x_2966);
lean_dec(x_2964);
lean_inc(x_2966);
x_2967 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2966, x_1);
if (x_2967 == 0)
{
uint8_t x_2968; 
x_2968 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_2966, x_2);
if (x_2968 == 0)
{
lean_object* x_2969; lean_object* x_2999; uint8_t x_3000; 
x_2999 = lean_ctor_get(x_3, 0);
lean_inc(x_2999);
x_3000 = lean_ctor_get_uint8(x_2999, 4);
lean_dec(x_2999);
if (x_3000 == 0)
{
uint8_t x_3001; lean_object* x_3002; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3001 = 0;
x_3002 = lean_box(x_3001);
lean_ctor_set(x_2962, 0, x_3002);
return x_2962;
}
else
{
uint8_t x_3003; 
x_3003 = l_Lean_Level_isMVar(x_1);
if (x_3003 == 0)
{
uint8_t x_3004; 
x_3004 = l_Lean_Level_isMVar(x_2);
if (x_3004 == 0)
{
uint8_t x_3005; lean_object* x_3006; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3005 = 0;
x_3006 = lean_box(x_3005);
lean_ctor_set(x_2962, 0, x_3006);
return x_2962;
}
else
{
lean_object* x_3007; 
lean_free_object(x_2962);
x_3007 = lean_box(0);
x_2969 = x_3007;
goto block_2998;
}
}
else
{
lean_object* x_3008; 
lean_free_object(x_2962);
x_3008 = lean_box(0);
x_2969 = x_3008;
goto block_2998;
}
}
block_2998:
{
uint8_t x_2970; lean_object* x_2971; lean_object* x_2986; lean_object* x_2987; lean_object* x_2988; uint8_t x_2989; 
lean_dec(x_2969);
x_2986 = lean_st_ref_get(x_6, x_2965);
x_2987 = lean_ctor_get(x_2986, 0);
lean_inc(x_2987);
x_2988 = lean_ctor_get(x_2987, 3);
lean_inc(x_2988);
lean_dec(x_2987);
x_2989 = lean_ctor_get_uint8(x_2988, sizeof(void*)*1);
lean_dec(x_2988);
if (x_2989 == 0)
{
lean_object* x_2990; uint8_t x_2991; 
x_2990 = lean_ctor_get(x_2986, 1);
lean_inc(x_2990);
lean_dec(x_2986);
x_2991 = 0;
x_2970 = x_2991;
x_2971 = x_2990;
goto block_2985;
}
else
{
lean_object* x_2992; lean_object* x_2993; lean_object* x_2994; lean_object* x_2995; lean_object* x_2996; uint8_t x_2997; 
x_2992 = lean_ctor_get(x_2986, 1);
lean_inc(x_2992);
lean_dec(x_2986);
x_2993 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2994 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_2993, x_3, x_4, x_5, x_6, x_2992);
x_2995 = lean_ctor_get(x_2994, 0);
lean_inc(x_2995);
x_2996 = lean_ctor_get(x_2994, 1);
lean_inc(x_2996);
lean_dec(x_2994);
x_2997 = lean_unbox(x_2995);
lean_dec(x_2995);
x_2970 = x_2997;
x_2971 = x_2996;
goto block_2985;
}
block_2985:
{
if (x_2970 == 0)
{
lean_object* x_2972; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2972 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2971);
return x_2972;
}
else
{
lean_object* x_2973; lean_object* x_2974; lean_object* x_2975; lean_object* x_2976; lean_object* x_2977; lean_object* x_2978; lean_object* x_2979; lean_object* x_2980; lean_object* x_2981; lean_object* x_2982; lean_object* x_2983; lean_object* x_2984; 
x_2973 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2973, 0, x_1);
x_2974 = l_Lean_KernelException_toMessageData___closed__15;
x_2975 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2975, 0, x_2974);
lean_ctor_set(x_2975, 1, x_2973);
x_2976 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_2977 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2977, 0, x_2975);
lean_ctor_set(x_2977, 1, x_2976);
x_2978 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2978, 0, x_2);
x_2979 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2979, 0, x_2977);
lean_ctor_set(x_2979, 1, x_2978);
x_2980 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2980, 0, x_2979);
lean_ctor_set(x_2980, 1, x_2974);
x_2981 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2982 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_2981, x_2980, x_3, x_4, x_5, x_6, x_2971);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2983 = lean_ctor_get(x_2982, 1);
lean_inc(x_2983);
lean_dec(x_2982);
x_2984 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_2983);
return x_2984;
}
}
}
}
else
{
lean_object* x_3009; uint8_t x_3010; 
lean_free_object(x_2962);
x_3009 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2965);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3010 = !lean_is_exclusive(x_3009);
if (x_3010 == 0)
{
lean_object* x_3011; uint8_t x_3012; lean_object* x_3013; 
x_3011 = lean_ctor_get(x_3009, 0);
lean_dec(x_3011);
x_3012 = 1;
x_3013 = lean_box(x_3012);
lean_ctor_set(x_3009, 0, x_3013);
return x_3009;
}
else
{
lean_object* x_3014; uint8_t x_3015; lean_object* x_3016; lean_object* x_3017; 
x_3014 = lean_ctor_get(x_3009, 1);
lean_inc(x_3014);
lean_dec(x_3009);
x_3015 = 1;
x_3016 = lean_box(x_3015);
x_3017 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3017, 0, x_3016);
lean_ctor_set(x_3017, 1, x_3014);
return x_3017;
}
}
}
else
{
lean_object* x_3018; uint8_t x_3019; 
lean_dec(x_2966);
lean_free_object(x_2962);
x_3018 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_2965);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3019 = !lean_is_exclusive(x_3018);
if (x_3019 == 0)
{
lean_object* x_3020; uint8_t x_3021; lean_object* x_3022; 
x_3020 = lean_ctor_get(x_3018, 0);
lean_dec(x_3020);
x_3021 = 1;
x_3022 = lean_box(x_3021);
lean_ctor_set(x_3018, 0, x_3022);
return x_3018;
}
else
{
lean_object* x_3023; uint8_t x_3024; lean_object* x_3025; lean_object* x_3026; 
x_3023 = lean_ctor_get(x_3018, 1);
lean_inc(x_3023);
lean_dec(x_3018);
x_3024 = 1;
x_3025 = lean_box(x_3024);
x_3026 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3026, 0, x_3025);
lean_ctor_set(x_3026, 1, x_3023);
return x_3026;
}
}
}
else
{
lean_object* x_3027; lean_object* x_3028; lean_object* x_3029; uint8_t x_3030; 
x_3027 = lean_ctor_get(x_2962, 0);
x_3028 = lean_ctor_get(x_2962, 1);
lean_inc(x_3028);
lean_inc(x_3027);
lean_dec(x_2962);
x_3029 = lean_ctor_get(x_3027, 0);
lean_inc(x_3029);
lean_dec(x_3027);
lean_inc(x_3029);
x_3030 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3029, x_1);
if (x_3030 == 0)
{
uint8_t x_3031; 
x_3031 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3029, x_2);
if (x_3031 == 0)
{
lean_object* x_3032; lean_object* x_3062; uint8_t x_3063; 
x_3062 = lean_ctor_get(x_3, 0);
lean_inc(x_3062);
x_3063 = lean_ctor_get_uint8(x_3062, 4);
lean_dec(x_3062);
if (x_3063 == 0)
{
uint8_t x_3064; lean_object* x_3065; lean_object* x_3066; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3064 = 0;
x_3065 = lean_box(x_3064);
x_3066 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3066, 0, x_3065);
lean_ctor_set(x_3066, 1, x_3028);
return x_3066;
}
else
{
uint8_t x_3067; 
x_3067 = l_Lean_Level_isMVar(x_1);
if (x_3067 == 0)
{
uint8_t x_3068; 
x_3068 = l_Lean_Level_isMVar(x_2);
if (x_3068 == 0)
{
uint8_t x_3069; lean_object* x_3070; lean_object* x_3071; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3069 = 0;
x_3070 = lean_box(x_3069);
x_3071 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3071, 0, x_3070);
lean_ctor_set(x_3071, 1, x_3028);
return x_3071;
}
else
{
lean_object* x_3072; 
x_3072 = lean_box(0);
x_3032 = x_3072;
goto block_3061;
}
}
else
{
lean_object* x_3073; 
x_3073 = lean_box(0);
x_3032 = x_3073;
goto block_3061;
}
}
block_3061:
{
uint8_t x_3033; lean_object* x_3034; lean_object* x_3049; lean_object* x_3050; lean_object* x_3051; uint8_t x_3052; 
lean_dec(x_3032);
x_3049 = lean_st_ref_get(x_6, x_3028);
x_3050 = lean_ctor_get(x_3049, 0);
lean_inc(x_3050);
x_3051 = lean_ctor_get(x_3050, 3);
lean_inc(x_3051);
lean_dec(x_3050);
x_3052 = lean_ctor_get_uint8(x_3051, sizeof(void*)*1);
lean_dec(x_3051);
if (x_3052 == 0)
{
lean_object* x_3053; uint8_t x_3054; 
x_3053 = lean_ctor_get(x_3049, 1);
lean_inc(x_3053);
lean_dec(x_3049);
x_3054 = 0;
x_3033 = x_3054;
x_3034 = x_3053;
goto block_3048;
}
else
{
lean_object* x_3055; lean_object* x_3056; lean_object* x_3057; lean_object* x_3058; lean_object* x_3059; uint8_t x_3060; 
x_3055 = lean_ctor_get(x_3049, 1);
lean_inc(x_3055);
lean_dec(x_3049);
x_3056 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3057 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_3056, x_3, x_4, x_5, x_6, x_3055);
x_3058 = lean_ctor_get(x_3057, 0);
lean_inc(x_3058);
x_3059 = lean_ctor_get(x_3057, 1);
lean_inc(x_3059);
lean_dec(x_3057);
x_3060 = lean_unbox(x_3058);
lean_dec(x_3058);
x_3033 = x_3060;
x_3034 = x_3059;
goto block_3048;
}
block_3048:
{
if (x_3033 == 0)
{
lean_object* x_3035; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3035 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3034);
return x_3035;
}
else
{
lean_object* x_3036; lean_object* x_3037; lean_object* x_3038; lean_object* x_3039; lean_object* x_3040; lean_object* x_3041; lean_object* x_3042; lean_object* x_3043; lean_object* x_3044; lean_object* x_3045; lean_object* x_3046; lean_object* x_3047; 
x_3036 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3036, 0, x_1);
x_3037 = l_Lean_KernelException_toMessageData___closed__15;
x_3038 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3038, 0, x_3037);
lean_ctor_set(x_3038, 1, x_3036);
x_3039 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_3040 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3040, 0, x_3038);
lean_ctor_set(x_3040, 1, x_3039);
x_3041 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3041, 0, x_2);
x_3042 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3042, 0, x_3040);
lean_ctor_set(x_3042, 1, x_3041);
x_3043 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3043, 0, x_3042);
lean_ctor_set(x_3043, 1, x_3037);
x_3044 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3045 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_3044, x_3043, x_3, x_4, x_5, x_6, x_3034);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3046 = lean_ctor_get(x_3045, 1);
lean_inc(x_3046);
lean_dec(x_3045);
x_3047 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3046);
return x_3047;
}
}
}
}
else
{
lean_object* x_3074; lean_object* x_3075; lean_object* x_3076; uint8_t x_3077; lean_object* x_3078; lean_object* x_3079; 
x_3074 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3028);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3075 = lean_ctor_get(x_3074, 1);
lean_inc(x_3075);
if (lean_is_exclusive(x_3074)) {
 lean_ctor_release(x_3074, 0);
 lean_ctor_release(x_3074, 1);
 x_3076 = x_3074;
} else {
 lean_dec_ref(x_3074);
 x_3076 = lean_box(0);
}
x_3077 = 1;
x_3078 = lean_box(x_3077);
if (lean_is_scalar(x_3076)) {
 x_3079 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3079 = x_3076;
}
lean_ctor_set(x_3079, 0, x_3078);
lean_ctor_set(x_3079, 1, x_3075);
return x_3079;
}
}
else
{
lean_object* x_3080; lean_object* x_3081; lean_object* x_3082; uint8_t x_3083; lean_object* x_3084; lean_object* x_3085; 
lean_dec(x_3029);
x_3080 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3028);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3081 = lean_ctor_get(x_3080, 1);
lean_inc(x_3081);
if (lean_is_exclusive(x_3080)) {
 lean_ctor_release(x_3080, 0);
 lean_ctor_release(x_3080, 1);
 x_3082 = x_3080;
} else {
 lean_dec_ref(x_3080);
 x_3082 = lean_box(0);
}
x_3083 = 1;
x_3084 = lean_box(x_3083);
if (lean_is_scalar(x_3082)) {
 x_3085 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3085 = x_3082;
}
lean_ctor_set(x_3085, 0, x_3084);
lean_ctor_set(x_3085, 1, x_3081);
return x_3085;
}
}
}
}
else
{
lean_object* x_3086; lean_object* x_3087; uint8_t x_3088; uint8_t x_3089; 
x_3086 = lean_ctor_get(x_2950, 0);
x_3087 = lean_ctor_get(x_2950, 1);
lean_inc(x_3087);
lean_inc(x_3086);
lean_dec(x_2950);
x_3088 = lean_unbox(x_3086);
x_3089 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3088, x_2943);
if (x_3089 == 0)
{
uint8_t x_3090; uint8_t x_3091; uint8_t x_3092; lean_object* x_3093; lean_object* x_3094; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3090 = 1;
x_3091 = lean_unbox(x_3086);
lean_dec(x_3086);
x_3092 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3091, x_3090);
x_3093 = lean_box(x_3092);
x_3094 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3094, 0, x_3093);
lean_ctor_set(x_3094, 1, x_3087);
return x_3094;
}
else
{
lean_object* x_3095; lean_object* x_3096; lean_object* x_3097; lean_object* x_3098; lean_object* x_3099; lean_object* x_3100; lean_object* x_3101; uint8_t x_3102; 
lean_dec(x_3086);
x_3095 = lean_st_ref_get(x_6, x_3087);
x_3096 = lean_ctor_get(x_3095, 1);
lean_inc(x_3096);
lean_dec(x_3095);
x_3097 = lean_st_ref_get(x_4, x_3096);
x_3098 = lean_ctor_get(x_3097, 0);
lean_inc(x_3098);
x_3099 = lean_ctor_get(x_3097, 1);
lean_inc(x_3099);
if (lean_is_exclusive(x_3097)) {
 lean_ctor_release(x_3097, 0);
 lean_ctor_release(x_3097, 1);
 x_3100 = x_3097;
} else {
 lean_dec_ref(x_3097);
 x_3100 = lean_box(0);
}
x_3101 = lean_ctor_get(x_3098, 0);
lean_inc(x_3101);
lean_dec(x_3098);
lean_inc(x_3101);
x_3102 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3101, x_1);
if (x_3102 == 0)
{
uint8_t x_3103; 
x_3103 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3101, x_2);
if (x_3103 == 0)
{
lean_object* x_3104; lean_object* x_3134; uint8_t x_3135; 
x_3134 = lean_ctor_get(x_3, 0);
lean_inc(x_3134);
x_3135 = lean_ctor_get_uint8(x_3134, 4);
lean_dec(x_3134);
if (x_3135 == 0)
{
uint8_t x_3136; lean_object* x_3137; lean_object* x_3138; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3136 = 0;
x_3137 = lean_box(x_3136);
if (lean_is_scalar(x_3100)) {
 x_3138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3138 = x_3100;
}
lean_ctor_set(x_3138, 0, x_3137);
lean_ctor_set(x_3138, 1, x_3099);
return x_3138;
}
else
{
uint8_t x_3139; 
x_3139 = l_Lean_Level_isMVar(x_1);
if (x_3139 == 0)
{
uint8_t x_3140; 
x_3140 = l_Lean_Level_isMVar(x_2);
if (x_3140 == 0)
{
uint8_t x_3141; lean_object* x_3142; lean_object* x_3143; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3141 = 0;
x_3142 = lean_box(x_3141);
if (lean_is_scalar(x_3100)) {
 x_3143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3143 = x_3100;
}
lean_ctor_set(x_3143, 0, x_3142);
lean_ctor_set(x_3143, 1, x_3099);
return x_3143;
}
else
{
lean_object* x_3144; 
lean_dec(x_3100);
x_3144 = lean_box(0);
x_3104 = x_3144;
goto block_3133;
}
}
else
{
lean_object* x_3145; 
lean_dec(x_3100);
x_3145 = lean_box(0);
x_3104 = x_3145;
goto block_3133;
}
}
block_3133:
{
uint8_t x_3105; lean_object* x_3106; lean_object* x_3121; lean_object* x_3122; lean_object* x_3123; uint8_t x_3124; 
lean_dec(x_3104);
x_3121 = lean_st_ref_get(x_6, x_3099);
x_3122 = lean_ctor_get(x_3121, 0);
lean_inc(x_3122);
x_3123 = lean_ctor_get(x_3122, 3);
lean_inc(x_3123);
lean_dec(x_3122);
x_3124 = lean_ctor_get_uint8(x_3123, sizeof(void*)*1);
lean_dec(x_3123);
if (x_3124 == 0)
{
lean_object* x_3125; uint8_t x_3126; 
x_3125 = lean_ctor_get(x_3121, 1);
lean_inc(x_3125);
lean_dec(x_3121);
x_3126 = 0;
x_3105 = x_3126;
x_3106 = x_3125;
goto block_3120;
}
else
{
lean_object* x_3127; lean_object* x_3128; lean_object* x_3129; lean_object* x_3130; lean_object* x_3131; uint8_t x_3132; 
x_3127 = lean_ctor_get(x_3121, 1);
lean_inc(x_3127);
lean_dec(x_3121);
x_3128 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3129 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_3128, x_3, x_4, x_5, x_6, x_3127);
x_3130 = lean_ctor_get(x_3129, 0);
lean_inc(x_3130);
x_3131 = lean_ctor_get(x_3129, 1);
lean_inc(x_3131);
lean_dec(x_3129);
x_3132 = lean_unbox(x_3130);
lean_dec(x_3130);
x_3105 = x_3132;
x_3106 = x_3131;
goto block_3120;
}
block_3120:
{
if (x_3105 == 0)
{
lean_object* x_3107; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3107 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3106);
return x_3107;
}
else
{
lean_object* x_3108; lean_object* x_3109; lean_object* x_3110; lean_object* x_3111; lean_object* x_3112; lean_object* x_3113; lean_object* x_3114; lean_object* x_3115; lean_object* x_3116; lean_object* x_3117; lean_object* x_3118; lean_object* x_3119; 
x_3108 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3108, 0, x_1);
x_3109 = l_Lean_KernelException_toMessageData___closed__15;
x_3110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3110, 0, x_3109);
lean_ctor_set(x_3110, 1, x_3108);
x_3111 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_3112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3112, 0, x_3110);
lean_ctor_set(x_3112, 1, x_3111);
x_3113 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3113, 0, x_2);
x_3114 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3114, 0, x_3112);
lean_ctor_set(x_3114, 1, x_3113);
x_3115 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3115, 0, x_3114);
lean_ctor_set(x_3115, 1, x_3109);
x_3116 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3117 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_3116, x_3115, x_3, x_4, x_5, x_6, x_3106);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3118 = lean_ctor_get(x_3117, 1);
lean_inc(x_3118);
lean_dec(x_3117);
x_3119 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3118);
return x_3119;
}
}
}
}
else
{
lean_object* x_3146; lean_object* x_3147; lean_object* x_3148; uint8_t x_3149; lean_object* x_3150; lean_object* x_3151; 
lean_dec(x_3100);
x_3146 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3099);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3147 = lean_ctor_get(x_3146, 1);
lean_inc(x_3147);
if (lean_is_exclusive(x_3146)) {
 lean_ctor_release(x_3146, 0);
 lean_ctor_release(x_3146, 1);
 x_3148 = x_3146;
} else {
 lean_dec_ref(x_3146);
 x_3148 = lean_box(0);
}
x_3149 = 1;
x_3150 = lean_box(x_3149);
if (lean_is_scalar(x_3148)) {
 x_3151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3151 = x_3148;
}
lean_ctor_set(x_3151, 0, x_3150);
lean_ctor_set(x_3151, 1, x_3147);
return x_3151;
}
}
else
{
lean_object* x_3152; lean_object* x_3153; lean_object* x_3154; uint8_t x_3155; lean_object* x_3156; lean_object* x_3157; 
lean_dec(x_3101);
lean_dec(x_3100);
x_3152 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3099);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3153 = lean_ctor_get(x_3152, 1);
lean_inc(x_3153);
if (lean_is_exclusive(x_3152)) {
 lean_ctor_release(x_3152, 0);
 lean_ctor_release(x_3152, 1);
 x_3154 = x_3152;
} else {
 lean_dec_ref(x_3152);
 x_3154 = lean_box(0);
}
x_3155 = 1;
x_3156 = lean_box(x_3155);
if (lean_is_scalar(x_3154)) {
 x_3157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3157 = x_3154;
}
lean_ctor_set(x_3157, 0, x_3156);
lean_ctor_set(x_3157, 1, x_3153);
return x_3157;
}
}
}
}
else
{
uint8_t x_3158; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3158 = !lean_is_exclusive(x_2950);
if (x_3158 == 0)
{
return x_2950;
}
else
{
lean_object* x_3159; lean_object* x_3160; lean_object* x_3161; 
x_3159 = lean_ctor_get(x_2950, 0);
x_3160 = lean_ctor_get(x_2950, 1);
lean_inc(x_3160);
lean_inc(x_3159);
lean_dec(x_2950);
x_3161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3161, 0, x_3159);
lean_ctor_set(x_3161, 1, x_3160);
return x_3161;
}
}
}
}
else
{
lean_object* x_3162; lean_object* x_3163; uint8_t x_3164; uint8_t x_3165; uint8_t x_3166; 
x_3162 = lean_ctor_get(x_2939, 0);
x_3163 = lean_ctor_get(x_2939, 1);
lean_inc(x_3163);
lean_inc(x_3162);
lean_dec(x_2939);
x_3164 = 2;
x_3165 = lean_unbox(x_3162);
x_3166 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3165, x_3164);
if (x_3166 == 0)
{
uint8_t x_3167; uint8_t x_3168; uint8_t x_3169; lean_object* x_3170; lean_object* x_3171; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3167 = 1;
x_3168 = lean_unbox(x_3162);
lean_dec(x_3162);
x_3169 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3168, x_3167);
x_3170 = lean_box(x_3169);
x_3171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3171, 0, x_3170);
lean_ctor_set(x_3171, 1, x_3163);
return x_3171;
}
else
{
lean_object* x_3172; 
lean_dec(x_3162);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_3172 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_3163);
if (lean_obj_tag(x_3172) == 0)
{
lean_object* x_3173; lean_object* x_3174; lean_object* x_3175; uint8_t x_3176; uint8_t x_3177; 
x_3173 = lean_ctor_get(x_3172, 0);
lean_inc(x_3173);
x_3174 = lean_ctor_get(x_3172, 1);
lean_inc(x_3174);
if (lean_is_exclusive(x_3172)) {
 lean_ctor_release(x_3172, 0);
 lean_ctor_release(x_3172, 1);
 x_3175 = x_3172;
} else {
 lean_dec_ref(x_3172);
 x_3175 = lean_box(0);
}
x_3176 = lean_unbox(x_3173);
x_3177 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3176, x_3164);
if (x_3177 == 0)
{
uint8_t x_3178; uint8_t x_3179; uint8_t x_3180; lean_object* x_3181; lean_object* x_3182; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3178 = 1;
x_3179 = lean_unbox(x_3173);
lean_dec(x_3173);
x_3180 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3179, x_3178);
x_3181 = lean_box(x_3180);
if (lean_is_scalar(x_3175)) {
 x_3182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3182 = x_3175;
}
lean_ctor_set(x_3182, 0, x_3181);
lean_ctor_set(x_3182, 1, x_3174);
return x_3182;
}
else
{
lean_object* x_3183; lean_object* x_3184; lean_object* x_3185; lean_object* x_3186; lean_object* x_3187; lean_object* x_3188; lean_object* x_3189; uint8_t x_3190; 
lean_dec(x_3175);
lean_dec(x_3173);
x_3183 = lean_st_ref_get(x_6, x_3174);
x_3184 = lean_ctor_get(x_3183, 1);
lean_inc(x_3184);
lean_dec(x_3183);
x_3185 = lean_st_ref_get(x_4, x_3184);
x_3186 = lean_ctor_get(x_3185, 0);
lean_inc(x_3186);
x_3187 = lean_ctor_get(x_3185, 1);
lean_inc(x_3187);
if (lean_is_exclusive(x_3185)) {
 lean_ctor_release(x_3185, 0);
 lean_ctor_release(x_3185, 1);
 x_3188 = x_3185;
} else {
 lean_dec_ref(x_3185);
 x_3188 = lean_box(0);
}
x_3189 = lean_ctor_get(x_3186, 0);
lean_inc(x_3189);
lean_dec(x_3186);
lean_inc(x_3189);
x_3190 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3189, x_1);
if (x_3190 == 0)
{
uint8_t x_3191; 
x_3191 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3189, x_2);
if (x_3191 == 0)
{
lean_object* x_3192; lean_object* x_3222; uint8_t x_3223; 
x_3222 = lean_ctor_get(x_3, 0);
lean_inc(x_3222);
x_3223 = lean_ctor_get_uint8(x_3222, 4);
lean_dec(x_3222);
if (x_3223 == 0)
{
uint8_t x_3224; lean_object* x_3225; lean_object* x_3226; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3224 = 0;
x_3225 = lean_box(x_3224);
if (lean_is_scalar(x_3188)) {
 x_3226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3226 = x_3188;
}
lean_ctor_set(x_3226, 0, x_3225);
lean_ctor_set(x_3226, 1, x_3187);
return x_3226;
}
else
{
uint8_t x_3227; 
x_3227 = l_Lean_Level_isMVar(x_1);
if (x_3227 == 0)
{
uint8_t x_3228; 
x_3228 = l_Lean_Level_isMVar(x_2);
if (x_3228 == 0)
{
uint8_t x_3229; lean_object* x_3230; lean_object* x_3231; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3229 = 0;
x_3230 = lean_box(x_3229);
if (lean_is_scalar(x_3188)) {
 x_3231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3231 = x_3188;
}
lean_ctor_set(x_3231, 0, x_3230);
lean_ctor_set(x_3231, 1, x_3187);
return x_3231;
}
else
{
lean_object* x_3232; 
lean_dec(x_3188);
x_3232 = lean_box(0);
x_3192 = x_3232;
goto block_3221;
}
}
else
{
lean_object* x_3233; 
lean_dec(x_3188);
x_3233 = lean_box(0);
x_3192 = x_3233;
goto block_3221;
}
}
block_3221:
{
uint8_t x_3193; lean_object* x_3194; lean_object* x_3209; lean_object* x_3210; lean_object* x_3211; uint8_t x_3212; 
lean_dec(x_3192);
x_3209 = lean_st_ref_get(x_6, x_3187);
x_3210 = lean_ctor_get(x_3209, 0);
lean_inc(x_3210);
x_3211 = lean_ctor_get(x_3210, 3);
lean_inc(x_3211);
lean_dec(x_3210);
x_3212 = lean_ctor_get_uint8(x_3211, sizeof(void*)*1);
lean_dec(x_3211);
if (x_3212 == 0)
{
lean_object* x_3213; uint8_t x_3214; 
x_3213 = lean_ctor_get(x_3209, 1);
lean_inc(x_3213);
lean_dec(x_3209);
x_3214 = 0;
x_3193 = x_3214;
x_3194 = x_3213;
goto block_3208;
}
else
{
lean_object* x_3215; lean_object* x_3216; lean_object* x_3217; lean_object* x_3218; lean_object* x_3219; uint8_t x_3220; 
x_3215 = lean_ctor_get(x_3209, 1);
lean_inc(x_3215);
lean_dec(x_3209);
x_3216 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3217 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_3216, x_3, x_4, x_5, x_6, x_3215);
x_3218 = lean_ctor_get(x_3217, 0);
lean_inc(x_3218);
x_3219 = lean_ctor_get(x_3217, 1);
lean_inc(x_3219);
lean_dec(x_3217);
x_3220 = lean_unbox(x_3218);
lean_dec(x_3218);
x_3193 = x_3220;
x_3194 = x_3219;
goto block_3208;
}
block_3208:
{
if (x_3193 == 0)
{
lean_object* x_3195; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3195 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3194);
return x_3195;
}
else
{
lean_object* x_3196; lean_object* x_3197; lean_object* x_3198; lean_object* x_3199; lean_object* x_3200; lean_object* x_3201; lean_object* x_3202; lean_object* x_3203; lean_object* x_3204; lean_object* x_3205; lean_object* x_3206; lean_object* x_3207; 
x_3196 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3196, 0, x_1);
x_3197 = l_Lean_KernelException_toMessageData___closed__15;
x_3198 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3198, 0, x_3197);
lean_ctor_set(x_3198, 1, x_3196);
x_3199 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_3200 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3200, 0, x_3198);
lean_ctor_set(x_3200, 1, x_3199);
x_3201 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3201, 0, x_2);
x_3202 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3202, 0, x_3200);
lean_ctor_set(x_3202, 1, x_3201);
x_3203 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3203, 0, x_3202);
lean_ctor_set(x_3203, 1, x_3197);
x_3204 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3205 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_3204, x_3203, x_3, x_4, x_5, x_6, x_3194);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3206 = lean_ctor_get(x_3205, 1);
lean_inc(x_3206);
lean_dec(x_3205);
x_3207 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3206);
return x_3207;
}
}
}
}
else
{
lean_object* x_3234; lean_object* x_3235; lean_object* x_3236; uint8_t x_3237; lean_object* x_3238; lean_object* x_3239; 
lean_dec(x_3188);
x_3234 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3187);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3235 = lean_ctor_get(x_3234, 1);
lean_inc(x_3235);
if (lean_is_exclusive(x_3234)) {
 lean_ctor_release(x_3234, 0);
 lean_ctor_release(x_3234, 1);
 x_3236 = x_3234;
} else {
 lean_dec_ref(x_3234);
 x_3236 = lean_box(0);
}
x_3237 = 1;
x_3238 = lean_box(x_3237);
if (lean_is_scalar(x_3236)) {
 x_3239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3239 = x_3236;
}
lean_ctor_set(x_3239, 0, x_3238);
lean_ctor_set(x_3239, 1, x_3235);
return x_3239;
}
}
else
{
lean_object* x_3240; lean_object* x_3241; lean_object* x_3242; uint8_t x_3243; lean_object* x_3244; lean_object* x_3245; 
lean_dec(x_3189);
lean_dec(x_3188);
x_3240 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3187);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3241 = lean_ctor_get(x_3240, 1);
lean_inc(x_3241);
if (lean_is_exclusive(x_3240)) {
 lean_ctor_release(x_3240, 0);
 lean_ctor_release(x_3240, 1);
 x_3242 = x_3240;
} else {
 lean_dec_ref(x_3240);
 x_3242 = lean_box(0);
}
x_3243 = 1;
x_3244 = lean_box(x_3243);
if (lean_is_scalar(x_3242)) {
 x_3245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3245 = x_3242;
}
lean_ctor_set(x_3245, 0, x_3244);
lean_ctor_set(x_3245, 1, x_3241);
return x_3245;
}
}
}
else
{
lean_object* x_3246; lean_object* x_3247; lean_object* x_3248; lean_object* x_3249; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3246 = lean_ctor_get(x_3172, 0);
lean_inc(x_3246);
x_3247 = lean_ctor_get(x_3172, 1);
lean_inc(x_3247);
if (lean_is_exclusive(x_3172)) {
 lean_ctor_release(x_3172, 0);
 lean_ctor_release(x_3172, 1);
 x_3248 = x_3172;
} else {
 lean_dec_ref(x_3172);
 x_3248 = lean_box(0);
}
if (lean_is_scalar(x_3248)) {
 x_3249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3249 = x_3248;
}
lean_ctor_set(x_3249, 0, x_3246);
lean_ctor_set(x_3249, 1, x_3247);
return x_3249;
}
}
}
}
else
{
uint8_t x_3250; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3250 = !lean_is_exclusive(x_2939);
if (x_3250 == 0)
{
return x_2939;
}
else
{
lean_object* x_3251; lean_object* x_3252; lean_object* x_3253; 
x_3251 = lean_ctor_get(x_2939, 0);
x_3252 = lean_ctor_get(x_2939, 1);
lean_inc(x_3252);
lean_inc(x_3251);
lean_dec(x_2939);
x_3253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3253, 0, x_3251);
lean_ctor_set(x_3253, 1, x_3252);
return x_3253;
}
}
}
}
}
block_3268:
{
if (x_3255 == 0)
{
x_2926 = x_3256;
goto block_3254;
}
else
{
lean_object* x_3257; lean_object* x_3258; lean_object* x_3259; lean_object* x_3260; lean_object* x_3261; lean_object* x_3262; lean_object* x_3263; lean_object* x_3264; lean_object* x_3265; lean_object* x_3266; lean_object* x_3267; 
lean_inc(x_1);
x_3257 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3257, 0, x_1);
x_3258 = l_Lean_KernelException_toMessageData___closed__15;
x_3259 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3259, 0, x_3258);
lean_ctor_set(x_3259, 1, x_3257);
x_3260 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_3261 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3261, 0, x_3259);
lean_ctor_set(x_3261, 1, x_3260);
lean_inc(x_2);
x_3262 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3262, 0, x_2);
x_3263 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3263, 0, x_3261);
lean_ctor_set(x_3263, 1, x_3262);
x_3264 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3264, 0, x_3263);
lean_ctor_set(x_3264, 1, x_3258);
x_3265 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_3266 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_3265, x_3264, x_3, x_4, x_5, x_6, x_3256);
x_3267 = lean_ctor_get(x_3266, 1);
lean_inc(x_3267);
lean_dec(x_3266);
x_2926 = x_3267;
goto block_3254;
}
}
}
else
{
lean_object* x_3281; lean_object* x_3282; lean_object* x_3283; uint8_t x_3284; lean_object* x_3285; lean_object* x_3286; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3281 = lean_unsigned_to_nat(0u);
x_3282 = l_Lean_Level_getOffsetAux(x_1, x_3281);
lean_dec(x_1);
x_3283 = l_Lean_Level_getOffsetAux(x_2, x_3281);
lean_dec(x_2);
x_3284 = lean_nat_dec_eq(x_3282, x_3283);
lean_dec(x_3283);
lean_dec(x_3282);
x_3285 = lean_box(x_3284);
x_3286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3286, 0, x_3285);
lean_ctor_set(x_3286, 1, x_7);
return x_3286;
}
}
default: 
{
lean_object* x_3287; lean_object* x_3288; uint8_t x_3289; 
x_3287 = l_Lean_Level_getLevelOffset(x_1);
x_3288 = l_Lean_Level_getLevelOffset(x_2);
x_3289 = lean_level_eq(x_3287, x_3288);
lean_dec(x_3288);
lean_dec(x_3287);
if (x_3289 == 0)
{
lean_object* x_3290; uint8_t x_3619; lean_object* x_3620; lean_object* x_3633; lean_object* x_3634; lean_object* x_3635; uint8_t x_3636; 
x_3633 = lean_st_ref_get(x_6, x_7);
x_3634 = lean_ctor_get(x_3633, 0);
lean_inc(x_3634);
x_3635 = lean_ctor_get(x_3634, 3);
lean_inc(x_3635);
lean_dec(x_3634);
x_3636 = lean_ctor_get_uint8(x_3635, sizeof(void*)*1);
lean_dec(x_3635);
if (x_3636 == 0)
{
lean_object* x_3637; uint8_t x_3638; 
x_3637 = lean_ctor_get(x_3633, 1);
lean_inc(x_3637);
lean_dec(x_3633);
x_3638 = 0;
x_3619 = x_3638;
x_3620 = x_3637;
goto block_3632;
}
else
{
lean_object* x_3639; lean_object* x_3640; lean_object* x_3641; lean_object* x_3642; lean_object* x_3643; uint8_t x_3644; 
x_3639 = lean_ctor_get(x_3633, 1);
lean_inc(x_3639);
lean_dec(x_3633);
x_3640 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_3641 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_3640, x_3, x_4, x_5, x_6, x_3639);
x_3642 = lean_ctor_get(x_3641, 0);
lean_inc(x_3642);
x_3643 = lean_ctor_get(x_3641, 1);
lean_inc(x_3643);
lean_dec(x_3641);
x_3644 = lean_unbox(x_3642);
lean_dec(x_3642);
x_3619 = x_3644;
x_3620 = x_3643;
goto block_3632;
}
block_3618:
{
lean_object* x_3291; lean_object* x_3292; lean_object* x_3293; lean_object* x_3294; lean_object* x_3295; lean_object* x_3296; lean_object* x_3297; lean_object* x_3298; uint8_t x_3299; 
lean_inc(x_1);
x_3291 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_3290);
x_3292 = lean_ctor_get(x_3291, 0);
lean_inc(x_3292);
x_3293 = lean_ctor_get(x_3291, 1);
lean_inc(x_3293);
lean_dec(x_3291);
x_3294 = l_Lean_Level_normalize(x_3292);
lean_dec(x_3292);
lean_inc(x_2);
x_3295 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_2, x_3, x_4, x_5, x_6, x_3293);
x_3296 = lean_ctor_get(x_3295, 0);
lean_inc(x_3296);
x_3297 = lean_ctor_get(x_3295, 1);
lean_inc(x_3297);
lean_dec(x_3295);
x_3298 = l_Lean_Level_normalize(x_3296);
lean_dec(x_3296);
x_3299 = lean_level_eq(x_1, x_3294);
if (x_3299 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_3294;
x_2 = x_3298;
x_7 = x_3297;
goto _start;
}
else
{
uint8_t x_3301; 
x_3301 = lean_level_eq(x_2, x_3298);
if (x_3301 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_3294;
x_2 = x_3298;
x_7 = x_3297;
goto _start;
}
else
{
lean_object* x_3303; 
lean_dec(x_3298);
lean_dec(x_3294);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_3303 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_3297);
if (lean_obj_tag(x_3303) == 0)
{
uint8_t x_3304; 
x_3304 = !lean_is_exclusive(x_3303);
if (x_3304 == 0)
{
lean_object* x_3305; lean_object* x_3306; uint8_t x_3307; uint8_t x_3308; uint8_t x_3309; 
x_3305 = lean_ctor_get(x_3303, 0);
x_3306 = lean_ctor_get(x_3303, 1);
x_3307 = 2;
x_3308 = lean_unbox(x_3305);
x_3309 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3308, x_3307);
if (x_3309 == 0)
{
uint8_t x_3310; uint8_t x_3311; uint8_t x_3312; lean_object* x_3313; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3310 = 1;
x_3311 = lean_unbox(x_3305);
lean_dec(x_3305);
x_3312 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3311, x_3310);
x_3313 = lean_box(x_3312);
lean_ctor_set(x_3303, 0, x_3313);
return x_3303;
}
else
{
lean_object* x_3314; 
lean_free_object(x_3303);
lean_dec(x_3305);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_3314 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_3306);
if (lean_obj_tag(x_3314) == 0)
{
uint8_t x_3315; 
x_3315 = !lean_is_exclusive(x_3314);
if (x_3315 == 0)
{
lean_object* x_3316; lean_object* x_3317; uint8_t x_3318; uint8_t x_3319; 
x_3316 = lean_ctor_get(x_3314, 0);
x_3317 = lean_ctor_get(x_3314, 1);
x_3318 = lean_unbox(x_3316);
x_3319 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3318, x_3307);
if (x_3319 == 0)
{
uint8_t x_3320; uint8_t x_3321; uint8_t x_3322; lean_object* x_3323; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3320 = 1;
x_3321 = lean_unbox(x_3316);
lean_dec(x_3316);
x_3322 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3321, x_3320);
x_3323 = lean_box(x_3322);
lean_ctor_set(x_3314, 0, x_3323);
return x_3314;
}
else
{
lean_object* x_3324; lean_object* x_3325; lean_object* x_3326; uint8_t x_3327; 
lean_free_object(x_3314);
lean_dec(x_3316);
x_3324 = lean_st_ref_get(x_6, x_3317);
x_3325 = lean_ctor_get(x_3324, 1);
lean_inc(x_3325);
lean_dec(x_3324);
x_3326 = lean_st_ref_get(x_4, x_3325);
x_3327 = !lean_is_exclusive(x_3326);
if (x_3327 == 0)
{
lean_object* x_3328; lean_object* x_3329; lean_object* x_3330; uint8_t x_3331; 
x_3328 = lean_ctor_get(x_3326, 0);
x_3329 = lean_ctor_get(x_3326, 1);
x_3330 = lean_ctor_get(x_3328, 0);
lean_inc(x_3330);
lean_dec(x_3328);
lean_inc(x_3330);
x_3331 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3330, x_1);
if (x_3331 == 0)
{
uint8_t x_3332; 
x_3332 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3330, x_2);
if (x_3332 == 0)
{
lean_object* x_3333; lean_object* x_3363; uint8_t x_3364; 
x_3363 = lean_ctor_get(x_3, 0);
lean_inc(x_3363);
x_3364 = lean_ctor_get_uint8(x_3363, 4);
lean_dec(x_3363);
if (x_3364 == 0)
{
uint8_t x_3365; lean_object* x_3366; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3365 = 0;
x_3366 = lean_box(x_3365);
lean_ctor_set(x_3326, 0, x_3366);
return x_3326;
}
else
{
uint8_t x_3367; 
x_3367 = l_Lean_Level_isMVar(x_1);
if (x_3367 == 0)
{
uint8_t x_3368; 
x_3368 = l_Lean_Level_isMVar(x_2);
if (x_3368 == 0)
{
uint8_t x_3369; lean_object* x_3370; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3369 = 0;
x_3370 = lean_box(x_3369);
lean_ctor_set(x_3326, 0, x_3370);
return x_3326;
}
else
{
lean_object* x_3371; 
lean_free_object(x_3326);
x_3371 = lean_box(0);
x_3333 = x_3371;
goto block_3362;
}
}
else
{
lean_object* x_3372; 
lean_free_object(x_3326);
x_3372 = lean_box(0);
x_3333 = x_3372;
goto block_3362;
}
}
block_3362:
{
uint8_t x_3334; lean_object* x_3335; lean_object* x_3350; lean_object* x_3351; lean_object* x_3352; uint8_t x_3353; 
lean_dec(x_3333);
x_3350 = lean_st_ref_get(x_6, x_3329);
x_3351 = lean_ctor_get(x_3350, 0);
lean_inc(x_3351);
x_3352 = lean_ctor_get(x_3351, 3);
lean_inc(x_3352);
lean_dec(x_3351);
x_3353 = lean_ctor_get_uint8(x_3352, sizeof(void*)*1);
lean_dec(x_3352);
if (x_3353 == 0)
{
lean_object* x_3354; uint8_t x_3355; 
x_3354 = lean_ctor_get(x_3350, 1);
lean_inc(x_3354);
lean_dec(x_3350);
x_3355 = 0;
x_3334 = x_3355;
x_3335 = x_3354;
goto block_3349;
}
else
{
lean_object* x_3356; lean_object* x_3357; lean_object* x_3358; lean_object* x_3359; lean_object* x_3360; uint8_t x_3361; 
x_3356 = lean_ctor_get(x_3350, 1);
lean_inc(x_3356);
lean_dec(x_3350);
x_3357 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3358 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_3357, x_3, x_4, x_5, x_6, x_3356);
x_3359 = lean_ctor_get(x_3358, 0);
lean_inc(x_3359);
x_3360 = lean_ctor_get(x_3358, 1);
lean_inc(x_3360);
lean_dec(x_3358);
x_3361 = lean_unbox(x_3359);
lean_dec(x_3359);
x_3334 = x_3361;
x_3335 = x_3360;
goto block_3349;
}
block_3349:
{
if (x_3334 == 0)
{
lean_object* x_3336; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3336 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3335);
return x_3336;
}
else
{
lean_object* x_3337; lean_object* x_3338; lean_object* x_3339; lean_object* x_3340; lean_object* x_3341; lean_object* x_3342; lean_object* x_3343; lean_object* x_3344; lean_object* x_3345; lean_object* x_3346; lean_object* x_3347; lean_object* x_3348; 
x_3337 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3337, 0, x_1);
x_3338 = l_Lean_KernelException_toMessageData___closed__15;
x_3339 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3339, 0, x_3338);
lean_ctor_set(x_3339, 1, x_3337);
x_3340 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_3341 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3341, 0, x_3339);
lean_ctor_set(x_3341, 1, x_3340);
x_3342 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3342, 0, x_2);
x_3343 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3343, 0, x_3341);
lean_ctor_set(x_3343, 1, x_3342);
x_3344 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3344, 0, x_3343);
lean_ctor_set(x_3344, 1, x_3338);
x_3345 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3346 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_3345, x_3344, x_3, x_4, x_5, x_6, x_3335);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3347 = lean_ctor_get(x_3346, 1);
lean_inc(x_3347);
lean_dec(x_3346);
x_3348 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3347);
return x_3348;
}
}
}
}
else
{
lean_object* x_3373; uint8_t x_3374; 
lean_free_object(x_3326);
x_3373 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3329);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3374 = !lean_is_exclusive(x_3373);
if (x_3374 == 0)
{
lean_object* x_3375; uint8_t x_3376; lean_object* x_3377; 
x_3375 = lean_ctor_get(x_3373, 0);
lean_dec(x_3375);
x_3376 = 1;
x_3377 = lean_box(x_3376);
lean_ctor_set(x_3373, 0, x_3377);
return x_3373;
}
else
{
lean_object* x_3378; uint8_t x_3379; lean_object* x_3380; lean_object* x_3381; 
x_3378 = lean_ctor_get(x_3373, 1);
lean_inc(x_3378);
lean_dec(x_3373);
x_3379 = 1;
x_3380 = lean_box(x_3379);
x_3381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3381, 0, x_3380);
lean_ctor_set(x_3381, 1, x_3378);
return x_3381;
}
}
}
else
{
lean_object* x_3382; uint8_t x_3383; 
lean_dec(x_3330);
lean_free_object(x_3326);
x_3382 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3329);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3383 = !lean_is_exclusive(x_3382);
if (x_3383 == 0)
{
lean_object* x_3384; uint8_t x_3385; lean_object* x_3386; 
x_3384 = lean_ctor_get(x_3382, 0);
lean_dec(x_3384);
x_3385 = 1;
x_3386 = lean_box(x_3385);
lean_ctor_set(x_3382, 0, x_3386);
return x_3382;
}
else
{
lean_object* x_3387; uint8_t x_3388; lean_object* x_3389; lean_object* x_3390; 
x_3387 = lean_ctor_get(x_3382, 1);
lean_inc(x_3387);
lean_dec(x_3382);
x_3388 = 1;
x_3389 = lean_box(x_3388);
x_3390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3390, 0, x_3389);
lean_ctor_set(x_3390, 1, x_3387);
return x_3390;
}
}
}
else
{
lean_object* x_3391; lean_object* x_3392; lean_object* x_3393; uint8_t x_3394; 
x_3391 = lean_ctor_get(x_3326, 0);
x_3392 = lean_ctor_get(x_3326, 1);
lean_inc(x_3392);
lean_inc(x_3391);
lean_dec(x_3326);
x_3393 = lean_ctor_get(x_3391, 0);
lean_inc(x_3393);
lean_dec(x_3391);
lean_inc(x_3393);
x_3394 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3393, x_1);
if (x_3394 == 0)
{
uint8_t x_3395; 
x_3395 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3393, x_2);
if (x_3395 == 0)
{
lean_object* x_3396; lean_object* x_3426; uint8_t x_3427; 
x_3426 = lean_ctor_get(x_3, 0);
lean_inc(x_3426);
x_3427 = lean_ctor_get_uint8(x_3426, 4);
lean_dec(x_3426);
if (x_3427 == 0)
{
uint8_t x_3428; lean_object* x_3429; lean_object* x_3430; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3428 = 0;
x_3429 = lean_box(x_3428);
x_3430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3430, 0, x_3429);
lean_ctor_set(x_3430, 1, x_3392);
return x_3430;
}
else
{
uint8_t x_3431; 
x_3431 = l_Lean_Level_isMVar(x_1);
if (x_3431 == 0)
{
uint8_t x_3432; 
x_3432 = l_Lean_Level_isMVar(x_2);
if (x_3432 == 0)
{
uint8_t x_3433; lean_object* x_3434; lean_object* x_3435; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3433 = 0;
x_3434 = lean_box(x_3433);
x_3435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3435, 0, x_3434);
lean_ctor_set(x_3435, 1, x_3392);
return x_3435;
}
else
{
lean_object* x_3436; 
x_3436 = lean_box(0);
x_3396 = x_3436;
goto block_3425;
}
}
else
{
lean_object* x_3437; 
x_3437 = lean_box(0);
x_3396 = x_3437;
goto block_3425;
}
}
block_3425:
{
uint8_t x_3397; lean_object* x_3398; lean_object* x_3413; lean_object* x_3414; lean_object* x_3415; uint8_t x_3416; 
lean_dec(x_3396);
x_3413 = lean_st_ref_get(x_6, x_3392);
x_3414 = lean_ctor_get(x_3413, 0);
lean_inc(x_3414);
x_3415 = lean_ctor_get(x_3414, 3);
lean_inc(x_3415);
lean_dec(x_3414);
x_3416 = lean_ctor_get_uint8(x_3415, sizeof(void*)*1);
lean_dec(x_3415);
if (x_3416 == 0)
{
lean_object* x_3417; uint8_t x_3418; 
x_3417 = lean_ctor_get(x_3413, 1);
lean_inc(x_3417);
lean_dec(x_3413);
x_3418 = 0;
x_3397 = x_3418;
x_3398 = x_3417;
goto block_3412;
}
else
{
lean_object* x_3419; lean_object* x_3420; lean_object* x_3421; lean_object* x_3422; lean_object* x_3423; uint8_t x_3424; 
x_3419 = lean_ctor_get(x_3413, 1);
lean_inc(x_3419);
lean_dec(x_3413);
x_3420 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3421 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_3420, x_3, x_4, x_5, x_6, x_3419);
x_3422 = lean_ctor_get(x_3421, 0);
lean_inc(x_3422);
x_3423 = lean_ctor_get(x_3421, 1);
lean_inc(x_3423);
lean_dec(x_3421);
x_3424 = lean_unbox(x_3422);
lean_dec(x_3422);
x_3397 = x_3424;
x_3398 = x_3423;
goto block_3412;
}
block_3412:
{
if (x_3397 == 0)
{
lean_object* x_3399; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3399 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3398);
return x_3399;
}
else
{
lean_object* x_3400; lean_object* x_3401; lean_object* x_3402; lean_object* x_3403; lean_object* x_3404; lean_object* x_3405; lean_object* x_3406; lean_object* x_3407; lean_object* x_3408; lean_object* x_3409; lean_object* x_3410; lean_object* x_3411; 
x_3400 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3400, 0, x_1);
x_3401 = l_Lean_KernelException_toMessageData___closed__15;
x_3402 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3402, 0, x_3401);
lean_ctor_set(x_3402, 1, x_3400);
x_3403 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_3404 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3404, 0, x_3402);
lean_ctor_set(x_3404, 1, x_3403);
x_3405 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3405, 0, x_2);
x_3406 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3406, 0, x_3404);
lean_ctor_set(x_3406, 1, x_3405);
x_3407 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3407, 0, x_3406);
lean_ctor_set(x_3407, 1, x_3401);
x_3408 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3409 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_3408, x_3407, x_3, x_4, x_5, x_6, x_3398);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3410 = lean_ctor_get(x_3409, 1);
lean_inc(x_3410);
lean_dec(x_3409);
x_3411 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3410);
return x_3411;
}
}
}
}
else
{
lean_object* x_3438; lean_object* x_3439; lean_object* x_3440; uint8_t x_3441; lean_object* x_3442; lean_object* x_3443; 
x_3438 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3392);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3439 = lean_ctor_get(x_3438, 1);
lean_inc(x_3439);
if (lean_is_exclusive(x_3438)) {
 lean_ctor_release(x_3438, 0);
 lean_ctor_release(x_3438, 1);
 x_3440 = x_3438;
} else {
 lean_dec_ref(x_3438);
 x_3440 = lean_box(0);
}
x_3441 = 1;
x_3442 = lean_box(x_3441);
if (lean_is_scalar(x_3440)) {
 x_3443 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3443 = x_3440;
}
lean_ctor_set(x_3443, 0, x_3442);
lean_ctor_set(x_3443, 1, x_3439);
return x_3443;
}
}
else
{
lean_object* x_3444; lean_object* x_3445; lean_object* x_3446; uint8_t x_3447; lean_object* x_3448; lean_object* x_3449; 
lean_dec(x_3393);
x_3444 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3392);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3445 = lean_ctor_get(x_3444, 1);
lean_inc(x_3445);
if (lean_is_exclusive(x_3444)) {
 lean_ctor_release(x_3444, 0);
 lean_ctor_release(x_3444, 1);
 x_3446 = x_3444;
} else {
 lean_dec_ref(x_3444);
 x_3446 = lean_box(0);
}
x_3447 = 1;
x_3448 = lean_box(x_3447);
if (lean_is_scalar(x_3446)) {
 x_3449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3449 = x_3446;
}
lean_ctor_set(x_3449, 0, x_3448);
lean_ctor_set(x_3449, 1, x_3445);
return x_3449;
}
}
}
}
else
{
lean_object* x_3450; lean_object* x_3451; uint8_t x_3452; uint8_t x_3453; 
x_3450 = lean_ctor_get(x_3314, 0);
x_3451 = lean_ctor_get(x_3314, 1);
lean_inc(x_3451);
lean_inc(x_3450);
lean_dec(x_3314);
x_3452 = lean_unbox(x_3450);
x_3453 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3452, x_3307);
if (x_3453 == 0)
{
uint8_t x_3454; uint8_t x_3455; uint8_t x_3456; lean_object* x_3457; lean_object* x_3458; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3454 = 1;
x_3455 = lean_unbox(x_3450);
lean_dec(x_3450);
x_3456 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3455, x_3454);
x_3457 = lean_box(x_3456);
x_3458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3458, 0, x_3457);
lean_ctor_set(x_3458, 1, x_3451);
return x_3458;
}
else
{
lean_object* x_3459; lean_object* x_3460; lean_object* x_3461; lean_object* x_3462; lean_object* x_3463; lean_object* x_3464; lean_object* x_3465; uint8_t x_3466; 
lean_dec(x_3450);
x_3459 = lean_st_ref_get(x_6, x_3451);
x_3460 = lean_ctor_get(x_3459, 1);
lean_inc(x_3460);
lean_dec(x_3459);
x_3461 = lean_st_ref_get(x_4, x_3460);
x_3462 = lean_ctor_get(x_3461, 0);
lean_inc(x_3462);
x_3463 = lean_ctor_get(x_3461, 1);
lean_inc(x_3463);
if (lean_is_exclusive(x_3461)) {
 lean_ctor_release(x_3461, 0);
 lean_ctor_release(x_3461, 1);
 x_3464 = x_3461;
} else {
 lean_dec_ref(x_3461);
 x_3464 = lean_box(0);
}
x_3465 = lean_ctor_get(x_3462, 0);
lean_inc(x_3465);
lean_dec(x_3462);
lean_inc(x_3465);
x_3466 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3465, x_1);
if (x_3466 == 0)
{
uint8_t x_3467; 
x_3467 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3465, x_2);
if (x_3467 == 0)
{
lean_object* x_3468; lean_object* x_3498; uint8_t x_3499; 
x_3498 = lean_ctor_get(x_3, 0);
lean_inc(x_3498);
x_3499 = lean_ctor_get_uint8(x_3498, 4);
lean_dec(x_3498);
if (x_3499 == 0)
{
uint8_t x_3500; lean_object* x_3501; lean_object* x_3502; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3500 = 0;
x_3501 = lean_box(x_3500);
if (lean_is_scalar(x_3464)) {
 x_3502 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3502 = x_3464;
}
lean_ctor_set(x_3502, 0, x_3501);
lean_ctor_set(x_3502, 1, x_3463);
return x_3502;
}
else
{
uint8_t x_3503; 
x_3503 = l_Lean_Level_isMVar(x_1);
if (x_3503 == 0)
{
uint8_t x_3504; 
x_3504 = l_Lean_Level_isMVar(x_2);
if (x_3504 == 0)
{
uint8_t x_3505; lean_object* x_3506; lean_object* x_3507; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3505 = 0;
x_3506 = lean_box(x_3505);
if (lean_is_scalar(x_3464)) {
 x_3507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3507 = x_3464;
}
lean_ctor_set(x_3507, 0, x_3506);
lean_ctor_set(x_3507, 1, x_3463);
return x_3507;
}
else
{
lean_object* x_3508; 
lean_dec(x_3464);
x_3508 = lean_box(0);
x_3468 = x_3508;
goto block_3497;
}
}
else
{
lean_object* x_3509; 
lean_dec(x_3464);
x_3509 = lean_box(0);
x_3468 = x_3509;
goto block_3497;
}
}
block_3497:
{
uint8_t x_3469; lean_object* x_3470; lean_object* x_3485; lean_object* x_3486; lean_object* x_3487; uint8_t x_3488; 
lean_dec(x_3468);
x_3485 = lean_st_ref_get(x_6, x_3463);
x_3486 = lean_ctor_get(x_3485, 0);
lean_inc(x_3486);
x_3487 = lean_ctor_get(x_3486, 3);
lean_inc(x_3487);
lean_dec(x_3486);
x_3488 = lean_ctor_get_uint8(x_3487, sizeof(void*)*1);
lean_dec(x_3487);
if (x_3488 == 0)
{
lean_object* x_3489; uint8_t x_3490; 
x_3489 = lean_ctor_get(x_3485, 1);
lean_inc(x_3489);
lean_dec(x_3485);
x_3490 = 0;
x_3469 = x_3490;
x_3470 = x_3489;
goto block_3484;
}
else
{
lean_object* x_3491; lean_object* x_3492; lean_object* x_3493; lean_object* x_3494; lean_object* x_3495; uint8_t x_3496; 
x_3491 = lean_ctor_get(x_3485, 1);
lean_inc(x_3491);
lean_dec(x_3485);
x_3492 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3493 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_3492, x_3, x_4, x_5, x_6, x_3491);
x_3494 = lean_ctor_get(x_3493, 0);
lean_inc(x_3494);
x_3495 = lean_ctor_get(x_3493, 1);
lean_inc(x_3495);
lean_dec(x_3493);
x_3496 = lean_unbox(x_3494);
lean_dec(x_3494);
x_3469 = x_3496;
x_3470 = x_3495;
goto block_3484;
}
block_3484:
{
if (x_3469 == 0)
{
lean_object* x_3471; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3471 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3470);
return x_3471;
}
else
{
lean_object* x_3472; lean_object* x_3473; lean_object* x_3474; lean_object* x_3475; lean_object* x_3476; lean_object* x_3477; lean_object* x_3478; lean_object* x_3479; lean_object* x_3480; lean_object* x_3481; lean_object* x_3482; lean_object* x_3483; 
x_3472 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3472, 0, x_1);
x_3473 = l_Lean_KernelException_toMessageData___closed__15;
x_3474 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3474, 0, x_3473);
lean_ctor_set(x_3474, 1, x_3472);
x_3475 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_3476 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3476, 0, x_3474);
lean_ctor_set(x_3476, 1, x_3475);
x_3477 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3477, 0, x_2);
x_3478 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3478, 0, x_3476);
lean_ctor_set(x_3478, 1, x_3477);
x_3479 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3479, 0, x_3478);
lean_ctor_set(x_3479, 1, x_3473);
x_3480 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3481 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_3480, x_3479, x_3, x_4, x_5, x_6, x_3470);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3482 = lean_ctor_get(x_3481, 1);
lean_inc(x_3482);
lean_dec(x_3481);
x_3483 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3482);
return x_3483;
}
}
}
}
else
{
lean_object* x_3510; lean_object* x_3511; lean_object* x_3512; uint8_t x_3513; lean_object* x_3514; lean_object* x_3515; 
lean_dec(x_3464);
x_3510 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3463);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3511 = lean_ctor_get(x_3510, 1);
lean_inc(x_3511);
if (lean_is_exclusive(x_3510)) {
 lean_ctor_release(x_3510, 0);
 lean_ctor_release(x_3510, 1);
 x_3512 = x_3510;
} else {
 lean_dec_ref(x_3510);
 x_3512 = lean_box(0);
}
x_3513 = 1;
x_3514 = lean_box(x_3513);
if (lean_is_scalar(x_3512)) {
 x_3515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3515 = x_3512;
}
lean_ctor_set(x_3515, 0, x_3514);
lean_ctor_set(x_3515, 1, x_3511);
return x_3515;
}
}
else
{
lean_object* x_3516; lean_object* x_3517; lean_object* x_3518; uint8_t x_3519; lean_object* x_3520; lean_object* x_3521; 
lean_dec(x_3465);
lean_dec(x_3464);
x_3516 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3463);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3517 = lean_ctor_get(x_3516, 1);
lean_inc(x_3517);
if (lean_is_exclusive(x_3516)) {
 lean_ctor_release(x_3516, 0);
 lean_ctor_release(x_3516, 1);
 x_3518 = x_3516;
} else {
 lean_dec_ref(x_3516);
 x_3518 = lean_box(0);
}
x_3519 = 1;
x_3520 = lean_box(x_3519);
if (lean_is_scalar(x_3518)) {
 x_3521 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3521 = x_3518;
}
lean_ctor_set(x_3521, 0, x_3520);
lean_ctor_set(x_3521, 1, x_3517);
return x_3521;
}
}
}
}
else
{
uint8_t x_3522; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3522 = !lean_is_exclusive(x_3314);
if (x_3522 == 0)
{
return x_3314;
}
else
{
lean_object* x_3523; lean_object* x_3524; lean_object* x_3525; 
x_3523 = lean_ctor_get(x_3314, 0);
x_3524 = lean_ctor_get(x_3314, 1);
lean_inc(x_3524);
lean_inc(x_3523);
lean_dec(x_3314);
x_3525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3525, 0, x_3523);
lean_ctor_set(x_3525, 1, x_3524);
return x_3525;
}
}
}
}
else
{
lean_object* x_3526; lean_object* x_3527; uint8_t x_3528; uint8_t x_3529; uint8_t x_3530; 
x_3526 = lean_ctor_get(x_3303, 0);
x_3527 = lean_ctor_get(x_3303, 1);
lean_inc(x_3527);
lean_inc(x_3526);
lean_dec(x_3303);
x_3528 = 2;
x_3529 = lean_unbox(x_3526);
x_3530 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3529, x_3528);
if (x_3530 == 0)
{
uint8_t x_3531; uint8_t x_3532; uint8_t x_3533; lean_object* x_3534; lean_object* x_3535; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3531 = 1;
x_3532 = lean_unbox(x_3526);
lean_dec(x_3526);
x_3533 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3532, x_3531);
x_3534 = lean_box(x_3533);
x_3535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3535, 0, x_3534);
lean_ctor_set(x_3535, 1, x_3527);
return x_3535;
}
else
{
lean_object* x_3536; 
lean_dec(x_3526);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_3536 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_3, x_4, x_5, x_6, x_3527);
if (lean_obj_tag(x_3536) == 0)
{
lean_object* x_3537; lean_object* x_3538; lean_object* x_3539; uint8_t x_3540; uint8_t x_3541; 
x_3537 = lean_ctor_get(x_3536, 0);
lean_inc(x_3537);
x_3538 = lean_ctor_get(x_3536, 1);
lean_inc(x_3538);
if (lean_is_exclusive(x_3536)) {
 lean_ctor_release(x_3536, 0);
 lean_ctor_release(x_3536, 1);
 x_3539 = x_3536;
} else {
 lean_dec_ref(x_3536);
 x_3539 = lean_box(0);
}
x_3540 = lean_unbox(x_3537);
x_3541 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3540, x_3528);
if (x_3541 == 0)
{
uint8_t x_3542; uint8_t x_3543; uint8_t x_3544; lean_object* x_3545; lean_object* x_3546; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3542 = 1;
x_3543 = lean_unbox(x_3537);
lean_dec(x_3537);
x_3544 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3543, x_3542);
x_3545 = lean_box(x_3544);
if (lean_is_scalar(x_3539)) {
 x_3546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3546 = x_3539;
}
lean_ctor_set(x_3546, 0, x_3545);
lean_ctor_set(x_3546, 1, x_3538);
return x_3546;
}
else
{
lean_object* x_3547; lean_object* x_3548; lean_object* x_3549; lean_object* x_3550; lean_object* x_3551; lean_object* x_3552; lean_object* x_3553; uint8_t x_3554; 
lean_dec(x_3539);
lean_dec(x_3537);
x_3547 = lean_st_ref_get(x_6, x_3538);
x_3548 = lean_ctor_get(x_3547, 1);
lean_inc(x_3548);
lean_dec(x_3547);
x_3549 = lean_st_ref_get(x_4, x_3548);
x_3550 = lean_ctor_get(x_3549, 0);
lean_inc(x_3550);
x_3551 = lean_ctor_get(x_3549, 1);
lean_inc(x_3551);
if (lean_is_exclusive(x_3549)) {
 lean_ctor_release(x_3549, 0);
 lean_ctor_release(x_3549, 1);
 x_3552 = x_3549;
} else {
 lean_dec_ref(x_3549);
 x_3552 = lean_box(0);
}
x_3553 = lean_ctor_get(x_3550, 0);
lean_inc(x_3553);
lean_dec(x_3550);
lean_inc(x_3553);
x_3554 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3553, x_1);
if (x_3554 == 0)
{
uint8_t x_3555; 
x_3555 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_3553, x_2);
if (x_3555 == 0)
{
lean_object* x_3556; lean_object* x_3586; uint8_t x_3587; 
x_3586 = lean_ctor_get(x_3, 0);
lean_inc(x_3586);
x_3587 = lean_ctor_get_uint8(x_3586, 4);
lean_dec(x_3586);
if (x_3587 == 0)
{
uint8_t x_3588; lean_object* x_3589; lean_object* x_3590; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3588 = 0;
x_3589 = lean_box(x_3588);
if (lean_is_scalar(x_3552)) {
 x_3590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3590 = x_3552;
}
lean_ctor_set(x_3590, 0, x_3589);
lean_ctor_set(x_3590, 1, x_3551);
return x_3590;
}
else
{
uint8_t x_3591; 
x_3591 = l_Lean_Level_isMVar(x_1);
if (x_3591 == 0)
{
uint8_t x_3592; 
x_3592 = l_Lean_Level_isMVar(x_2);
if (x_3592 == 0)
{
uint8_t x_3593; lean_object* x_3594; lean_object* x_3595; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3593 = 0;
x_3594 = lean_box(x_3593);
if (lean_is_scalar(x_3552)) {
 x_3595 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3595 = x_3552;
}
lean_ctor_set(x_3595, 0, x_3594);
lean_ctor_set(x_3595, 1, x_3551);
return x_3595;
}
else
{
lean_object* x_3596; 
lean_dec(x_3552);
x_3596 = lean_box(0);
x_3556 = x_3596;
goto block_3585;
}
}
else
{
lean_object* x_3597; 
lean_dec(x_3552);
x_3597 = lean_box(0);
x_3556 = x_3597;
goto block_3585;
}
}
block_3585:
{
uint8_t x_3557; lean_object* x_3558; lean_object* x_3573; lean_object* x_3574; lean_object* x_3575; uint8_t x_3576; 
lean_dec(x_3556);
x_3573 = lean_st_ref_get(x_6, x_3551);
x_3574 = lean_ctor_get(x_3573, 0);
lean_inc(x_3574);
x_3575 = lean_ctor_get(x_3574, 3);
lean_inc(x_3575);
lean_dec(x_3574);
x_3576 = lean_ctor_get_uint8(x_3575, sizeof(void*)*1);
lean_dec(x_3575);
if (x_3576 == 0)
{
lean_object* x_3577; uint8_t x_3578; 
x_3577 = lean_ctor_get(x_3573, 1);
lean_inc(x_3577);
lean_dec(x_3573);
x_3578 = 0;
x_3557 = x_3578;
x_3558 = x_3577;
goto block_3572;
}
else
{
lean_object* x_3579; lean_object* x_3580; lean_object* x_3581; lean_object* x_3582; lean_object* x_3583; uint8_t x_3584; 
x_3579 = lean_ctor_get(x_3573, 1);
lean_inc(x_3579);
lean_dec(x_3573);
x_3580 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3581 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_3580, x_3, x_4, x_5, x_6, x_3579);
x_3582 = lean_ctor_get(x_3581, 0);
lean_inc(x_3582);
x_3583 = lean_ctor_get(x_3581, 1);
lean_inc(x_3583);
lean_dec(x_3581);
x_3584 = lean_unbox(x_3582);
lean_dec(x_3582);
x_3557 = x_3584;
x_3558 = x_3583;
goto block_3572;
}
block_3572:
{
if (x_3557 == 0)
{
lean_object* x_3559; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3559 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3558);
return x_3559;
}
else
{
lean_object* x_3560; lean_object* x_3561; lean_object* x_3562; lean_object* x_3563; lean_object* x_3564; lean_object* x_3565; lean_object* x_3566; lean_object* x_3567; lean_object* x_3568; lean_object* x_3569; lean_object* x_3570; lean_object* x_3571; 
x_3560 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3560, 0, x_1);
x_3561 = l_Lean_KernelException_toMessageData___closed__15;
x_3562 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3562, 0, x_3561);
lean_ctor_set(x_3562, 1, x_3560);
x_3563 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_3564 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3564, 0, x_3562);
lean_ctor_set(x_3564, 1, x_3563);
x_3565 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3565, 0, x_2);
x_3566 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3566, 0, x_3564);
lean_ctor_set(x_3566, 1, x_3565);
x_3567 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3567, 0, x_3566);
lean_ctor_set(x_3567, 1, x_3561);
x_3568 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3569 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_3568, x_3567, x_3, x_4, x_5, x_6, x_3558);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3570 = lean_ctor_get(x_3569, 1);
lean_inc(x_3570);
lean_dec(x_3569);
x_3571 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_3570);
return x_3571;
}
}
}
}
else
{
lean_object* x_3598; lean_object* x_3599; lean_object* x_3600; uint8_t x_3601; lean_object* x_3602; lean_object* x_3603; 
lean_dec(x_3552);
x_3598 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3551);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3599 = lean_ctor_get(x_3598, 1);
lean_inc(x_3599);
if (lean_is_exclusive(x_3598)) {
 lean_ctor_release(x_3598, 0);
 lean_ctor_release(x_3598, 1);
 x_3600 = x_3598;
} else {
 lean_dec_ref(x_3598);
 x_3600 = lean_box(0);
}
x_3601 = 1;
x_3602 = lean_box(x_3601);
if (lean_is_scalar(x_3600)) {
 x_3603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3603 = x_3600;
}
lean_ctor_set(x_3603, 0, x_3602);
lean_ctor_set(x_3603, 1, x_3599);
return x_3603;
}
}
else
{
lean_object* x_3604; lean_object* x_3605; lean_object* x_3606; uint8_t x_3607; lean_object* x_3608; lean_object* x_3609; 
lean_dec(x_3553);
lean_dec(x_3552);
x_3604 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_3551);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3605 = lean_ctor_get(x_3604, 1);
lean_inc(x_3605);
if (lean_is_exclusive(x_3604)) {
 lean_ctor_release(x_3604, 0);
 lean_ctor_release(x_3604, 1);
 x_3606 = x_3604;
} else {
 lean_dec_ref(x_3604);
 x_3606 = lean_box(0);
}
x_3607 = 1;
x_3608 = lean_box(x_3607);
if (lean_is_scalar(x_3606)) {
 x_3609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3609 = x_3606;
}
lean_ctor_set(x_3609, 0, x_3608);
lean_ctor_set(x_3609, 1, x_3605);
return x_3609;
}
}
}
else
{
lean_object* x_3610; lean_object* x_3611; lean_object* x_3612; lean_object* x_3613; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3610 = lean_ctor_get(x_3536, 0);
lean_inc(x_3610);
x_3611 = lean_ctor_get(x_3536, 1);
lean_inc(x_3611);
if (lean_is_exclusive(x_3536)) {
 lean_ctor_release(x_3536, 0);
 lean_ctor_release(x_3536, 1);
 x_3612 = x_3536;
} else {
 lean_dec_ref(x_3536);
 x_3612 = lean_box(0);
}
if (lean_is_scalar(x_3612)) {
 x_3613 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3613 = x_3612;
}
lean_ctor_set(x_3613, 0, x_3610);
lean_ctor_set(x_3613, 1, x_3611);
return x_3613;
}
}
}
}
else
{
uint8_t x_3614; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3614 = !lean_is_exclusive(x_3303);
if (x_3614 == 0)
{
return x_3303;
}
else
{
lean_object* x_3615; lean_object* x_3616; lean_object* x_3617; 
x_3615 = lean_ctor_get(x_3303, 0);
x_3616 = lean_ctor_get(x_3303, 1);
lean_inc(x_3616);
lean_inc(x_3615);
lean_dec(x_3303);
x_3617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3617, 0, x_3615);
lean_ctor_set(x_3617, 1, x_3616);
return x_3617;
}
}
}
}
}
block_3632:
{
if (x_3619 == 0)
{
x_3290 = x_3620;
goto block_3618;
}
else
{
lean_object* x_3621; lean_object* x_3622; lean_object* x_3623; lean_object* x_3624; lean_object* x_3625; lean_object* x_3626; lean_object* x_3627; lean_object* x_3628; lean_object* x_3629; lean_object* x_3630; lean_object* x_3631; 
lean_inc(x_1);
x_3621 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3621, 0, x_1);
x_3622 = l_Lean_KernelException_toMessageData___closed__15;
x_3623 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3623, 0, x_3622);
lean_ctor_set(x_3623, 1, x_3621);
x_3624 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_3625 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3625, 0, x_3623);
lean_ctor_set(x_3625, 1, x_3624);
lean_inc(x_2);
x_3626 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3626, 0, x_2);
x_3627 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3627, 0, x_3625);
lean_ctor_set(x_3627, 1, x_3626);
x_3628 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3628, 0, x_3627);
lean_ctor_set(x_3628, 1, x_3622);
x_3629 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_3630 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_3629, x_3628, x_3, x_4, x_5, x_6, x_3620);
x_3631 = lean_ctor_get(x_3630, 1);
lean_inc(x_3631);
lean_dec(x_3630);
x_3290 = x_3631;
goto block_3618;
}
}
}
else
{
lean_object* x_3645; lean_object* x_3646; lean_object* x_3647; uint8_t x_3648; lean_object* x_3649; lean_object* x_3650; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3645 = lean_unsigned_to_nat(0u);
x_3646 = l_Lean_Level_getOffsetAux(x_1, x_3645);
lean_dec(x_1);
x_3647 = l_Lean_Level_getOffsetAux(x_2, x_3645);
lean_dec(x_2);
x_3648 = lean_nat_dec_eq(x_3646, x_3647);
lean_dec(x_3647);
lean_dec(x_3646);
x_3649 = lean_box(x_3648);
x_3650 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3650, 0, x_3649);
lean_ctor_set(x_3650, 1, x_7);
return x_3650;
}
}
}
}
}
lean_object* l_Lean_Meta_isListLevelDefEqAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_apply_2(x_5, x_1, x_2);
return x_8;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_apply_2(x_5, x_1, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_4(x_4, x_10, x_11, x_12, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Meta_isListLevelDefEqAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isListLevelDefEqAux_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isListLevelDefEqAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_Meta_isLevelDefEqAux(x_17, x_19, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_22);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_1 = x_18;
x_2 = x_20;
x_7 = x_28;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Meta_getPostponed___rarg(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
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
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_getResetPostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = l_Lean_Meta_getPostponed___rarg(x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_PersistentArray_empty___closed__1;
x_10 = l_Lean_Meta_setPostponed(x_9, x_1, x_2, x_3, x_4, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Meta_getResetPostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_getResetPostponed(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_2(x_3, x_5, x_7);
return x_8;
}
case 4:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_3(x_2, x_9, x_10, x_12);
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_1(x_4, x_1);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = l_List_foldr___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__1(x_1, x_2, x_5);
x_7 = lean_apply_1(x_1, x_4);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
return x_6;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_215; lean_object* x_229; lean_object* x_230; size_t x_231; uint8_t x_232; 
x_6 = lean_ptr_addr(x_4);
x_7 = x_3 == 0 ? x_6 : x_6 % x_3;
x_229 = lean_ctor_get(x_5, 0);
lean_inc(x_229);
x_230 = lean_array_uget(x_229, x_7);
lean_dec(x_229);
x_231 = lean_ptr_addr(x_230);
lean_dec(x_230);
x_232 = x_231 == x_6;
if (x_232 == 0)
{
switch (lean_obj_tag(x_4)) {
case 3:
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_233 = lean_ctor_get(x_4, 0);
lean_inc(x_233);
lean_inc(x_2);
x_234 = lean_apply_1(x_2, x_233);
x_235 = lean_unbox(x_234);
lean_dec(x_234);
if (x_235 == 0)
{
lean_object* x_236; 
x_236 = lean_box(0);
x_8 = x_236;
goto block_214;
}
else
{
uint8_t x_237; lean_object* x_238; 
lean_dec(x_2);
x_237 = 1;
x_238 = l_Lean_Expr_setPPUniverses(x_1, x_237);
x_215 = x_238;
goto block_228;
}
}
case 4:
{
lean_object* x_239; uint8_t x_240; uint8_t x_241; 
x_239 = lean_ctor_get(x_4, 1);
lean_inc(x_239);
x_240 = 0;
lean_inc(x_2);
x_241 = l_List_foldr___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__1(x_2, x_240, x_239);
if (x_241 == 0)
{
lean_object* x_242; 
x_242 = lean_box(0);
x_8 = x_242;
goto block_214;
}
else
{
uint8_t x_243; lean_object* x_244; 
lean_dec(x_2);
x_243 = 1;
x_244 = l_Lean_Expr_setPPUniverses(x_1, x_243);
x_215 = x_244;
goto block_228;
}
}
default: 
{
lean_object* x_245; 
x_245 = lean_box(0);
x_8 = x_245;
goto block_214;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_246 = lean_ctor_get(x_5, 1);
lean_inc(x_246);
x_247 = lean_array_uget(x_246, x_7);
lean_dec(x_246);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_5);
return x_248;
}
block_214:
{
lean_dec(x_8);
switch (lean_obj_tag(x_4)) {
case 5:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_3, x_9, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_3, x_10, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set_uint64(x_19, sizeof(void*)*2, x_11);
x_20 = lean_expr_update_app(x_19, x_13, x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
x_24 = lean_array_uset(x_22, x_7, x_4);
lean_inc(x_20);
x_25 = lean_array_uset(x_23, x_7, x_20);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_24);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_array_uset(x_26, x_7, x_4);
lean_inc(x_20);
x_29 = lean_array_uset(x_27, x_7, x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_15, 1, x_30);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_10);
lean_ctor_set_uint64(x_33, sizeof(void*)*2, x_11);
x_34 = lean_expr_update_app(x_33, x_13, x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_37 = x_32;
} else {
 lean_dec_ref(x_32);
 x_37 = lean_box(0);
}
x_38 = lean_array_uset(x_35, x_7, x_4);
lean_inc(x_34);
x_39 = lean_array_uset(x_36, x_7, x_34);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
case 6:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 2);
lean_inc(x_44);
x_45 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_43);
lean_inc(x_2);
lean_inc(x_1);
x_46 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_3, x_43, x_5);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_44);
x_49 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_3, x_44, x_48);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
x_53 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set(x_53, 2, x_44);
lean_ctor_set_uint64(x_53, sizeof(void*)*3, x_45);
x_54 = (uint8_t)((x_45 << 24) >> 61);
x_55 = lean_expr_update_lambda(x_53, x_54, x_47, x_51);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
x_59 = lean_array_uset(x_57, x_7, x_4);
lean_inc(x_55);
x_60 = lean_array_uset(x_58, x_7, x_55);
lean_ctor_set(x_52, 1, x_60);
lean_ctor_set(x_52, 0, x_59);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_63 = lean_array_uset(x_61, x_7, x_4);
lean_inc(x_55);
x_64 = lean_array_uset(x_62, x_7, x_55);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_49, 1, x_65);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_66 = lean_ctor_get(x_49, 0);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_49);
x_68 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_43);
lean_ctor_set(x_68, 2, x_44);
lean_ctor_set_uint64(x_68, sizeof(void*)*3, x_45);
x_69 = (uint8_t)((x_45 << 24) >> 61);
x_70 = lean_expr_update_lambda(x_68, x_69, x_47, x_66);
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
x_74 = lean_array_uset(x_71, x_7, x_4);
lean_inc(x_70);
x_75 = lean_array_uset(x_72, x_7, x_70);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
case 7:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_78 = lean_ctor_get(x_4, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_4, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_4, 2);
lean_inc(x_80);
x_81 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_79);
lean_inc(x_2);
lean_inc(x_1);
x_82 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_3, x_79, x_5);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_80);
x_85 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_3, x_80, x_84);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
x_89 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_79);
lean_ctor_set(x_89, 2, x_80);
lean_ctor_set_uint64(x_89, sizeof(void*)*3, x_81);
x_90 = (uint8_t)((x_81 << 24) >> 61);
x_91 = lean_expr_update_forall(x_89, x_90, x_83, x_87);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_88, 0);
x_94 = lean_ctor_get(x_88, 1);
x_95 = lean_array_uset(x_93, x_7, x_4);
lean_inc(x_91);
x_96 = lean_array_uset(x_94, x_7, x_91);
lean_ctor_set(x_88, 1, x_96);
lean_ctor_set(x_88, 0, x_95);
lean_ctor_set(x_85, 0, x_91);
return x_85;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_88);
x_99 = lean_array_uset(x_97, x_7, x_4);
lean_inc(x_91);
x_100 = lean_array_uset(x_98, x_7, x_91);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_85, 1, x_101);
lean_ctor_set(x_85, 0, x_91);
return x_85;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_102 = lean_ctor_get(x_85, 0);
x_103 = lean_ctor_get(x_85, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_85);
x_104 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_104, 0, x_78);
lean_ctor_set(x_104, 1, x_79);
lean_ctor_set(x_104, 2, x_80);
lean_ctor_set_uint64(x_104, sizeof(void*)*3, x_81);
x_105 = (uint8_t)((x_81 << 24) >> 61);
x_106 = lean_expr_update_forall(x_104, x_105, x_83, x_102);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = lean_array_uset(x_107, x_7, x_4);
lean_inc(x_106);
x_111 = lean_array_uset(x_108, x_7, x_106);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
case 8:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint64_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_114 = lean_ctor_get(x_4, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_4, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_4, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_4, 3);
lean_inc(x_117);
x_118 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
lean_inc(x_115);
lean_inc(x_2);
lean_inc(x_1);
x_119 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_3, x_115, x_5);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
lean_inc(x_116);
lean_inc(x_2);
lean_inc(x_1);
x_122 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_3, x_116, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_117);
x_125 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_3, x_117, x_124);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
x_129 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_129, 0, x_114);
lean_ctor_set(x_129, 1, x_115);
lean_ctor_set(x_129, 2, x_116);
lean_ctor_set(x_129, 3, x_117);
lean_ctor_set_uint64(x_129, sizeof(void*)*4, x_118);
x_130 = lean_expr_update_let(x_129, x_120, x_123, x_127);
x_131 = !lean_is_exclusive(x_128);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_128, 0);
x_133 = lean_ctor_get(x_128, 1);
x_134 = lean_array_uset(x_132, x_7, x_4);
lean_inc(x_130);
x_135 = lean_array_uset(x_133, x_7, x_130);
lean_ctor_set(x_128, 1, x_135);
lean_ctor_set(x_128, 0, x_134);
lean_ctor_set(x_125, 0, x_130);
return x_125;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_128, 0);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_128);
x_138 = lean_array_uset(x_136, x_7, x_4);
lean_inc(x_130);
x_139 = lean_array_uset(x_137, x_7, x_130);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_125, 1, x_140);
lean_ctor_set(x_125, 0, x_130);
return x_125;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_141 = lean_ctor_get(x_125, 0);
x_142 = lean_ctor_get(x_125, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_125);
x_143 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_143, 0, x_114);
lean_ctor_set(x_143, 1, x_115);
lean_ctor_set(x_143, 2, x_116);
lean_ctor_set(x_143, 3, x_117);
lean_ctor_set_uint64(x_143, sizeof(void*)*4, x_118);
x_144 = lean_expr_update_let(x_143, x_120, x_123, x_141);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
x_148 = lean_array_uset(x_145, x_7, x_4);
lean_inc(x_144);
x_149 = lean_array_uset(x_146, x_7, x_144);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
case 10:
{
lean_object* x_152; lean_object* x_153; uint64_t x_154; lean_object* x_155; uint8_t x_156; 
x_152 = lean_ctor_get(x_4, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_4, 1);
lean_inc(x_153);
x_154 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_inc(x_153);
x_155 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_3, x_153, x_5);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_159, 0, x_152);
lean_ctor_set(x_159, 1, x_153);
lean_ctor_set_uint64(x_159, sizeof(void*)*2, x_154);
x_160 = lean_expr_update_mdata(x_159, x_157);
x_161 = !lean_is_exclusive(x_158);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_158, 0);
x_163 = lean_ctor_get(x_158, 1);
x_164 = lean_array_uset(x_162, x_7, x_4);
lean_inc(x_160);
x_165 = lean_array_uset(x_163, x_7, x_160);
lean_ctor_set(x_158, 1, x_165);
lean_ctor_set(x_158, 0, x_164);
lean_ctor_set(x_155, 0, x_160);
return x_155;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_array_uset(x_166, x_7, x_4);
lean_inc(x_160);
x_169 = lean_array_uset(x_167, x_7, x_160);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_155, 1, x_170);
lean_ctor_set(x_155, 0, x_160);
return x_155;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_171 = lean_ctor_get(x_155, 0);
x_172 = lean_ctor_get(x_155, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_155);
x_173 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_173, 0, x_152);
lean_ctor_set(x_173, 1, x_153);
lean_ctor_set_uint64(x_173, sizeof(void*)*2, x_154);
x_174 = lean_expr_update_mdata(x_173, x_171);
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_177 = x_172;
} else {
 lean_dec_ref(x_172);
 x_177 = lean_box(0);
}
x_178 = lean_array_uset(x_175, x_7, x_4);
lean_inc(x_174);
x_179 = lean_array_uset(x_176, x_7, x_174);
if (lean_is_scalar(x_177)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_177;
}
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_174);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
case 11:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint64_t x_185; lean_object* x_186; uint8_t x_187; 
x_182 = lean_ctor_get(x_4, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_4, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_4, 2);
lean_inc(x_184);
x_185 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_184);
x_186 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_3, x_184, x_5);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_188 = lean_ctor_get(x_186, 0);
x_189 = lean_ctor_get(x_186, 1);
x_190 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_190, 0, x_182);
lean_ctor_set(x_190, 1, x_183);
lean_ctor_set(x_190, 2, x_184);
lean_ctor_set_uint64(x_190, sizeof(void*)*3, x_185);
x_191 = lean_expr_update_proj(x_190, x_188);
x_192 = !lean_is_exclusive(x_189);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_189, 0);
x_194 = lean_ctor_get(x_189, 1);
x_195 = lean_array_uset(x_193, x_7, x_4);
lean_inc(x_191);
x_196 = lean_array_uset(x_194, x_7, x_191);
lean_ctor_set(x_189, 1, x_196);
lean_ctor_set(x_189, 0, x_195);
lean_ctor_set(x_186, 0, x_191);
return x_186;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_189, 0);
x_198 = lean_ctor_get(x_189, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_189);
x_199 = lean_array_uset(x_197, x_7, x_4);
lean_inc(x_191);
x_200 = lean_array_uset(x_198, x_7, x_191);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_186, 1, x_201);
lean_ctor_set(x_186, 0, x_191);
return x_186;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_202 = lean_ctor_get(x_186, 0);
x_203 = lean_ctor_get(x_186, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_186);
x_204 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_204, 0, x_182);
lean_ctor_set(x_204, 1, x_183);
lean_ctor_set(x_204, 2, x_184);
lean_ctor_set_uint64(x_204, sizeof(void*)*3, x_185);
x_205 = lean_expr_update_proj(x_204, x_202);
x_206 = lean_ctor_get(x_203, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_203, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_208 = x_203;
} else {
 lean_dec_ref(x_203);
 x_208 = lean_box(0);
}
x_209 = lean_array_uset(x_206, x_7, x_4);
lean_inc(x_205);
x_210 = lean_array_uset(x_207, x_7, x_205);
if (lean_is_scalar(x_208)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_208;
}
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_205);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
default: 
{
lean_object* x_213; 
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_4);
lean_ctor_set(x_213, 1, x_5);
return x_213;
}
}
}
block_228:
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_5);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_ctor_get(x_5, 0);
x_218 = lean_ctor_get(x_5, 1);
x_219 = lean_array_uset(x_217, x_7, x_4);
lean_inc(x_215);
x_220 = lean_array_uset(x_218, x_7, x_215);
lean_ctor_set(x_5, 1, x_220);
lean_ctor_set(x_5, 0, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_215);
lean_ctor_set(x_221, 1, x_5);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_5, 0);
x_223 = lean_ctor_get(x_5, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_5);
x_224 = lean_array_uset(x_222, x_7, x_4);
lean_inc(x_215);
x_225 = lean_array_uset(x_223, x_7, x_215);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_215);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_ReplaceImpl_initCache;
lean_inc(x_1);
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_3, x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__1(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
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
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__1___rarg), 8, 0);
return x_2;
}
}
uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_NameSet_contains(x_1, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Level_any(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nwhile trying to unify");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nwith");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termDepIfThenElse___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses(x_6, x_1);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Meta_instantiateMVars(x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_45; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses(x_15, x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_12);
x_45 = l_Lean_Meta_inferType(x_12, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_17);
x_48 = l_Lean_Meta_inferType(x_17, x_7, x_8, x_9, x_10, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_stringToMessageData(x_3);
x_52 = l_Lean_KernelException_toMessageData___closed__15;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_4);
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_5);
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_52);
x_62 = l_Lean_indentD(x_61);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__2;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_12);
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_52);
lean_ctor_set(x_67, 1, x_66);
x_68 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__5;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_46);
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_52);
x_73 = l_Lean_indentD(x_72);
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_73);
x_75 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__4;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_17);
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_52);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_68);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_49);
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_52);
x_83 = l_Lean_indentD(x_82);
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_52);
x_86 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_85, x_7, x_8, x_9, x_10, x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_86;
}
else
{
lean_object* x_87; 
lean_dec(x_46);
x_87 = lean_ctor_get(x_48, 1);
lean_inc(x_87);
lean_dec(x_48);
x_18 = x_87;
goto block_44;
}
}
else
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_45, 1);
lean_inc(x_88);
lean_dec(x_45);
x_18 = x_88;
goto block_44;
}
block_44:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_19 = l_Lean_stringToMessageData(x_3);
x_20 = l_Lean_KernelException_toMessageData___closed__15;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_4);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_5);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
x_30 = l_Lean_indentD(x_29);
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__2;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_12);
x_35 = l_Lean_indentD(x_34);
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__4;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_17);
x_40 = l_Lean_indentD(x_39);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_20);
x_43 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_42, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_43;
}
}
else
{
uint8_t x_89; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_14);
if (x_89 == 0)
{
return x_14;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_14, 0);
x_91 = lean_ctor_get(x_14, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_14);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_Lean_stringToMessageData(x_1);
lean_dec(x_1);
x_10 = l_Lean_KernelException_toMessageData___closed__15;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
x_22 = l_Lean_indentD(x_21);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
lean_dec(x_2);
x_31 = l_Lean_NameSet_empty;
lean_inc(x_30);
x_32 = l_Lean_Level_collectMVars(x_30, x_31);
lean_inc(x_29);
x_33 = l_Lean_Level_collectMVars(x_29, x_32);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__2___boxed), 2, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVars), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___boxed), 11, 5);
lean_closure_set(x_37, 0, x_34);
lean_closure_set(x_37, 1, x_26);
lean_closure_set(x_37, 2, x_1);
lean_closure_set(x_37, 3, x_29);
lean_closure_set(x_37, 4, x_30);
x_38 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_38, 0, x_36);
lean_closure_set(x_38, 1, x_37);
x_39 = l_Lean_Meta_withLCtx___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__1___rarg(x_27, x_28, x_38, x_3, x_4, x_5, x_6, x_7);
return x_39;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_mkLevelStuckErrorMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("stuck at solving universe constraint");
return x_1;
}
}
lean_object* l_Lean_Meta_mkLevelStuckErrorMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_mkLevelStuckErrorMessage___closed__1;
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_mkLevelErrorMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to solve universe constraint");
return x_1;
}
}
lean_object* l_Lean_Meta_mkLevelErrorMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_mkLevelErrorMessage___closed__1;
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_7 < x_6;
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_18 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2(x_1, x_2, x_3, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
lean_inc(x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_31);
x_33 = 1;
x_34 = x_7 + x_33;
x_7 = x_34;
x_8 = x_32;
x_13 = x_30;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
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
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_25; 
x_25 = x_6 < x_5;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_7);
x_27 = lean_array_uget(x_4, x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 2);
lean_inc(x_33);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_35 = l_Lean_Meta_isLevelDefEqAux(x_28, x_29, x_34, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
if (x_1 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_27);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3;
x_13 = x_39;
x_14 = x_38;
goto block_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Lean_Meta_mkLevelErrorMessage___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(x_41, x_27, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_43, x_8, x_9, x_10, x_11, x_44);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_42);
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
lean_object* x_54; lean_object* x_55; 
lean_dec(x_27);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_dec(x_35);
lean_inc(x_2);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_2);
x_13 = x_55;
x_14 = x_54;
goto block_24;
}
}
else
{
uint8_t x_56; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_35);
if (x_56 == 0)
{
return x_35;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_35, 0);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_35);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
block_24:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
lean_inc(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
x_21 = 1;
x_22 = x_6 + x_21;
x_6 = x_22;
x_7 = x_20;
x_12 = x_14;
goto _start;
}
}
}
}
lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
x_14 = lean_array_get_size(x_11);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__3(x_1, x_2, x_3, x_12, x_11, x_15, x_16, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1(x_21, x_22, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_5);
x_37 = lean_array_get_size(x_34);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4(x_1, x_2, x_35, x_34, x_38, x_39, x_36, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1(x_44, x_45, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_40, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_49);
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_25; 
x_25 = x_6 < x_5;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_7);
x_27 = lean_array_uget(x_4, x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 2);
lean_inc(x_33);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_35 = l_Lean_Meta_isLevelDefEqAux(x_28, x_29, x_34, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
if (x_1 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_27);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3;
x_13 = x_39;
x_14 = x_38;
goto block_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Lean_Meta_mkLevelErrorMessage___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(x_41, x_27, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_43, x_8, x_9, x_10, x_11, x_44);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_42);
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
lean_object* x_54; lean_object* x_55; 
lean_dec(x_27);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_dec(x_35);
lean_inc(x_2);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_2);
x_13 = x_55;
x_14 = x_54;
goto block_24;
}
}
else
{
uint8_t x_56; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_35);
if (x_56 == 0)
{
return x_35;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_35, 0);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_35);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
block_24:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
lean_inc(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
x_21 = 1;
x_22 = x_6 + x_21;
x_6 = x_22;
x_7 = x_20;
x_12 = x_14;
goto _start;
}
}
}
}
lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_11 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2(x_1, x_2, x_4, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_get_size(x_21);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__5(x_1, x_2, x_22, x_21, x_25, x_26, x_23, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(lean_object* x_1, lean_object* x_2) {
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
x_16 = l_Std_PersistentArray_empty___closed__1;
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
x_23 = l_Std_PersistentArray_empty___closed__1;
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
x_31 = lean_ctor_get(x_9, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_32 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_33 = x_10;
} else {
 lean_dec_ref(x_10);
 x_33 = lean_box(0);
}
x_34 = l_Std_PersistentArray_empty___closed__1;
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 1, 1);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_32);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_st_ref_set(x_1, x_36, x_11);
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
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__9(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_7 < x_6;
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_18 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8(x_1, x_2, x_3, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
lean_inc(x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_31);
x_33 = 1;
x_34 = x_7 + x_33;
x_7 = x_34;
x_8 = x_32;
x_13 = x_30;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
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
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__10(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_25; 
x_25 = x_6 < x_5;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_7);
x_27 = lean_array_uget(x_4, x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 2);
lean_inc(x_33);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_35 = l_Lean_Meta_isLevelDefEqAux(x_28, x_29, x_34, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
if (x_1 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_27);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3;
x_13 = x_39;
x_14 = x_38;
goto block_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Lean_Meta_mkLevelErrorMessage___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(x_41, x_27, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_43, x_8, x_9, x_10, x_11, x_44);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_42);
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
lean_object* x_54; lean_object* x_55; 
lean_dec(x_27);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_dec(x_35);
lean_inc(x_2);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_2);
x_13 = x_55;
x_14 = x_54;
goto block_24;
}
}
else
{
uint8_t x_56; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_35);
if (x_56 == 0)
{
return x_35;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_35, 0);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_35);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
block_24:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
lean_inc(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
x_21 = 1;
x_22 = x_6 + x_21;
x_6 = x_22;
x_7 = x_20;
x_12 = x_14;
goto _start;
}
}
}
}
lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
x_14 = lean_array_get_size(x_11);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__9(x_1, x_2, x_3, x_12, x_11, x_15, x_16, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1(x_21, x_22, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_5);
x_37 = lean_array_get_size(x_34);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__10(x_1, x_2, x_35, x_34, x_38, x_39, x_36, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1(x_44, x_45, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_40, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_49);
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__11(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_25; 
x_25 = x_6 < x_5;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_7);
x_27 = lean_array_uget(x_4, x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 2);
lean_inc(x_33);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_35 = l_Lean_Meta_isLevelDefEqAux(x_28, x_29, x_34, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
if (x_1 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_27);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3;
x_13 = x_39;
x_14 = x_38;
goto block_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Lean_Meta_mkLevelErrorMessage___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(x_41, x_27, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_43, x_8, x_9, x_10, x_11, x_44);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_42);
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
lean_object* x_54; lean_object* x_55; 
lean_dec(x_27);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_dec(x_35);
lean_inc(x_2);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_2);
x_13 = x_55;
x_14 = x_54;
goto block_24;
}
}
else
{
uint8_t x_56; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_35);
if (x_56 == 0)
{
return x_35;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_35, 0);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_35);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
block_24:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
lean_inc(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
x_21 = 1;
x_22 = x_6 + x_21;
x_6 = x_22;
x_7 = x_20;
x_12 = x_14;
goto _start;
}
}
}
}
lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_11 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8(x_1, x_2, x_4, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_get_size(x_21);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__11(x_1, x_2, x_22, x_21, x_25, x_26, x_23, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 3);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = l_Std_PersistentArray_isEmpty___rarg(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_2);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_2);
x_19 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Std_PersistentArray_toArray___rarg(x_16);
lean_dec(x_16);
x_24 = lean_array_get_size(x_23);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = x_23;
x_28 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_25, x_26, x_27);
x_29 = x_28;
x_30 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_KernelException_toMessageData___closed__15;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_PersistentArray_push___rarg(x_1, x_35);
lean_ctor_set(x_11, 0, x_36);
x_37 = lean_st_ref_set(x_7, x_10, x_12);
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
lean_object* x_44; uint8_t x_45; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_1);
x_44 = lean_st_ref_set(x_7, x_10, x_12);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
x_52 = lean_ctor_get(x_11, 0);
lean_inc(x_52);
lean_dec(x_11);
x_53 = l_Std_PersistentArray_isEmpty___rarg(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_inc(x_2);
x_54 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_54, 0, x_2);
x_55 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Std_PersistentArray_toArray___rarg(x_52);
lean_dec(x_52);
x_60 = lean_array_get_size(x_59);
x_61 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_62 = 0;
x_63 = x_59;
x_64 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_61, x_62, x_63);
x_65 = x_64;
x_66 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_KernelException_toMessageData___closed__15;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_70, 0, x_2);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_3);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Std_PersistentArray_push___rarg(x_1, x_71);
x_73 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_51);
lean_ctor_set(x_10, 3, x_73);
x_74 = lean_st_ref_set(x_7, x_10, x_12);
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
lean_dec(x_52);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_51);
lean_ctor_set(x_10, 3, x_79);
x_80 = lean_st_ref_set(x_7, x_10, x_12);
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
x_83 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_85 = lean_ctor_get(x_10, 0);
x_86 = lean_ctor_get(x_10, 1);
x_87 = lean_ctor_get(x_10, 2);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_10);
x_88 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
x_89 = lean_ctor_get(x_11, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_90 = x_11;
} else {
 lean_dec_ref(x_11);
 x_90 = lean_box(0);
}
x_91 = l_Std_PersistentArray_isEmpty___rarg(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; size_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_inc(x_2);
x_92 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_92, 0, x_2);
x_93 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
x_96 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Std_PersistentArray_toArray___rarg(x_89);
lean_dec(x_89);
x_98 = lean_array_get_size(x_97);
x_99 = lean_usize_of_nat(x_98);
lean_dec(x_98);
x_100 = 0;
x_101 = x_97;
x_102 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_99, x_100, x_101);
x_103 = x_102;
x_104 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_96);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_KernelException_toMessageData___closed__15;
x_107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_108, 0, x_2);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_3);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Std_PersistentArray_push___rarg(x_1, x_109);
if (lean_is_scalar(x_90)) {
 x_111 = lean_alloc_ctor(0, 1, 1);
} else {
 x_111 = x_90;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_88);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_85);
lean_ctor_set(x_112, 1, x_86);
lean_ctor_set(x_112, 2, x_87);
lean_ctor_set(x_112, 3, x_111);
x_113 = lean_st_ref_set(x_7, x_112, x_12);
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
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_89);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_90)) {
 x_118 = lean_alloc_ctor(0, 1, 1);
} else {
 x_118 = x_90;
}
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_88);
x_119 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_119, 0, x_85);
lean_ctor_set(x_119, 1, x_86);
lean_ctor_set(x_119, 2, x_87);
lean_ctor_set(x_119, 3, x_118);
x_120 = lean_st_ref_set(x_7, x_119, x_12);
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
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("postponed");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_2 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_933____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_308 = lean_st_ref_get(x_5, x_6);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_309, 3);
lean_inc(x_310);
lean_dec(x_309);
x_311 = lean_ctor_get_uint8(x_310, sizeof(void*)*1);
lean_dec(x_310);
if (x_311 == 0)
{
lean_object* x_312; uint8_t x_313; 
x_312 = lean_ctor_get(x_308, 1);
lean_inc(x_312);
lean_dec(x_308);
x_313 = 0;
x_7 = x_313;
x_8 = x_312;
goto block_307;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_314 = lean_ctor_get(x_308, 1);
lean_inc(x_314);
lean_dec(x_308);
x_315 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3;
x_316 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_315, x_2, x_3, x_4, x_5, x_314);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_unbox(x_317);
lean_dec(x_317);
x_7 = x_319;
x_8 = x_318;
goto block_307;
}
block_307:
{
if (x_7 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_5, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 3);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_62; lean_object* x_63; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_21 = 0;
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_21);
x_22 = lean_st_ref_set(x_5, x_15, x_17);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_96 = l_Lean_Meta_getResetPostponed(x_2, x_3, x_4, x_5, x_23);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Array_findSomeM_x3f___rarg___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_100 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1(x_1, x_99, x_97, x_99, x_2, x_3, x_4, x_5, x_98);
lean_dec(x_97);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
x_105 = lean_box(0);
lean_inc(x_5);
x_106 = lean_apply_6(x_104, x_105, x_2, x_3, x_4, x_5, x_103);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_unbox(x_107);
lean_dec(x_107);
x_24 = x_109;
x_25 = x_108;
goto block_61;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_106, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_62 = x_110;
x_63 = x_111;
goto block_95;
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_112 = lean_ctor_get(x_100, 1);
lean_inc(x_112);
lean_dec(x_100);
x_113 = lean_ctor_get(x_102, 0);
lean_inc(x_113);
lean_dec(x_102);
x_114 = lean_unbox(x_113);
lean_dec(x_113);
x_24 = x_114;
x_25 = x_112;
goto block_61;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_115 = lean_ctor_get(x_100, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_100, 1);
lean_inc(x_116);
lean_dec(x_100);
x_62 = x_115;
x_63 = x_116;
goto block_95;
}
block_61:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_st_ref_get(x_5, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_take(x_5, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 3);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_13);
x_35 = lean_st_ref_set(x_5, x_29, x_31);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(x_24);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(x_24);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_30, 0);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_13);
lean_ctor_set(x_29, 3, x_43);
x_44 = lean_st_ref_set(x_5, x_29, x_31);
lean_dec(x_5);
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
x_47 = lean_box(x_24);
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
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_ctor_get(x_29, 1);
x_51 = lean_ctor_get(x_29, 2);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_29);
x_52 = lean_ctor_get(x_30, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_53 = x_30;
} else {
 lean_dec_ref(x_30);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 1, 1);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_13);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set(x_55, 3, x_54);
x_56 = lean_st_ref_set(x_5, x_55, x_31);
lean_dec(x_5);
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
x_59 = lean_box(x_24);
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
block_95:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_st_ref_get(x_5, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_take(x_5, x_65);
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
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_13);
x_73 = lean_st_ref_set(x_5, x_67, x_69);
lean_dec(x_5);
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
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_13);
lean_ctor_set(x_67, 3, x_79);
x_80 = lean_st_ref_set(x_5, x_67, x_69);
lean_dec(x_5);
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
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_13);
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set(x_90, 2, x_86);
lean_ctor_set(x_90, 3, x_89);
x_91 = lean_st_ref_set(x_5, x_90, x_69);
lean_dec(x_5);
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
lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_144; lean_object* x_145; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_117 = lean_ctor_get(x_16, 0);
lean_inc(x_117);
lean_dec(x_16);
x_118 = 0;
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
lean_ctor_set(x_15, 3, x_119);
x_120 = lean_st_ref_set(x_5, x_15, x_17);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_165 = l_Lean_Meta_getResetPostponed(x_2, x_3, x_4, x_5, x_121);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_Array_findSomeM_x3f___rarg___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_169 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1(x_1, x_168, x_166, x_168, x_2, x_3, x_4, x_5, x_167);
lean_dec(x_166);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec(x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
x_174 = lean_box(0);
lean_inc(x_5);
x_175 = lean_apply_6(x_173, x_174, x_2, x_3, x_4, x_5, x_172);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_unbox(x_176);
lean_dec(x_176);
x_122 = x_178;
x_123 = x_177;
goto block_143;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_175, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
lean_dec(x_175);
x_144 = x_179;
x_145 = x_180;
goto block_164;
}
}
else
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_181 = lean_ctor_get(x_169, 1);
lean_inc(x_181);
lean_dec(x_169);
x_182 = lean_ctor_get(x_171, 0);
lean_inc(x_182);
lean_dec(x_171);
x_183 = lean_unbox(x_182);
lean_dec(x_182);
x_122 = x_183;
x_123 = x_181;
goto block_143;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_184 = lean_ctor_get(x_169, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_169, 1);
lean_inc(x_185);
lean_dec(x_169);
x_144 = x_184;
x_145 = x_185;
goto block_164;
}
block_143:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_124 = lean_st_ref_get(x_5, x_123);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_st_ref_take(x_5, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 2);
lean_inc(x_132);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 x_133 = x_127;
} else {
 lean_dec_ref(x_127);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_128, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_135 = x_128;
} else {
 lean_dec_ref(x_128);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 1, 1);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_133)) {
 x_137 = lean_alloc_ctor(0, 4, 0);
} else {
 x_137 = x_133;
}
lean_ctor_set(x_137, 0, x_130);
lean_ctor_set(x_137, 1, x_131);
lean_ctor_set(x_137, 2, x_132);
lean_ctor_set(x_137, 3, x_136);
x_138 = lean_st_ref_set(x_5, x_137, x_129);
lean_dec(x_5);
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
x_141 = lean_box(x_122);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_139);
return x_142;
}
block_164:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_146 = lean_st_ref_get(x_5, x_145);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_148 = lean_st_ref_take(x_5, x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec(x_148);
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_149, 2);
lean_inc(x_154);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 lean_ctor_release(x_149, 3);
 x_155 = x_149;
} else {
 lean_dec_ref(x_149);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_150, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_157 = x_150;
} else {
 lean_dec_ref(x_150);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 1, 1);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set_uint8(x_158, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_155)) {
 x_159 = lean_alloc_ctor(0, 4, 0);
} else {
 x_159 = x_155;
}
lean_ctor_set(x_159, 0, x_152);
lean_ctor_set(x_159, 1, x_153);
lean_ctor_set(x_159, 2, x_154);
lean_ctor_set(x_159, 3, x_158);
x_160 = lean_st_ref_set(x_5, x_159, x_151);
lean_dec(x_5);
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
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
 lean_ctor_set_tag(x_163, 1);
}
lean_ctor_set(x_163, 0, x_144);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_218; lean_object* x_219; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_186 = lean_ctor_get(x_15, 0);
x_187 = lean_ctor_get(x_15, 1);
x_188 = lean_ctor_get(x_15, 2);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_15);
x_189 = lean_ctor_get(x_16, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_190 = x_16;
} else {
 lean_dec_ref(x_16);
 x_190 = lean_box(0);
}
x_191 = 0;
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(0, 1, 1);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set_uint8(x_192, sizeof(void*)*1, x_191);
x_193 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_193, 0, x_186);
lean_ctor_set(x_193, 1, x_187);
lean_ctor_set(x_193, 2, x_188);
lean_ctor_set(x_193, 3, x_192);
x_194 = lean_st_ref_set(x_5, x_193, x_17);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_239 = l_Lean_Meta_getResetPostponed(x_2, x_3, x_4, x_5, x_195);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = l_Array_findSomeM_x3f___rarg___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_243 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1(x_1, x_242, x_240, x_242, x_2, x_3, x_4, x_5, x_241);
lean_dec(x_240);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec(x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
lean_dec(x_243);
x_247 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
x_248 = lean_box(0);
lean_inc(x_5);
x_249 = lean_apply_6(x_247, x_248, x_2, x_3, x_4, x_5, x_246);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_unbox(x_250);
lean_dec(x_250);
x_196 = x_252;
x_197 = x_251;
goto block_217;
}
else
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_249, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_249, 1);
lean_inc(x_254);
lean_dec(x_249);
x_218 = x_253;
x_219 = x_254;
goto block_238;
}
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_255 = lean_ctor_get(x_243, 1);
lean_inc(x_255);
lean_dec(x_243);
x_256 = lean_ctor_get(x_245, 0);
lean_inc(x_256);
lean_dec(x_245);
x_257 = lean_unbox(x_256);
lean_dec(x_256);
x_196 = x_257;
x_197 = x_255;
goto block_217;
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_258 = lean_ctor_get(x_243, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_243, 1);
lean_inc(x_259);
lean_dec(x_243);
x_218 = x_258;
x_219 = x_259;
goto block_238;
}
block_217:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_198 = lean_st_ref_get(x_5, x_197);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_st_ref_take(x_5, x_199);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_201, 3);
lean_inc(x_202);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec(x_200);
x_204 = lean_ctor_get(x_201, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_201, 2);
lean_inc(x_206);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 lean_ctor_release(x_201, 2);
 lean_ctor_release(x_201, 3);
 x_207 = x_201;
} else {
 lean_dec_ref(x_201);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_202, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_209 = x_202;
} else {
 lean_dec_ref(x_202);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 1, 1);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set_uint8(x_210, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_207)) {
 x_211 = lean_alloc_ctor(0, 4, 0);
} else {
 x_211 = x_207;
}
lean_ctor_set(x_211, 0, x_204);
lean_ctor_set(x_211, 1, x_205);
lean_ctor_set(x_211, 2, x_206);
lean_ctor_set(x_211, 3, x_210);
x_212 = lean_st_ref_set(x_5, x_211, x_203);
lean_dec(x_5);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
x_215 = lean_box(x_196);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_213);
return x_216;
}
block_238:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_220 = lean_st_ref_get(x_5, x_219);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_st_ref_take(x_5, x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_223, 3);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_ctor_get(x_223, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_223, 2);
lean_inc(x_228);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 lean_ctor_release(x_223, 2);
 lean_ctor_release(x_223, 3);
 x_229 = x_223;
} else {
 lean_dec_ref(x_223);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_224, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 x_231 = x_224;
} else {
 lean_dec_ref(x_224);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(0, 1, 1);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set_uint8(x_232, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_229)) {
 x_233 = lean_alloc_ctor(0, 4, 0);
} else {
 x_233 = x_229;
}
lean_ctor_set(x_233, 0, x_226);
lean_ctor_set(x_233, 1, x_227);
lean_ctor_set(x_233, 2, x_228);
lean_ctor_set(x_233, 3, x_232);
x_234 = lean_st_ref_set(x_5, x_233, x_225);
lean_dec(x_5);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_236 = x_234;
} else {
 lean_dec_ref(x_234);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
 lean_ctor_set_tag(x_237, 1);
}
lean_ctor_set(x_237, 0, x_218);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_260 = lean_ctor_get(x_4, 3);
lean_inc(x_260);
x_261 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(x_5, x_8);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = l_Lean_Meta_getResetPostponed(x_2, x_3, x_4, x_5, x_263);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = l_Array_findSomeM_x3f___rarg___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_268 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7(x_1, x_267, x_265, x_267, x_2, x_3, x_4, x_5, x_266);
lean_dec(x_265);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
lean_dec(x_269);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_dec(x_268);
x_272 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
x_273 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_274 = lean_apply_6(x_272, x_273, x_2, x_3, x_4, x_5, x_271);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3;
x_278 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_262, x_277, x_260, x_2, x_3, x_4, x_5, x_276);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_279 = !lean_is_exclusive(x_278);
if (x_279 == 0)
{
lean_object* x_280; 
x_280 = lean_ctor_get(x_278, 0);
lean_dec(x_280);
lean_ctor_set(x_278, 0, x_275);
return x_278;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_281);
lean_dec(x_278);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_275);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_283 = lean_ctor_get(x_274, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_274, 1);
lean_inc(x_284);
lean_dec(x_274);
x_285 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3;
x_286 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_262, x_285, x_260, x_2, x_3, x_4, x_5, x_284);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_287 = !lean_is_exclusive(x_286);
if (x_287 == 0)
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_286, 0);
lean_dec(x_288);
lean_ctor_set_tag(x_286, 1);
lean_ctor_set(x_286, 0, x_283);
return x_286;
}
else
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
lean_dec(x_286);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_283);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_291 = lean_ctor_get(x_268, 1);
lean_inc(x_291);
lean_dec(x_268);
x_292 = lean_ctor_get(x_270, 0);
lean_inc(x_292);
lean_dec(x_270);
x_293 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3;
x_294 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_262, x_293, x_260, x_2, x_3, x_4, x_5, x_291);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_295 = !lean_is_exclusive(x_294);
if (x_295 == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_294, 0);
lean_dec(x_296);
lean_ctor_set(x_294, 0, x_292);
return x_294;
}
else
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_292);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_299 = lean_ctor_get(x_268, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_268, 1);
lean_inc(x_300);
lean_dec(x_268);
x_301 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3;
x_302 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_262, x_301, x_260, x_2, x_3, x_4, x_5, x_300);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_303 = !lean_is_exclusive(x_302);
if (x_303 == 0)
{
lean_object* x_304; 
x_304 = lean_ctor_get(x_302, 0);
lean_dec(x_304);
lean_ctor_set_tag(x_302, 1);
lean_ctor_set(x_302, 0, x_299);
return x_302;
}
else
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_302, 1);
lean_inc(x_305);
lean_dec(x_302);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_299);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__3(x_14, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
return x_17;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4(x_13, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__5(x_13, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__9(x_14, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
return x_17;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__10(x_13, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__11(x_13, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_processPostponed_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no progress solving pending is-def-eq level constraints");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_processPostponed_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_processPostponed_loop___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_processPostponed_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("processing #");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_processPostponed_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_processPostponed_loop___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_processPostponed_loop___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" postponed is-def-eq level constraints");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_processPostponed_loop___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_processPostponed_loop___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_processPostponed_loop(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg(x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_103; lean_object* x_104; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_free_object(x_8);
x_115 = lean_st_ref_get(x_6, x_11);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 3);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_ctor_get_uint8(x_117, sizeof(void*)*1);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_dec(x_115);
x_120 = 0;
x_103 = x_120;
x_104 = x_119;
goto block_114;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
lean_dec(x_115);
x_122 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_123 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_122, x_3, x_4, x_5, x_6, x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_unbox(x_124);
lean_dec(x_124);
x_103 = x_126;
x_104 = x_125;
goto block_114;
}
block_102:
{
lean_object* x_15; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep(x_2, x_3, x_4, x_5, x_6, x_14);
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
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = 0;
x_21 = lean_box(x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg(x_4, x_5, x_6, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_nat_dec_eq(x_29, x_12);
if (x_31 == 0)
{
uint8_t x_32; 
lean_free_object(x_27);
x_32 = lean_nat_dec_lt(x_29, x_10);
lean_dec(x_10);
lean_dec(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_st_ref_get(x_6, x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_33, 0);
lean_dec(x_38);
x_39 = lean_box(x_1);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_box(x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_dec(x_33);
x_44 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_45 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_44, x_3, x_4, x_5, x_6, x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 0);
lean_dec(x_49);
x_50 = lean_box(x_1);
lean_ctor_set(x_45, 0, x_50);
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_box(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec(x_45);
x_55 = l_Lean_Meta_processPostponed_loop___closed__2;
x_56 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_44, x_55, x_3, x_4, x_5, x_6, x_54);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_box(x_1);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_box(x_1);
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
x_7 = x_30;
goto _start;
}
}
else
{
uint8_t x_64; lean_object* x_65; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = 1;
x_65 = lean_box(x_64);
lean_ctor_set(x_27, 0, x_65);
return x_27;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_27, 0);
x_67 = lean_ctor_get(x_27, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_27);
x_68 = lean_nat_dec_eq(x_66, x_12);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = lean_nat_dec_lt(x_66, x_10);
lean_dec(x_10);
lean_dec(x_66);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_st_ref_get(x_6, x_67);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 3);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get_uint8(x_72, sizeof(void*)*1);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_75 = x_70;
} else {
 lean_dec_ref(x_70);
 x_75 = lean_box(0);
}
x_76 = lean_box(x_1);
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
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_70, 1);
lean_inc(x_78);
lean_dec(x_70);
x_79 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_80 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_79, x_3, x_4, x_5, x_6, x_78);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_84 = x_80;
} else {
 lean_dec_ref(x_80);
 x_84 = lean_box(0);
}
x_85 = lean_box(x_1);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_80, 1);
lean_inc(x_87);
lean_dec(x_80);
x_88 = l_Lean_Meta_processPostponed_loop___closed__2;
x_89 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_79, x_88, x_3, x_4, x_5, x_6, x_87);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_92 = lean_box(x_1);
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
else
{
x_7 = x_67;
goto _start;
}
}
else
{
uint8_t x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_66);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = 1;
x_96 = lean_box(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_67);
return x_97;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = !lean_is_exclusive(x_15);
if (x_98 == 0)
{
return x_15;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_15, 0);
x_100 = lean_ctor_get(x_15, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_15);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
block_114:
{
if (x_103 == 0)
{
x_14 = x_104;
goto block_102;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_inc(x_10);
x_105 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_10);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = l_Lean_Meta_processPostponed_loop___closed__4;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Meta_processPostponed_loop___closed__6;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_112 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_111, x_110, x_3, x_4, x_5, x_6, x_104);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_14 = x_113;
goto block_102;
}
}
}
else
{
uint8_t x_127; lean_object* x_128; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_127 = 1;
x_128 = lean_box(x_127);
lean_ctor_set(x_8, 0, x_128);
return x_8;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_8, 0);
x_130 = lean_ctor_get(x_8, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_8);
x_131 = lean_unsigned_to_nat(0u);
x_132 = lean_nat_dec_eq(x_129, x_131);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_182; lean_object* x_183; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_194 = lean_st_ref_get(x_6, x_130);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_195, 3);
lean_inc(x_196);
lean_dec(x_195);
x_197 = lean_ctor_get_uint8(x_196, sizeof(void*)*1);
lean_dec(x_196);
if (x_197 == 0)
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
lean_dec(x_194);
x_199 = 0;
x_182 = x_199;
x_183 = x_198;
goto block_193;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_ctor_get(x_194, 1);
lean_inc(x_200);
lean_dec(x_194);
x_201 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_202 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_201, x_3, x_4, x_5, x_6, x_200);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_unbox(x_203);
lean_dec(x_203);
x_182 = x_205;
x_183 = x_204;
goto block_193;
}
block_181:
{
lean_object* x_134; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_134 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep(x_2, x_3, x_4, x_5, x_6, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_129);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_138 = x_134;
} else {
 lean_dec_ref(x_134);
 x_138 = lean_box(0);
}
x_139 = 0;
x_140 = lean_box(x_139);
if (lean_is_scalar(x_138)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_138;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_137);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_142 = lean_ctor_get(x_134, 1);
lean_inc(x_142);
lean_dec(x_134);
x_143 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg(x_4, x_5, x_6, x_142);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
x_147 = lean_nat_dec_eq(x_144, x_131);
if (x_147 == 0)
{
uint8_t x_148; 
lean_dec(x_146);
x_148 = lean_nat_dec_lt(x_144, x_129);
lean_dec(x_129);
lean_dec(x_144);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = lean_st_ref_get(x_6, x_145);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_150, 3);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_ctor_get_uint8(x_151, sizeof(void*)*1);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_154 = x_149;
} else {
 lean_dec_ref(x_149);
 x_154 = lean_box(0);
}
x_155 = lean_box(x_1);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_149, 1);
lean_inc(x_157);
lean_dec(x_149);
x_158 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_159 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_158, x_3, x_4, x_5, x_6, x_157);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_unbox(x_160);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_163 = x_159;
} else {
 lean_dec_ref(x_159);
 x_163 = lean_box(0);
}
x_164 = lean_box(x_1);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
lean_dec(x_159);
x_167 = l_Lean_Meta_processPostponed_loop___closed__2;
x_168 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_158, x_167, x_3, x_4, x_5, x_6, x_166);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_171 = lean_box(x_1);
if (lean_is_scalar(x_170)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_170;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_169);
return x_172;
}
}
}
else
{
x_7 = x_145;
goto _start;
}
}
else
{
uint8_t x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_144);
lean_dec(x_129);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_174 = 1;
x_175 = lean_box(x_174);
if (lean_is_scalar(x_146)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_146;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_145);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_129);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_177 = lean_ctor_get(x_134, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_134, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_179 = x_134;
} else {
 lean_dec_ref(x_134);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
block_193:
{
if (x_182 == 0)
{
x_133 = x_183;
goto block_181;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_inc(x_129);
x_184 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_129);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_186 = l_Lean_Meta_processPostponed_loop___closed__4;
x_187 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
x_188 = l_Lean_Meta_processPostponed_loop___closed__6;
x_189 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_191 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_190, x_189, x_3, x_4, x_5, x_6, x_183);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_133 = x_192;
goto block_181;
}
}
}
else
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_129);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_206 = 1;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_130);
return x_208;
}
}
}
}
lean_object* l_Lean_Meta_processPostponed_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_processPostponed_loop(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_Meta_processPostponed(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg(x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_10, x_12);
lean_dec(x_10);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
lean_free_object(x_8);
x_217 = lean_st_ref_get(x_6, x_11);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_218, 3);
lean_inc(x_219);
lean_dec(x_218);
x_220 = lean_ctor_get_uint8(x_219, sizeof(void*)*1);
lean_dec(x_219);
if (x_220 == 0)
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_217, 1);
lean_inc(x_221);
lean_dec(x_217);
x_222 = 0;
x_14 = x_222;
x_15 = x_221;
goto block_216;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_223 = lean_ctor_get(x_217, 1);
lean_inc(x_223);
lean_dec(x_217);
x_224 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_225 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_224, x_3, x_4, x_5, x_6, x_223);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_unbox(x_226);
lean_dec(x_226);
x_14 = x_228;
x_15 = x_227;
goto block_216;
}
block_216:
{
if (x_14 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_st_ref_get(x_6, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_dec(x_18);
x_21 = lean_st_ref_take(x_6, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_22, 3);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = 0;
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_28);
x_29 = lean_st_ref_set(x_6, x_22, x_24);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_6);
x_31 = l_Lean_Meta_processPostponed_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_6, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_take(x_6, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 3);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_20);
x_43 = lean_st_ref_set(x_6, x_37, x_39);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_32);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_20);
lean_ctor_set(x_37, 3, x_49);
x_50 = lean_st_ref_set(x_6, x_37, x_39);
lean_dec(x_6);
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
lean_ctor_set(x_53, 0, x_32);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
x_56 = lean_ctor_get(x_37, 2);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
x_57 = lean_ctor_get(x_38, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_58 = x_38;
} else {
 lean_dec_ref(x_38);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 1, 1);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_20);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_59);
x_61 = lean_st_ref_set(x_6, x_60, x_39);
lean_dec(x_6);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_32);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_65 = lean_ctor_get(x_31, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_31, 1);
lean_inc(x_66);
lean_dec(x_31);
x_67 = lean_st_ref_get(x_6, x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_take(x_6, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_70, 3);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_20);
x_76 = lean_st_ref_set(x_6, x_70, x_72);
lean_dec(x_6);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 0, x_65);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_65);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
lean_dec(x_71);
x_82 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_20);
lean_ctor_set(x_70, 3, x_82);
x_83 = lean_st_ref_set(x_6, x_70, x_72);
lean_dec(x_6);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
 lean_ctor_set_tag(x_86, 1);
}
lean_ctor_set(x_86, 0, x_65);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_87 = lean_ctor_get(x_70, 0);
x_88 = lean_ctor_get(x_70, 1);
x_89 = lean_ctor_get(x_70, 2);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_70);
x_90 = lean_ctor_get(x_71, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_91 = x_71;
} else {
 lean_dec_ref(x_71);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 1, 1);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_20);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_88);
lean_ctor_set(x_93, 2, x_89);
lean_ctor_set(x_93, 3, x_92);
x_94 = lean_st_ref_set(x_6, x_93, x_72);
lean_dec(x_6);
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
lean_ctor_set(x_97, 0, x_65);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_23, 0);
lean_inc(x_98);
lean_dec(x_23);
x_99 = 0;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
lean_ctor_set(x_22, 3, x_100);
x_101 = lean_st_ref_set(x_6, x_22, x_24);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
lean_inc(x_6);
x_103 = l_Lean_Meta_processPostponed_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_st_ref_get(x_6, x_105);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_take(x_6, x_107);
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
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 lean_ctor_release(x_109, 2);
 lean_ctor_release(x_109, 3);
 x_115 = x_109;
} else {
 lean_dec_ref(x_109);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_117 = x_110;
} else {
 lean_dec_ref(x_110);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 1, 1);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_20);
if (lean_is_scalar(x_115)) {
 x_119 = lean_alloc_ctor(0, 4, 0);
} else {
 x_119 = x_115;
}
lean_ctor_set(x_119, 0, x_112);
lean_ctor_set(x_119, 1, x_113);
lean_ctor_set(x_119, 2, x_114);
lean_ctor_set(x_119, 3, x_118);
x_120 = lean_st_ref_set(x_6, x_119, x_111);
lean_dec(x_6);
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
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_104);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_124 = lean_ctor_get(x_103, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_103, 1);
lean_inc(x_125);
lean_dec(x_103);
x_126 = lean_st_ref_get(x_6, x_125);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_st_ref_take(x_6, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_129, 2);
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
x_136 = lean_ctor_get(x_130, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_137 = x_130;
} else {
 lean_dec_ref(x_130);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 1, 1);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set_uint8(x_138, sizeof(void*)*1, x_20);
if (lean_is_scalar(x_135)) {
 x_139 = lean_alloc_ctor(0, 4, 0);
} else {
 x_139 = x_135;
}
lean_ctor_set(x_139, 0, x_132);
lean_ctor_set(x_139, 1, x_133);
lean_ctor_set(x_139, 2, x_134);
lean_ctor_set(x_139, 3, x_138);
x_140 = lean_st_ref_set(x_6, x_139, x_131);
lean_dec(x_6);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
 lean_ctor_set_tag(x_143, 1);
}
lean_ctor_set(x_143, 0, x_124);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_144 = lean_ctor_get(x_22, 0);
x_145 = lean_ctor_get(x_22, 1);
x_146 = lean_ctor_get(x_22, 2);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_22);
x_147 = lean_ctor_get(x_23, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_148 = x_23;
} else {
 lean_dec_ref(x_23);
 x_148 = lean_box(0);
}
x_149 = 0;
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(0, 1, 1);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set_uint8(x_150, sizeof(void*)*1, x_149);
x_151 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_145);
lean_ctor_set(x_151, 2, x_146);
lean_ctor_set(x_151, 3, x_150);
x_152 = lean_st_ref_set(x_6, x_151, x_24);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
lean_inc(x_6);
x_154 = l_Lean_Meta_processPostponed_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_st_ref_get(x_6, x_156);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_st_ref_take(x_6, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 2);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_161, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_168 = x_161;
} else {
 lean_dec_ref(x_161);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(0, 1, 1);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*1, x_20);
if (lean_is_scalar(x_166)) {
 x_170 = lean_alloc_ctor(0, 4, 0);
} else {
 x_170 = x_166;
}
lean_ctor_set(x_170, 0, x_163);
lean_ctor_set(x_170, 1, x_164);
lean_ctor_set(x_170, 2, x_165);
lean_ctor_set(x_170, 3, x_169);
x_171 = lean_st_ref_set(x_6, x_170, x_162);
lean_dec(x_6);
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
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_155);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_175 = lean_ctor_get(x_154, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_154, 1);
lean_inc(x_176);
lean_dec(x_154);
x_177 = lean_st_ref_get(x_6, x_176);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_st_ref_take(x_6, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_180, 3);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_183 = lean_ctor_get(x_180, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_180, 2);
lean_inc(x_185);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 x_186 = x_180;
} else {
 lean_dec_ref(x_180);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_181, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_188 = x_181;
} else {
 lean_dec_ref(x_181);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(0, 1, 1);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set_uint8(x_189, sizeof(void*)*1, x_20);
if (lean_is_scalar(x_186)) {
 x_190 = lean_alloc_ctor(0, 4, 0);
} else {
 x_190 = x_186;
}
lean_ctor_set(x_190, 0, x_183);
lean_ctor_set(x_190, 1, x_184);
lean_ctor_set(x_190, 2, x_185);
lean_ctor_set(x_190, 3, x_189);
x_191 = lean_st_ref_set(x_6, x_190, x_182);
lean_dec(x_6);
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
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
 lean_ctor_set_tag(x_194, 1);
}
lean_ctor_set(x_194, 0, x_175);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_5, 3);
lean_inc(x_195);
x_196 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(x_6, x_15);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_199 = l_Lean_Meta_processPostponed_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_203 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_197, x_202, x_195, x_3, x_4, x_5, x_6, x_201);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_203, 0);
lean_dec(x_205);
lean_ctor_set(x_203, 0, x_200);
return x_203;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_dec(x_203);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_200);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_208 = lean_ctor_get(x_199, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_199, 1);
lean_inc(x_209);
lean_dec(x_199);
x_210 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_211 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_197, x_210, x_195, x_3, x_4, x_5, x_6, x_209);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_211, 0);
lean_dec(x_213);
lean_ctor_set_tag(x_211, 1);
lean_ctor_set(x_211, 0, x_208);
return x_211;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_208);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
}
else
{
uint8_t x_229; lean_object* x_230; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_229 = 1;
x_230 = lean_box(x_229);
lean_ctor_set(x_8, 0, x_230);
return x_8;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_231 = lean_ctor_get(x_8, 0);
x_232 = lean_ctor_get(x_8, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_8);
x_233 = lean_unsigned_to_nat(0u);
x_234 = lean_nat_dec_eq(x_231, x_233);
lean_dec(x_231);
if (x_234 == 0)
{
uint8_t x_235; lean_object* x_236; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_318 = lean_st_ref_get(x_6, x_232);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_319, 3);
lean_inc(x_320);
lean_dec(x_319);
x_321 = lean_ctor_get_uint8(x_320, sizeof(void*)*1);
lean_dec(x_320);
if (x_321 == 0)
{
lean_object* x_322; uint8_t x_323; 
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
lean_dec(x_318);
x_323 = 0;
x_235 = x_323;
x_236 = x_322;
goto block_317;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_324 = lean_ctor_get(x_318, 1);
lean_inc(x_324);
lean_dec(x_318);
x_325 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_326 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_325, x_3, x_4, x_5, x_6, x_324);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_unbox(x_327);
lean_dec(x_327);
x_235 = x_329;
x_236 = x_328;
goto block_317;
}
block_317:
{
if (x_235 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_237 = lean_st_ref_get(x_6, x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_238, 3);
lean_inc(x_239);
lean_dec(x_238);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_ctor_get_uint8(x_239, sizeof(void*)*1);
lean_dec(x_239);
x_242 = lean_st_ref_take(x_6, x_240);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_243, 3);
lean_inc(x_244);
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
lean_dec(x_242);
x_246 = lean_ctor_get(x_243, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_243, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_243, 2);
lean_inc(x_248);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 lean_ctor_release(x_243, 2);
 lean_ctor_release(x_243, 3);
 x_249 = x_243;
} else {
 lean_dec_ref(x_243);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_244, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_251 = x_244;
} else {
 lean_dec_ref(x_244);
 x_251 = lean_box(0);
}
x_252 = 0;
if (lean_is_scalar(x_251)) {
 x_253 = lean_alloc_ctor(0, 1, 1);
} else {
 x_253 = x_251;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set_uint8(x_253, sizeof(void*)*1, x_252);
if (lean_is_scalar(x_249)) {
 x_254 = lean_alloc_ctor(0, 4, 0);
} else {
 x_254 = x_249;
}
lean_ctor_set(x_254, 0, x_246);
lean_ctor_set(x_254, 1, x_247);
lean_ctor_set(x_254, 2, x_248);
lean_ctor_set(x_254, 3, x_253);
x_255 = lean_st_ref_set(x_6, x_254, x_245);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec(x_255);
lean_inc(x_6);
x_257 = l_Lean_Meta_processPostponed_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_st_ref_get(x_6, x_259);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
x_262 = lean_st_ref_take(x_6, x_261);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_263, 3);
lean_inc(x_264);
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
lean_dec(x_262);
x_266 = lean_ctor_get(x_263, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_263, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 2);
lean_inc(x_268);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 lean_ctor_release(x_263, 2);
 lean_ctor_release(x_263, 3);
 x_269 = x_263;
} else {
 lean_dec_ref(x_263);
 x_269 = lean_box(0);
}
x_270 = lean_ctor_get(x_264, 0);
lean_inc(x_270);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 x_271 = x_264;
} else {
 lean_dec_ref(x_264);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 1, 1);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set_uint8(x_272, sizeof(void*)*1, x_241);
if (lean_is_scalar(x_269)) {
 x_273 = lean_alloc_ctor(0, 4, 0);
} else {
 x_273 = x_269;
}
lean_ctor_set(x_273, 0, x_266);
lean_ctor_set(x_273, 1, x_267);
lean_ctor_set(x_273, 2, x_268);
lean_ctor_set(x_273, 3, x_272);
x_274 = lean_st_ref_set(x_6, x_273, x_265);
lean_dec(x_6);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_258);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_278 = lean_ctor_get(x_257, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_257, 1);
lean_inc(x_279);
lean_dec(x_257);
x_280 = lean_st_ref_get(x_6, x_279);
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
lean_dec(x_280);
x_282 = lean_st_ref_take(x_6, x_281);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_283, 3);
lean_inc(x_284);
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
lean_dec(x_282);
x_286 = lean_ctor_get(x_283, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_283, 1);
lean_inc(x_287);
x_288 = lean_ctor_get(x_283, 2);
lean_inc(x_288);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 lean_ctor_release(x_283, 2);
 lean_ctor_release(x_283, 3);
 x_289 = x_283;
} else {
 lean_dec_ref(x_283);
 x_289 = lean_box(0);
}
x_290 = lean_ctor_get(x_284, 0);
lean_inc(x_290);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 x_291 = x_284;
} else {
 lean_dec_ref(x_284);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(0, 1, 1);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set_uint8(x_292, sizeof(void*)*1, x_241);
if (lean_is_scalar(x_289)) {
 x_293 = lean_alloc_ctor(0, 4, 0);
} else {
 x_293 = x_289;
}
lean_ctor_set(x_293, 0, x_286);
lean_ctor_set(x_293, 1, x_287);
lean_ctor_set(x_293, 2, x_288);
lean_ctor_set(x_293, 3, x_292);
x_294 = lean_st_ref_set(x_6, x_293, x_285);
lean_dec(x_6);
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
lean_ctor_set(x_297, 0, x_278);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_298 = lean_ctor_get(x_5, 3);
lean_inc(x_298);
x_299 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(x_6, x_236);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_302 = l_Lean_Meta_processPostponed_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_301);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_306 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_300, x_305, x_298, x_3, x_4, x_5, x_6, x_304);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_308 = x_306;
} else {
 lean_dec_ref(x_306);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_303);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_310 = lean_ctor_get(x_302, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_302, 1);
lean_inc(x_311);
lean_dec(x_302);
x_312 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_313 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_300, x_312, x_298, x_3, x_4, x_5, x_6, x_311);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_315 = x_313;
} else {
 lean_dec_ref(x_313);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_315;
 lean_ctor_set_tag(x_316, 1);
}
lean_ctor_set(x_316, 0, x_310);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
}
}
}
else
{
uint8_t x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_330 = 1;
x_331 = lean_box(x_330);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_232);
return x_332;
}
}
}
}
lean_object* l_Lean_Meta_processPostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_processPostponed(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_Meta_checkpointDefEq_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Meta_checkpointDefEq_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_checkpointDefEq_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_checkpointDefEq(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_19 = l_Lean_Meta_getResetPostponed(x_3, x_4, x_5, x_6, x_10);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_20);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = 0;
x_30 = lean_box(x_29);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_36 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_37 = l_Lean_Meta_processPostponed(x_2, x_36, x_3, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_20);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_40);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(x_36);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(x_36);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_9);
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_dec(x_37);
x_49 = l_Lean_Meta_getPostponed___rarg(x_4, x_5, x_6, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Std_PersistentArray_append___rarg(x_20, x_50);
lean_dec(x_50);
x_53 = l_Lean_Meta_setPostponed(x_52, x_3, x_4, x_5, x_6, x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
x_56 = 1;
x_57 = lean_box(x_56);
lean_ctor_set(x_53, 0, x_57);
return x_53;
}
else
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = 1;
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_20);
x_62 = lean_ctor_get(x_37, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_37, 1);
lean_inc(x_63);
lean_dec(x_37);
x_11 = x_62;
x_12 = x_63;
goto block_18;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_20);
x_64 = lean_ctor_get(x_22, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_dec(x_22);
x_11 = x_64;
x_12 = x_65;
goto block_18;
}
block_18:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Meta_checkpointDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_checkpointDefEq(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = l_Lean_Meta_saveState___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_20 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_isLevelDefEqAux(x_1, x_2, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
x_37 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Meta_processPostponed(x_3, x_37, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_21);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(x_37);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(x_37);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_10);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_dec(x_38);
x_50 = l_Lean_Meta_getPostponed___rarg(x_5, x_6, x_7, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Std_PersistentArray_append___rarg(x_21, x_51);
lean_dec(x_51);
x_54 = l_Lean_Meta_setPostponed(x_53, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_21);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
x_12 = x_63;
x_13 = x_64;
goto block_19;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_21);
x_65 = lean_ctor_get(x_23, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_dec(x_23);
x_12 = x_65;
x_13 = x_66;
goto block_19;
}
block_19:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = l_Lean_Meta_saveState___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_20 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_isLevelDefEqAux(x_1, x_2, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
x_37 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Meta_processPostponed(x_3, x_37, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_21);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(x_37);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(x_37);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_10);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_dec(x_38);
x_50 = l_Lean_Meta_getPostponed___rarg(x_5, x_6, x_7, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Std_PersistentArray_append___rarg(x_21, x_51);
lean_dec(x_51);
x_54 = l_Lean_Meta_setPostponed(x_53, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_21);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
x_12 = x_63;
x_13 = x_64;
goto block_19;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_21);
x_65 = lean_ctor_get(x_23, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_dec(x_23);
x_12 = x_65;
x_13 = x_66;
goto block_19;
}
block_19:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ... ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEq___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failure");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEq___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEq___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("success");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEq___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_isLevelDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_17; lean_object* x_18; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_422 = lean_st_ref_get(x_6, x_7);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_423, 3);
lean_inc(x_424);
lean_dec(x_423);
x_425 = lean_ctor_get_uint8(x_424, sizeof(void*)*1);
lean_dec(x_424);
if (x_425 == 0)
{
lean_object* x_426; uint8_t x_427; 
x_426 = lean_ctor_get(x_422, 1);
lean_inc(x_426);
lean_dec(x_422);
x_427 = 0;
x_17 = x_427;
x_18 = x_426;
goto block_421;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_428 = lean_ctor_get(x_422, 1);
lean_inc(x_428);
lean_dec(x_422);
x_429 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_430 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_429, x_3, x_4, x_5, x_6, x_428);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec(x_430);
x_433 = lean_unbox(x_431);
lean_dec(x_431);
x_17 = x_433;
x_18 = x_432;
goto block_421;
}
block_16:
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
block_421:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_st_ref_get(x_6, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
lean_dec(x_21);
x_24 = lean_st_ref_take(x_6, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 3);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_83; lean_object* x_84; 
x_31 = 0;
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_31);
x_32 = lean_st_ref_set(x_6, x_25, x_27);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_83 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_84 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1, x_2, x_83, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_115 = lean_st_ref_get(x_6, x_86);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 3);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_ctor_get_uint8(x_117, sizeof(void*)*1);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_dec(x_115);
x_87 = x_31;
x_88 = x_119;
goto block_114;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_dec(x_115);
x_121 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_122 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_121, x_3, x_4, x_5, x_6, x_120);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_unbox(x_123);
lean_dec(x_123);
x_87 = x_125;
x_88 = x_124;
goto block_114;
}
block_114:
{
if (x_87 == 0)
{
uint8_t x_89; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_unbox(x_85);
lean_dec(x_85);
x_34 = x_89;
x_35 = x_88;
goto block_82;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_90 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_90, 0, x_1);
x_91 = l_Lean_KernelException_toMessageData___closed__15;
x_92 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_95, 0, x_2);
x_96 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Meta_isLevelDefEq___closed__2;
x_98 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_unbox(x_85);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_100 = l_Lean_Meta_isLevelDefEq___closed__4;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_91);
x_103 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_104 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_103, x_102, x_3, x_4, x_5, x_6, x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_unbox(x_85);
lean_dec(x_85);
x_34 = x_106;
x_35 = x_105;
goto block_82;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_107 = l_Lean_Meta_isLevelDefEq___closed__6;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_98);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_91);
x_110 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_111 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_110, x_109, x_3, x_4, x_5, x_6, x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_unbox(x_85);
lean_dec(x_85);
x_34 = x_113;
x_35 = x_112;
goto block_82;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_ctor_get(x_84, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_84, 1);
lean_inc(x_127);
lean_dec(x_84);
x_128 = lean_st_ref_get(x_6, x_127);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_st_ref_take(x_6, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = !lean_is_exclusive(x_131);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_131, 3);
lean_dec(x_135);
x_136 = !lean_is_exclusive(x_132);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_23);
x_137 = lean_st_ref_set(x_6, x_131, x_133);
lean_dec(x_6);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_137, 0);
lean_dec(x_139);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 0, x_126);
return x_137;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_126);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_132, 0);
lean_inc(x_142);
lean_dec(x_132);
x_143 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*1, x_23);
lean_ctor_set(x_131, 3, x_143);
x_144 = lean_st_ref_set(x_6, x_131, x_133);
lean_dec(x_6);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
 lean_ctor_set_tag(x_147, 1);
}
lean_ctor_set(x_147, 0, x_126);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_148 = lean_ctor_get(x_131, 0);
x_149 = lean_ctor_get(x_131, 1);
x_150 = lean_ctor_get(x_131, 2);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_131);
x_151 = lean_ctor_get(x_132, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_152 = x_132;
} else {
 lean_dec_ref(x_132);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 1, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_23);
x_154 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_149);
lean_ctor_set(x_154, 2, x_150);
lean_ctor_set(x_154, 3, x_153);
x_155 = lean_st_ref_set(x_6, x_154, x_133);
lean_dec(x_6);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
 lean_ctor_set_tag(x_158, 1);
}
lean_ctor_set(x_158, 0, x_126);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
block_82:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_36 = lean_st_ref_get(x_6, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 3);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
lean_dec(x_39);
x_41 = lean_st_ref_take(x_6, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 3);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_23);
x_48 = lean_st_ref_set(x_6, x_42, x_44);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(x_34);
x_52 = lean_box(x_40);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_48, 0, x_53);
x_8 = x_48;
goto block_16;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_box(x_34);
x_56 = lean_box(x_40);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
x_8 = x_58;
goto block_16;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_43, 0);
lean_inc(x_59);
lean_dec(x_43);
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_23);
lean_ctor_set(x_42, 3, x_60);
x_61 = lean_st_ref_set(x_6, x_42, x_44);
lean_dec(x_6);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(x_34);
x_65 = lean_box(x_40);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
x_8 = x_67;
goto block_16;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_68 = lean_ctor_get(x_42, 0);
x_69 = lean_ctor_get(x_42, 1);
x_70 = lean_ctor_get(x_42, 2);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_42);
x_71 = lean_ctor_get(x_43, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_72 = x_43;
} else {
 lean_dec_ref(x_43);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 1, 1);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_23);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_69);
lean_ctor_set(x_74, 2, x_70);
lean_ctor_set(x_74, 3, x_73);
x_75 = lean_st_ref_set(x_6, x_74, x_44);
lean_dec(x_6);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_box(x_34);
x_79 = lean_box(x_40);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
if (lean_is_scalar(x_77)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_77;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
x_8 = x_81;
goto block_16;
}
}
}
else
{
lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; uint8_t x_191; lean_object* x_192; 
x_159 = lean_ctor_get(x_26, 0);
lean_inc(x_159);
lean_dec(x_26);
x_160 = 0;
x_161 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set_uint8(x_161, sizeof(void*)*1, x_160);
lean_ctor_set(x_25, 3, x_161);
x_162 = lean_st_ref_set(x_6, x_25, x_27);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_191 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_192 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1, x_2, x_191, x_3, x_4, x_5, x_6, x_163);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_223 = lean_st_ref_get(x_6, x_194);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_224, 3);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_ctor_get_uint8(x_225, sizeof(void*)*1);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
lean_dec(x_223);
x_195 = x_160;
x_196 = x_227;
goto block_222;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
lean_dec(x_223);
x_229 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_230 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_229, x_3, x_4, x_5, x_6, x_228);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_unbox(x_231);
lean_dec(x_231);
x_195 = x_233;
x_196 = x_232;
goto block_222;
}
block_222:
{
if (x_195 == 0)
{
uint8_t x_197; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = lean_unbox(x_193);
lean_dec(x_193);
x_164 = x_197;
x_165 = x_196;
goto block_190;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_198 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_198, 0, x_1);
x_199 = l_Lean_KernelException_toMessageData___closed__15;
x_200 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
x_201 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_202 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_203, 0, x_2);
x_204 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Lean_Meta_isLevelDefEq___closed__2;
x_206 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_unbox(x_193);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_208 = l_Lean_Meta_isLevelDefEq___closed__4;
x_209 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_199);
x_211 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_212 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_211, x_210, x_3, x_4, x_5, x_6, x_196);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_unbox(x_193);
lean_dec(x_193);
x_164 = x_214;
x_165 = x_213;
goto block_190;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_215 = l_Lean_Meta_isLevelDefEq___closed__6;
x_216 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_216, 0, x_206);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_199);
x_218 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_219 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_218, x_217, x_3, x_4, x_5, x_6, x_196);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = lean_unbox(x_193);
lean_dec(x_193);
x_164 = x_221;
x_165 = x_220;
goto block_190;
}
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_234 = lean_ctor_get(x_192, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_192, 1);
lean_inc(x_235);
lean_dec(x_192);
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
lean_ctor_set_uint8(x_248, sizeof(void*)*1, x_23);
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
return x_253;
}
block_190:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_166 = lean_st_ref_get(x_6, x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_ctor_get(x_167, 3);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get_uint8(x_169, sizeof(void*)*1);
lean_dec(x_169);
x_171 = lean_st_ref_take(x_6, x_168);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_172, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_172, 2);
lean_inc(x_177);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 x_178 = x_172;
} else {
 lean_dec_ref(x_172);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_173, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_180 = x_173;
} else {
 lean_dec_ref(x_173);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 1, 1);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_178)) {
 x_182 = lean_alloc_ctor(0, 4, 0);
} else {
 x_182 = x_178;
}
lean_ctor_set(x_182, 0, x_175);
lean_ctor_set(x_182, 1, x_176);
lean_ctor_set(x_182, 2, x_177);
lean_ctor_set(x_182, 3, x_181);
x_183 = lean_st_ref_set(x_6, x_182, x_174);
lean_dec(x_6);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
x_186 = lean_box(x_164);
x_187 = lean_box(x_170);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
if (lean_is_scalar(x_185)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_185;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_184);
x_8 = x_189;
goto block_16;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; lean_object* x_265; uint8_t x_291; lean_object* x_292; 
x_254 = lean_ctor_get(x_25, 0);
x_255 = lean_ctor_get(x_25, 1);
x_256 = lean_ctor_get(x_25, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_25);
x_257 = lean_ctor_get(x_26, 0);
lean_inc(x_257);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_258 = x_26;
} else {
 lean_dec_ref(x_26);
 x_258 = lean_box(0);
}
x_259 = 0;
if (lean_is_scalar(x_258)) {
 x_260 = lean_alloc_ctor(0, 1, 1);
} else {
 x_260 = x_258;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set_uint8(x_260, sizeof(void*)*1, x_259);
x_261 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_261, 0, x_254);
lean_ctor_set(x_261, 1, x_255);
lean_ctor_set(x_261, 2, x_256);
lean_ctor_set(x_261, 3, x_260);
x_262 = lean_st_ref_set(x_6, x_261, x_27);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_291 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_292 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1, x_2, x_291, x_3, x_4, x_5, x_6, x_263);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_323 = lean_st_ref_get(x_6, x_294);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_324, 3);
lean_inc(x_325);
lean_dec(x_324);
x_326 = lean_ctor_get_uint8(x_325, sizeof(void*)*1);
lean_dec(x_325);
if (x_326 == 0)
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
lean_dec(x_323);
x_295 = x_259;
x_296 = x_327;
goto block_322;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_328 = lean_ctor_get(x_323, 1);
lean_inc(x_328);
lean_dec(x_323);
x_329 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_330 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_329, x_3, x_4, x_5, x_6, x_328);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_unbox(x_331);
lean_dec(x_331);
x_295 = x_333;
x_296 = x_332;
goto block_322;
}
block_322:
{
if (x_295 == 0)
{
uint8_t x_297; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = lean_unbox(x_293);
lean_dec(x_293);
x_264 = x_297;
x_265 = x_296;
goto block_290;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_298 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_298, 0, x_1);
x_299 = l_Lean_KernelException_toMessageData___closed__15;
x_300 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_298);
x_301 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_302 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_303, 0, x_2);
x_304 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_Meta_isLevelDefEq___closed__2;
x_306 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_unbox(x_293);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_308 = l_Lean_Meta_isLevelDefEq___closed__4;
x_309 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_299);
x_311 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_312 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_311, x_310, x_3, x_4, x_5, x_6, x_296);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
lean_dec(x_312);
x_314 = lean_unbox(x_293);
lean_dec(x_293);
x_264 = x_314;
x_265 = x_313;
goto block_290;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_315 = l_Lean_Meta_isLevelDefEq___closed__6;
x_316 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_316, 0, x_306);
lean_ctor_set(x_316, 1, x_315);
x_317 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_299);
x_318 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_319 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_318, x_317, x_3, x_4, x_5, x_6, x_296);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
lean_dec(x_319);
x_321 = lean_unbox(x_293);
lean_dec(x_293);
x_264 = x_321;
x_265 = x_320;
goto block_290;
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_334 = lean_ctor_get(x_292, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_292, 1);
lean_inc(x_335);
lean_dec(x_292);
x_336 = lean_st_ref_get(x_6, x_335);
x_337 = lean_ctor_get(x_336, 1);
lean_inc(x_337);
lean_dec(x_336);
x_338 = lean_st_ref_take(x_6, x_337);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_339, 3);
lean_inc(x_340);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
lean_dec(x_338);
x_342 = lean_ctor_get(x_339, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_339, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_339, 2);
lean_inc(x_344);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_345 = x_339;
} else {
 lean_dec_ref(x_339);
 x_345 = lean_box(0);
}
x_346 = lean_ctor_get(x_340, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 x_347 = x_340;
} else {
 lean_dec_ref(x_340);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(0, 1, 1);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set_uint8(x_348, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_345)) {
 x_349 = lean_alloc_ctor(0, 4, 0);
} else {
 x_349 = x_345;
}
lean_ctor_set(x_349, 0, x_342);
lean_ctor_set(x_349, 1, x_343);
lean_ctor_set(x_349, 2, x_344);
lean_ctor_set(x_349, 3, x_348);
x_350 = lean_st_ref_set(x_6, x_349, x_341);
lean_dec(x_6);
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
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
 lean_ctor_set_tag(x_353, 1);
}
lean_ctor_set(x_353, 0, x_334);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
block_290:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_266 = lean_st_ref_get(x_6, x_265);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_ctor_get(x_267, 3);
lean_inc(x_269);
lean_dec(x_267);
x_270 = lean_ctor_get_uint8(x_269, sizeof(void*)*1);
lean_dec(x_269);
x_271 = lean_st_ref_take(x_6, x_268);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_272, 3);
lean_inc(x_273);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
lean_dec(x_271);
x_275 = lean_ctor_get(x_272, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_272, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_272, 2);
lean_inc(x_277);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 x_278 = x_272;
} else {
 lean_dec_ref(x_272);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_273, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_280 = x_273;
} else {
 lean_dec_ref(x_273);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(0, 1, 1);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set_uint8(x_281, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_278)) {
 x_282 = lean_alloc_ctor(0, 4, 0);
} else {
 x_282 = x_278;
}
lean_ctor_set(x_282, 0, x_275);
lean_ctor_set(x_282, 1, x_276);
lean_ctor_set(x_282, 2, x_277);
lean_ctor_set(x_282, 3, x_281);
x_283 = lean_st_ref_set(x_6, x_282, x_274);
lean_dec(x_6);
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_285 = x_283;
} else {
 lean_dec_ref(x_283);
 x_285 = lean_box(0);
}
x_286 = lean_box(x_264);
x_287 = lean_box(x_270);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
if (lean_is_scalar(x_285)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_285;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_284);
x_8 = x_289;
goto block_16;
}
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; uint8_t x_369; lean_object* x_370; 
x_354 = lean_ctor_get(x_5, 3);
lean_inc(x_354);
x_355 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(x_6, x_18);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_369 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_370 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__2(x_1, x_2, x_369, x_3, x_4, x_5, x_6, x_357);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_401 = lean_st_ref_get(x_6, x_372);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_402, 3);
lean_inc(x_403);
lean_dec(x_402);
x_404 = lean_ctor_get_uint8(x_403, sizeof(void*)*1);
lean_dec(x_403);
if (x_404 == 0)
{
lean_object* x_405; uint8_t x_406; 
x_405 = lean_ctor_get(x_401, 1);
lean_inc(x_405);
lean_dec(x_401);
x_406 = 0;
x_373 = x_406;
x_374 = x_405;
goto block_400;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_407 = lean_ctor_get(x_401, 1);
lean_inc(x_407);
lean_dec(x_401);
x_408 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_409 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_408, x_3, x_4, x_5, x_6, x_407);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_unbox(x_410);
lean_dec(x_410);
x_373 = x_412;
x_374 = x_411;
goto block_400;
}
block_400:
{
if (x_373 == 0)
{
uint8_t x_375; 
lean_dec(x_2);
lean_dec(x_1);
x_375 = lean_unbox(x_371);
lean_dec(x_371);
x_358 = x_375;
x_359 = x_374;
goto block_368;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_376 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_376, 0, x_1);
x_377 = l_Lean_KernelException_toMessageData___closed__15;
x_378 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
x_379 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_380 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
x_381 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_381, 0, x_2);
x_382 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
x_383 = l_Lean_Meta_isLevelDefEq___closed__2;
x_384 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
x_385 = lean_unbox(x_371);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_386 = l_Lean_Meta_isLevelDefEq___closed__4;
x_387 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_377);
x_389 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_390 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_389, x_388, x_3, x_4, x_5, x_6, x_374);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_392 = lean_unbox(x_371);
lean_dec(x_371);
x_358 = x_392;
x_359 = x_391;
goto block_368;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_393 = l_Lean_Meta_isLevelDefEq___closed__6;
x_394 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_394, 0, x_384);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_377);
x_396 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_397 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_396, x_395, x_3, x_4, x_5, x_6, x_374);
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
lean_dec(x_397);
x_399 = lean_unbox(x_371);
lean_dec(x_371);
x_358 = x_399;
x_359 = x_398;
goto block_368;
}
}
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
lean_dec(x_2);
lean_dec(x_1);
x_413 = lean_ctor_get(x_370, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_370, 1);
lean_inc(x_414);
lean_dec(x_370);
x_415 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_416 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_356, x_415, x_354, x_3, x_4, x_5, x_6, x_414);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_417 = !lean_is_exclusive(x_416);
if (x_417 == 0)
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_416, 0);
lean_dec(x_418);
lean_ctor_set_tag(x_416, 1);
lean_ctor_set(x_416, 0, x_413);
return x_416;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
lean_dec(x_416);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_413);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
block_368:
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_360 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_361 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_356, x_360, x_354, x_3, x_4, x_5, x_6, x_359);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_362 = !lean_is_exclusive(x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_361, 0);
lean_dec(x_363);
x_364 = lean_box(x_358);
lean_ctor_set(x_361, 0, x_364);
return x_361;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_361, 1);
lean_inc(x_365);
lean_dec(x_361);
x_366 = lean_box(x_358);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_365);
return x_367;
}
}
}
}
}
}
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = l_Lean_Meta_saveState___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_20 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_isExprDefEqAux(x_1, x_2, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
x_37 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Meta_processPostponed(x_3, x_37, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_21);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(x_37);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(x_37);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_10);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_dec(x_38);
x_50 = l_Lean_Meta_getPostponed___rarg(x_5, x_6, x_7, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Std_PersistentArray_append___rarg(x_21, x_51);
lean_dec(x_51);
x_54 = l_Lean_Meta_setPostponed(x_53, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_21);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
x_12 = x_63;
x_13 = x_64;
goto block_19;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_21);
x_65 = lean_ctor_get(x_23, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_dec(x_23);
x_12 = x_65;
x_13 = x_66;
goto block_19;
}
block_19:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = l_Lean_Meta_saveState___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_20 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_isExprDefEqAux(x_1, x_2, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
x_37 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Meta_processPostponed(x_3, x_37, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_21);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(x_37);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(x_37);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_10);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_dec(x_38);
x_50 = l_Lean_Meta_getPostponed___rarg(x_5, x_6, x_7, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Std_PersistentArray_append___rarg(x_21, x_51);
lean_dec(x_51);
x_54 = l_Lean_Meta_setPostponed(x_53, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_21);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
x_12 = x_63;
x_13 = x_64;
goto block_19;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_21);
x_65 = lean_ctor_get(x_23, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_dec(x_23);
x_12 = x_65;
x_13 = x_66;
goto block_19;
}
block_19:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Meta_isExprDefEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isDefEq");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isExprDefEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1037____closed__2;
x_2 = l_Lean_Meta_isExprDefEq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_isExprDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_17; lean_object* x_18; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; 
x_517 = lean_st_ref_get(x_6, x_7);
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_518, 3);
lean_inc(x_519);
lean_dec(x_518);
x_520 = lean_ctor_get_uint8(x_519, sizeof(void*)*1);
lean_dec(x_519);
if (x_520 == 0)
{
lean_object* x_521; uint8_t x_522; 
x_521 = lean_ctor_get(x_517, 1);
lean_inc(x_521);
lean_dec(x_517);
x_522 = 0;
x_17 = x_522;
x_18 = x_521;
goto block_516;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; uint8_t x_528; 
x_523 = lean_ctor_get(x_517, 1);
lean_inc(x_523);
lean_dec(x_517);
x_524 = l_Lean_Meta_isExprDefEq___closed__2;
x_525 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_524, x_3, x_4, x_5, x_6, x_523);
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
lean_dec(x_525);
x_528 = lean_unbox(x_526);
lean_dec(x_526);
x_17 = x_528;
x_18 = x_527;
goto block_516;
}
block_16:
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
block_516:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_st_ref_get(x_6, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
lean_dec(x_21);
x_24 = lean_st_ref_take(x_6, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 3);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_83; 
x_31 = 0;
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_31);
x_32 = lean_st_ref_set(x_6, x_25, x_27);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_83 = !lean_is_exclusive(x_3);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_84 = lean_ctor_get(x_3, 1);
x_85 = lean_ctor_get(x_3, 2);
x_86 = lean_ctor_get(x_3, 3);
lean_dec(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_2);
lean_inc(x_1);
x_87 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_2);
lean_ctor_set(x_87, 2, x_84);
lean_ctor_set(x_87, 3, x_85);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_3, 3, x_88);
x_89 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_90 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(x_1, x_2, x_89, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_121 = lean_st_ref_get(x_6, x_92);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_122, 3);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_ctor_get_uint8(x_123, sizeof(void*)*1);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_121, 1);
lean_inc(x_125);
lean_dec(x_121);
x_93 = x_31;
x_94 = x_125;
goto block_120;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_dec(x_121);
x_127 = l_Lean_Meta_isExprDefEq___closed__2;
x_128 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_127, x_3, x_4, x_5, x_6, x_126);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_unbox(x_129);
lean_dec(x_129);
x_93 = x_131;
x_94 = x_130;
goto block_120;
}
block_120:
{
if (x_93 == 0)
{
uint8_t x_95; 
lean_dec(x_3);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_unbox(x_91);
lean_dec(x_91);
x_34 = x_95;
x_35 = x_94;
goto block_82;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_1);
x_97 = l_Lean_KernelException_toMessageData___closed__15;
x_98 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_2);
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Meta_isLevelDefEq___closed__2;
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_unbox(x_91);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_106 = l_Lean_Meta_isLevelDefEq___closed__4;
x_107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_97);
x_109 = l_Lean_Meta_isExprDefEq___closed__2;
x_110 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_109, x_108, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_unbox(x_91);
lean_dec(x_91);
x_34 = x_112;
x_35 = x_111;
goto block_82;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_113 = l_Lean_Meta_isLevelDefEq___closed__6;
x_114 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_97);
x_116 = l_Lean_Meta_isExprDefEq___closed__2;
x_117 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_116, x_115, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_unbox(x_91);
lean_dec(x_91);
x_34 = x_119;
x_35 = x_118;
goto block_82;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
lean_dec(x_3);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_132 = lean_ctor_get(x_90, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_90, 1);
lean_inc(x_133);
lean_dec(x_90);
x_134 = lean_st_ref_get(x_6, x_133);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_st_ref_take(x_6, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = !lean_is_exclusive(x_137);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_137, 3);
lean_dec(x_141);
x_142 = !lean_is_exclusive(x_138);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
lean_ctor_set_uint8(x_138, sizeof(void*)*1, x_23);
x_143 = lean_st_ref_set(x_6, x_137, x_139);
lean_dec(x_6);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_143, 0);
lean_dec(x_145);
lean_ctor_set_tag(x_143, 1);
lean_ctor_set(x_143, 0, x_132);
return x_143;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_132);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_138, 0);
lean_inc(x_148);
lean_dec(x_138);
x_149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_23);
lean_ctor_set(x_137, 3, x_149);
x_150 = lean_st_ref_set(x_6, x_137, x_139);
lean_dec(x_6);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
 lean_ctor_set_tag(x_153, 1);
}
lean_ctor_set(x_153, 0, x_132);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_154 = lean_ctor_get(x_137, 0);
x_155 = lean_ctor_get(x_137, 1);
x_156 = lean_ctor_get(x_137, 2);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_137);
x_157 = lean_ctor_get(x_138, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_158 = x_138;
} else {
 lean_dec_ref(x_138);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(0, 1, 1);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_23);
x_160 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_155);
lean_ctor_set(x_160, 2, x_156);
lean_ctor_set(x_160, 3, x_159);
x_161 = lean_st_ref_set(x_6, x_160, x_139);
lean_dec(x_6);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
 lean_ctor_set_tag(x_164, 1);
}
lean_ctor_set(x_164, 0, x_132);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_3, 0);
x_166 = lean_ctor_get(x_3, 1);
x_167 = lean_ctor_get(x_3, 2);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_3);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_2);
lean_inc(x_1);
x_168 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_2);
lean_ctor_set(x_168, 2, x_166);
lean_ctor_set(x_168, 3, x_167);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_170, 0, x_165);
lean_ctor_set(x_170, 1, x_166);
lean_ctor_set(x_170, 2, x_167);
lean_ctor_set(x_170, 3, x_169);
x_171 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_170);
lean_inc(x_2);
lean_inc(x_1);
x_172 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(x_1, x_2, x_171, x_170, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_203 = lean_st_ref_get(x_6, x_174);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_204, 3);
lean_inc(x_205);
lean_dec(x_204);
x_206 = lean_ctor_get_uint8(x_205, sizeof(void*)*1);
lean_dec(x_205);
if (x_206 == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_203, 1);
lean_inc(x_207);
lean_dec(x_203);
x_175 = x_31;
x_176 = x_207;
goto block_202;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_208 = lean_ctor_get(x_203, 1);
lean_inc(x_208);
lean_dec(x_203);
x_209 = l_Lean_Meta_isExprDefEq___closed__2;
x_210 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_209, x_170, x_4, x_5, x_6, x_208);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = lean_unbox(x_211);
lean_dec(x_211);
x_175 = x_213;
x_176 = x_212;
goto block_202;
}
block_202:
{
if (x_175 == 0)
{
uint8_t x_177; 
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_unbox(x_173);
lean_dec(x_173);
x_34 = x_177;
x_35 = x_176;
goto block_82;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_178 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_178, 0, x_1);
x_179 = l_Lean_KernelException_toMessageData___closed__15;
x_180 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_182 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_183, 0, x_2);
x_184 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = l_Lean_Meta_isLevelDefEq___closed__2;
x_186 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_unbox(x_173);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_188 = l_Lean_Meta_isLevelDefEq___closed__4;
x_189 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_179);
x_191 = l_Lean_Meta_isExprDefEq___closed__2;
x_192 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_191, x_190, x_170, x_4, x_5, x_6, x_176);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_170);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_unbox(x_173);
lean_dec(x_173);
x_34 = x_194;
x_35 = x_193;
goto block_82;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_195 = l_Lean_Meta_isLevelDefEq___closed__6;
x_196 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_196, 0, x_186);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_179);
x_198 = l_Lean_Meta_isExprDefEq___closed__2;
x_199 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_198, x_197, x_170, x_4, x_5, x_6, x_176);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_170);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_201 = lean_unbox(x_173);
lean_dec(x_173);
x_34 = x_201;
x_35 = x_200;
goto block_82;
}
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_214 = lean_ctor_get(x_172, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_172, 1);
lean_inc(x_215);
lean_dec(x_172);
x_216 = lean_st_ref_get(x_6, x_215);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_st_ref_take(x_6, x_217);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_219, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = lean_ctor_get(x_219, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_219, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 2);
lean_inc(x_224);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 lean_ctor_release(x_219, 2);
 lean_ctor_release(x_219, 3);
 x_225 = x_219;
} else {
 lean_dec_ref(x_219);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_220, 0);
lean_inc(x_226);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_227 = x_220;
} else {
 lean_dec_ref(x_220);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(0, 1, 1);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set_uint8(x_228, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_225)) {
 x_229 = lean_alloc_ctor(0, 4, 0);
} else {
 x_229 = x_225;
}
lean_ctor_set(x_229, 0, x_222);
lean_ctor_set(x_229, 1, x_223);
lean_ctor_set(x_229, 2, x_224);
lean_ctor_set(x_229, 3, x_228);
x_230 = lean_st_ref_set(x_6, x_229, x_221);
lean_dec(x_6);
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
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
 lean_ctor_set_tag(x_233, 1);
}
lean_ctor_set(x_233, 0, x_214);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
block_82:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_36 = lean_st_ref_get(x_6, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 3);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
lean_dec(x_39);
x_41 = lean_st_ref_take(x_6, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 3);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_23);
x_48 = lean_st_ref_set(x_6, x_42, x_44);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(x_34);
x_52 = lean_box(x_40);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_48, 0, x_53);
x_8 = x_48;
goto block_16;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_box(x_34);
x_56 = lean_box(x_40);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
x_8 = x_58;
goto block_16;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_43, 0);
lean_inc(x_59);
lean_dec(x_43);
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_23);
lean_ctor_set(x_42, 3, x_60);
x_61 = lean_st_ref_set(x_6, x_42, x_44);
lean_dec(x_6);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(x_34);
x_65 = lean_box(x_40);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
x_8 = x_67;
goto block_16;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_68 = lean_ctor_get(x_42, 0);
x_69 = lean_ctor_get(x_42, 1);
x_70 = lean_ctor_get(x_42, 2);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_42);
x_71 = lean_ctor_get(x_43, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_72 = x_43;
} else {
 lean_dec_ref(x_43);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 1, 1);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_23);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_69);
lean_ctor_set(x_74, 2, x_70);
lean_ctor_set(x_74, 3, x_73);
x_75 = lean_st_ref_set(x_6, x_74, x_44);
lean_dec(x_6);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_box(x_34);
x_79 = lean_box(x_40);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
if (lean_is_scalar(x_77)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_77;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
x_8 = x_81;
goto block_16;
}
}
}
else
{
lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; 
x_234 = lean_ctor_get(x_26, 0);
lean_inc(x_234);
lean_dec(x_26);
x_235 = 0;
x_236 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set_uint8(x_236, sizeof(void*)*1, x_235);
lean_ctor_set(x_25, 3, x_236);
x_237 = lean_st_ref_set(x_6, x_25, x_27);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_266 = lean_ctor_get(x_3, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_3, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_3, 2);
lean_inc(x_268);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_269 = x_3;
} else {
 lean_dec_ref(x_3);
 x_269 = lean_box(0);
}
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_2);
lean_inc(x_1);
x_270 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_270, 0, x_1);
lean_ctor_set(x_270, 1, x_2);
lean_ctor_set(x_270, 2, x_267);
lean_ctor_set(x_270, 3, x_268);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
if (lean_is_scalar(x_269)) {
 x_272 = lean_alloc_ctor(0, 4, 0);
} else {
 x_272 = x_269;
}
lean_ctor_set(x_272, 0, x_266);
lean_ctor_set(x_272, 1, x_267);
lean_ctor_set(x_272, 2, x_268);
lean_ctor_set(x_272, 3, x_271);
x_273 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_272);
lean_inc(x_2);
lean_inc(x_1);
x_274 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(x_1, x_2, x_273, x_272, x_4, x_5, x_6, x_238);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_305 = lean_st_ref_get(x_6, x_276);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_306, 3);
lean_inc(x_307);
lean_dec(x_306);
x_308 = lean_ctor_get_uint8(x_307, sizeof(void*)*1);
lean_dec(x_307);
if (x_308 == 0)
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_305, 1);
lean_inc(x_309);
lean_dec(x_305);
x_277 = x_235;
x_278 = x_309;
goto block_304;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_310 = lean_ctor_get(x_305, 1);
lean_inc(x_310);
lean_dec(x_305);
x_311 = l_Lean_Meta_isExprDefEq___closed__2;
x_312 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_311, x_272, x_4, x_5, x_6, x_310);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_unbox(x_313);
lean_dec(x_313);
x_277 = x_315;
x_278 = x_314;
goto block_304;
}
block_304:
{
if (x_277 == 0)
{
uint8_t x_279; 
lean_dec(x_272);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_279 = lean_unbox(x_275);
lean_dec(x_275);
x_239 = x_279;
x_240 = x_278;
goto block_265;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_280 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_280, 0, x_1);
x_281 = l_Lean_KernelException_toMessageData___closed__15;
x_282 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
x_283 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_284 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_285, 0, x_2);
x_286 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = l_Lean_Meta_isLevelDefEq___closed__2;
x_288 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_unbox(x_275);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_290 = l_Lean_Meta_isLevelDefEq___closed__4;
x_291 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_281);
x_293 = l_Lean_Meta_isExprDefEq___closed__2;
x_294 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_293, x_292, x_272, x_4, x_5, x_6, x_278);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_272);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_unbox(x_275);
lean_dec(x_275);
x_239 = x_296;
x_240 = x_295;
goto block_265;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_297 = l_Lean_Meta_isLevelDefEq___closed__6;
x_298 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_298, 0, x_288);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_281);
x_300 = l_Lean_Meta_isExprDefEq___closed__2;
x_301 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_300, x_299, x_272, x_4, x_5, x_6, x_278);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_272);
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
lean_dec(x_301);
x_303 = lean_unbox(x_275);
lean_dec(x_275);
x_239 = x_303;
x_240 = x_302;
goto block_265;
}
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_272);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_316 = lean_ctor_get(x_274, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_274, 1);
lean_inc(x_317);
lean_dec(x_274);
x_318 = lean_st_ref_get(x_6, x_317);
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
lean_dec(x_318);
x_320 = lean_st_ref_take(x_6, x_319);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_321, 3);
lean_inc(x_322);
x_323 = lean_ctor_get(x_320, 1);
lean_inc(x_323);
lean_dec(x_320);
x_324 = lean_ctor_get(x_321, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_321, 1);
lean_inc(x_325);
x_326 = lean_ctor_get(x_321, 2);
lean_inc(x_326);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 x_327 = x_321;
} else {
 lean_dec_ref(x_321);
 x_327 = lean_box(0);
}
x_328 = lean_ctor_get(x_322, 0);
lean_inc(x_328);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 x_329 = x_322;
} else {
 lean_dec_ref(x_322);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(0, 1, 1);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set_uint8(x_330, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_327)) {
 x_331 = lean_alloc_ctor(0, 4, 0);
} else {
 x_331 = x_327;
}
lean_ctor_set(x_331, 0, x_324);
lean_ctor_set(x_331, 1, x_325);
lean_ctor_set(x_331, 2, x_326);
lean_ctor_set(x_331, 3, x_330);
x_332 = lean_st_ref_set(x_6, x_331, x_323);
lean_dec(x_6);
x_333 = lean_ctor_get(x_332, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_334 = x_332;
} else {
 lean_dec_ref(x_332);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 2, 0);
} else {
 x_335 = x_334;
 lean_ctor_set_tag(x_335, 1);
}
lean_ctor_set(x_335, 0, x_316);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
block_265:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_241 = lean_st_ref_get(x_6, x_240);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_ctor_get(x_242, 3);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_ctor_get_uint8(x_244, sizeof(void*)*1);
lean_dec(x_244);
x_246 = lean_st_ref_take(x_6, x_243);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_247, 3);
lean_inc(x_248);
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_250 = lean_ctor_get(x_247, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_247, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_247, 2);
lean_inc(x_252);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 x_253 = x_247;
} else {
 lean_dec_ref(x_247);
 x_253 = lean_box(0);
}
x_254 = lean_ctor_get(x_248, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_255 = x_248;
} else {
 lean_dec_ref(x_248);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(0, 1, 1);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set_uint8(x_256, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_253)) {
 x_257 = lean_alloc_ctor(0, 4, 0);
} else {
 x_257 = x_253;
}
lean_ctor_set(x_257, 0, x_250);
lean_ctor_set(x_257, 1, x_251);
lean_ctor_set(x_257, 2, x_252);
lean_ctor_set(x_257, 3, x_256);
x_258 = lean_st_ref_set(x_6, x_257, x_249);
lean_dec(x_6);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_260 = x_258;
} else {
 lean_dec_ref(x_258);
 x_260 = lean_box(0);
}
x_261 = lean_box(x_239);
x_262 = lean_box(x_245);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
if (lean_is_scalar(x_260)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_260;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_259);
x_8 = x_264;
goto block_16;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; 
x_336 = lean_ctor_get(x_25, 0);
x_337 = lean_ctor_get(x_25, 1);
x_338 = lean_ctor_get(x_25, 2);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_25);
x_339 = lean_ctor_get(x_26, 0);
lean_inc(x_339);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_340 = x_26;
} else {
 lean_dec_ref(x_26);
 x_340 = lean_box(0);
}
x_341 = 0;
if (lean_is_scalar(x_340)) {
 x_342 = lean_alloc_ctor(0, 1, 1);
} else {
 x_342 = x_340;
}
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set_uint8(x_342, sizeof(void*)*1, x_341);
x_343 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_343, 0, x_336);
lean_ctor_set(x_343, 1, x_337);
lean_ctor_set(x_343, 2, x_338);
lean_ctor_set(x_343, 3, x_342);
x_344 = lean_st_ref_set(x_6, x_343, x_27);
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
lean_dec(x_344);
x_373 = lean_ctor_get(x_3, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_3, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_3, 2);
lean_inc(x_375);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_376 = x_3;
} else {
 lean_dec_ref(x_3);
 x_376 = lean_box(0);
}
lean_inc(x_375);
lean_inc(x_374);
lean_inc(x_2);
lean_inc(x_1);
x_377 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_377, 0, x_1);
lean_ctor_set(x_377, 1, x_2);
lean_ctor_set(x_377, 2, x_374);
lean_ctor_set(x_377, 3, x_375);
x_378 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_378, 0, x_377);
if (lean_is_scalar(x_376)) {
 x_379 = lean_alloc_ctor(0, 4, 0);
} else {
 x_379 = x_376;
}
lean_ctor_set(x_379, 0, x_373);
lean_ctor_set(x_379, 1, x_374);
lean_ctor_set(x_379, 2, x_375);
lean_ctor_set(x_379, 3, x_378);
x_380 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_379);
lean_inc(x_2);
lean_inc(x_1);
x_381 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(x_1, x_2, x_380, x_379, x_4, x_5, x_6, x_345);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_412 = lean_st_ref_get(x_6, x_383);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_413, 3);
lean_inc(x_414);
lean_dec(x_413);
x_415 = lean_ctor_get_uint8(x_414, sizeof(void*)*1);
lean_dec(x_414);
if (x_415 == 0)
{
lean_object* x_416; 
x_416 = lean_ctor_get(x_412, 1);
lean_inc(x_416);
lean_dec(x_412);
x_384 = x_341;
x_385 = x_416;
goto block_411;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_417 = lean_ctor_get(x_412, 1);
lean_inc(x_417);
lean_dec(x_412);
x_418 = l_Lean_Meta_isExprDefEq___closed__2;
x_419 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_418, x_379, x_4, x_5, x_6, x_417);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_422 = lean_unbox(x_420);
lean_dec(x_420);
x_384 = x_422;
x_385 = x_421;
goto block_411;
}
block_411:
{
if (x_384 == 0)
{
uint8_t x_386; 
lean_dec(x_379);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_386 = lean_unbox(x_382);
lean_dec(x_382);
x_346 = x_386;
x_347 = x_385;
goto block_372;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; 
x_387 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_387, 0, x_1);
x_388 = l_Lean_KernelException_toMessageData___closed__15;
x_389 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_387);
x_390 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_391 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
x_392 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_392, 0, x_2);
x_393 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
x_394 = l_Lean_Meta_isLevelDefEq___closed__2;
x_395 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
x_396 = lean_unbox(x_382);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
x_397 = l_Lean_Meta_isLevelDefEq___closed__4;
x_398 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_397);
x_399 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_388);
x_400 = l_Lean_Meta_isExprDefEq___closed__2;
x_401 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_400, x_399, x_379, x_4, x_5, x_6, x_385);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_379);
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
lean_dec(x_401);
x_403 = lean_unbox(x_382);
lean_dec(x_382);
x_346 = x_403;
x_347 = x_402;
goto block_372;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; 
x_404 = l_Lean_Meta_isLevelDefEq___closed__6;
x_405 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_405, 0, x_395);
lean_ctor_set(x_405, 1, x_404);
x_406 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_388);
x_407 = l_Lean_Meta_isExprDefEq___closed__2;
x_408 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_407, x_406, x_379, x_4, x_5, x_6, x_385);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_379);
x_409 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
lean_dec(x_408);
x_410 = lean_unbox(x_382);
lean_dec(x_382);
x_346 = x_410;
x_347 = x_409;
goto block_372;
}
}
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_379);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_423 = lean_ctor_get(x_381, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_381, 1);
lean_inc(x_424);
lean_dec(x_381);
x_425 = lean_st_ref_get(x_6, x_424);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
lean_dec(x_425);
x_427 = lean_st_ref_take(x_6, x_426);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_428, 3);
lean_inc(x_429);
x_430 = lean_ctor_get(x_427, 1);
lean_inc(x_430);
lean_dec(x_427);
x_431 = lean_ctor_get(x_428, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_428, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_428, 2);
lean_inc(x_433);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_434 = x_428;
} else {
 lean_dec_ref(x_428);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_429, 0);
lean_inc(x_435);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 x_436 = x_429;
} else {
 lean_dec_ref(x_429);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(0, 1, 1);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set_uint8(x_437, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_434)) {
 x_438 = lean_alloc_ctor(0, 4, 0);
} else {
 x_438 = x_434;
}
lean_ctor_set(x_438, 0, x_431);
lean_ctor_set(x_438, 1, x_432);
lean_ctor_set(x_438, 2, x_433);
lean_ctor_set(x_438, 3, x_437);
x_439 = lean_st_ref_set(x_6, x_438, x_430);
lean_dec(x_6);
x_440 = lean_ctor_get(x_439, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_441 = x_439;
} else {
 lean_dec_ref(x_439);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_441;
 lean_ctor_set_tag(x_442, 1);
}
lean_ctor_set(x_442, 0, x_423);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
block_372:
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_348 = lean_st_ref_get(x_6, x_347);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = lean_ctor_get(x_349, 3);
lean_inc(x_351);
lean_dec(x_349);
x_352 = lean_ctor_get_uint8(x_351, sizeof(void*)*1);
lean_dec(x_351);
x_353 = lean_st_ref_take(x_6, x_350);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_354, 3);
lean_inc(x_355);
x_356 = lean_ctor_get(x_353, 1);
lean_inc(x_356);
lean_dec(x_353);
x_357 = lean_ctor_get(x_354, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_354, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_354, 2);
lean_inc(x_359);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_360 = x_354;
} else {
 lean_dec_ref(x_354);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_355, 0);
lean_inc(x_361);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 x_362 = x_355;
} else {
 lean_dec_ref(x_355);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(0, 1, 1);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set_uint8(x_363, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_360)) {
 x_364 = lean_alloc_ctor(0, 4, 0);
} else {
 x_364 = x_360;
}
lean_ctor_set(x_364, 0, x_357);
lean_ctor_set(x_364, 1, x_358);
lean_ctor_set(x_364, 2, x_359);
lean_ctor_set(x_364, 3, x_363);
x_365 = lean_st_ref_set(x_6, x_364, x_356);
lean_dec(x_6);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_367 = x_365;
} else {
 lean_dec_ref(x_365);
 x_367 = lean_box(0);
}
x_368 = lean_box(x_346);
x_369 = lean_box(x_352);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
if (lean_is_scalar(x_367)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_367;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_366);
x_8 = x_371;
goto block_16;
}
}
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_443 = lean_ctor_get(x_5, 3);
lean_inc(x_443);
x_444 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(x_6, x_18);
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec(x_444);
x_458 = lean_ctor_get(x_3, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_3, 1);
lean_inc(x_459);
x_460 = lean_ctor_get(x_3, 2);
lean_inc(x_460);
lean_inc(x_460);
lean_inc(x_459);
lean_inc(x_2);
lean_inc(x_1);
x_461 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_461, 0, x_1);
lean_ctor_set(x_461, 1, x_2);
lean_ctor_set(x_461, 2, x_459);
lean_ctor_set(x_461, 3, x_460);
x_462 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_462, 0, x_461);
x_463 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_463, 0, x_458);
lean_ctor_set(x_463, 1, x_459);
lean_ctor_set(x_463, 2, x_460);
lean_ctor_set(x_463, 3, x_462);
x_464 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_463);
lean_inc(x_2);
lean_inc(x_1);
x_465 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__2(x_1, x_2, x_464, x_463, x_4, x_5, x_6, x_446);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; uint8_t x_468; lean_object* x_469; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_496 = lean_st_ref_get(x_6, x_467);
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_497, 3);
lean_inc(x_498);
lean_dec(x_497);
x_499 = lean_ctor_get_uint8(x_498, sizeof(void*)*1);
lean_dec(x_498);
if (x_499 == 0)
{
lean_object* x_500; uint8_t x_501; 
x_500 = lean_ctor_get(x_496, 1);
lean_inc(x_500);
lean_dec(x_496);
x_501 = 0;
x_468 = x_501;
x_469 = x_500;
goto block_495;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; 
x_502 = lean_ctor_get(x_496, 1);
lean_inc(x_502);
lean_dec(x_496);
x_503 = l_Lean_Meta_isExprDefEq___closed__2;
x_504 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_503, x_463, x_4, x_5, x_6, x_502);
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec(x_504);
x_507 = lean_unbox(x_505);
lean_dec(x_505);
x_468 = x_507;
x_469 = x_506;
goto block_495;
}
block_495:
{
if (x_468 == 0)
{
uint8_t x_470; 
lean_dec(x_463);
lean_dec(x_2);
lean_dec(x_1);
x_470 = lean_unbox(x_466);
lean_dec(x_466);
x_447 = x_470;
x_448 = x_469;
goto block_457;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; 
x_471 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_471, 0, x_1);
x_472 = l_Lean_KernelException_toMessageData___closed__15;
x_473 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_471);
x_474 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_475 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_475, 0, x_473);
lean_ctor_set(x_475, 1, x_474);
x_476 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_476, 0, x_2);
x_477 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
x_478 = l_Lean_Meta_isLevelDefEq___closed__2;
x_479 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
x_480 = lean_unbox(x_466);
if (x_480 == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; 
x_481 = l_Lean_Meta_isLevelDefEq___closed__4;
x_482 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_481);
x_483 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_472);
x_484 = l_Lean_Meta_isExprDefEq___closed__2;
x_485 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_484, x_483, x_463, x_4, x_5, x_6, x_469);
lean_dec(x_463);
x_486 = lean_ctor_get(x_485, 1);
lean_inc(x_486);
lean_dec(x_485);
x_487 = lean_unbox(x_466);
lean_dec(x_466);
x_447 = x_487;
x_448 = x_486;
goto block_457;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; 
x_488 = l_Lean_Meta_isLevelDefEq___closed__6;
x_489 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_489, 0, x_479);
lean_ctor_set(x_489, 1, x_488);
x_490 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_472);
x_491 = l_Lean_Meta_isExprDefEq___closed__2;
x_492 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_491, x_490, x_463, x_4, x_5, x_6, x_469);
lean_dec(x_463);
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
lean_dec(x_492);
x_494 = lean_unbox(x_466);
lean_dec(x_466);
x_447 = x_494;
x_448 = x_493;
goto block_457;
}
}
}
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; 
lean_dec(x_463);
lean_dec(x_2);
lean_dec(x_1);
x_508 = lean_ctor_get(x_465, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_465, 1);
lean_inc(x_509);
lean_dec(x_465);
x_510 = l_Lean_Meta_isExprDefEq___closed__2;
x_511 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_445, x_510, x_443, x_3, x_4, x_5, x_6, x_509);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_512 = !lean_is_exclusive(x_511);
if (x_512 == 0)
{
lean_object* x_513; 
x_513 = lean_ctor_get(x_511, 0);
lean_dec(x_513);
lean_ctor_set_tag(x_511, 1);
lean_ctor_set(x_511, 0, x_508);
return x_511;
}
else
{
lean_object* x_514; lean_object* x_515; 
x_514 = lean_ctor_get(x_511, 1);
lean_inc(x_514);
lean_dec(x_511);
x_515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_515, 0, x_508);
lean_ctor_set(x_515, 1, x_514);
return x_515;
}
}
block_457:
{
lean_object* x_449; lean_object* x_450; uint8_t x_451; 
x_449 = l_Lean_Meta_isExprDefEq___closed__2;
x_450 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_445, x_449, x_443, x_3, x_4, x_5, x_6, x_448);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_451 = !lean_is_exclusive(x_450);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; 
x_452 = lean_ctor_get(x_450, 0);
lean_dec(x_452);
x_453 = lean_box(x_447);
lean_ctor_set(x_450, 0, x_453);
return x_450;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_450, 1);
lean_inc(x_454);
lean_dec(x_450);
x_455 = lean_box(x_447);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_454);
return x_456;
}
}
}
}
}
}
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_isDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_isDefEqGuarded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isExprDefEqGuarded(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_isDefEqNoConstantApprox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_ctor_set_uint8(x_9, 0, x_11);
lean_ctor_set_uint8(x_9, 1, x_11);
lean_ctor_set_uint8(x_9, 2, x_11);
x_12 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
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
else
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get_uint8(x_9, 3);
x_22 = lean_ctor_get_uint8(x_9, 4);
x_23 = lean_ctor_get_uint8(x_9, 5);
x_24 = lean_ctor_get_uint8(x_9, 6);
x_25 = lean_ctor_get_uint8(x_9, 7);
x_26 = lean_ctor_get_uint8(x_9, 8);
lean_dec(x_9);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, 3, x_21);
lean_ctor_set_uint8(x_28, 4, x_22);
lean_ctor_set_uint8(x_28, 5, x_23);
lean_ctor_set_uint8(x_28, 6, x_24);
lean_ctor_set_uint8(x_28, 7, x_25);
lean_ctor_set_uint8(x_28, 8, x_26);
lean_ctor_set(x_3, 0, x_28);
x_29 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
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
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 1);
x_40 = lean_ctor_get(x_3, 2);
x_41 = lean_ctor_get(x_3, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
x_42 = lean_ctor_get_uint8(x_38, 3);
x_43 = lean_ctor_get_uint8(x_38, 4);
x_44 = lean_ctor_get_uint8(x_38, 5);
x_45 = lean_ctor_get_uint8(x_38, 6);
x_46 = lean_ctor_get_uint8(x_38, 7);
x_47 = lean_ctor_get_uint8(x_38, 8);
if (lean_is_exclusive(x_38)) {
 x_48 = x_38;
} else {
 lean_dec_ref(x_38);
 x_48 = lean_box(0);
}
x_49 = 1;
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 0, 9);
} else {
 x_50 = x_48;
}
lean_ctor_set_uint8(x_50, 0, x_49);
lean_ctor_set_uint8(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, 2, x_49);
lean_ctor_set_uint8(x_50, 3, x_42);
lean_ctor_set_uint8(x_50, 4, x_43);
lean_ctor_set_uint8(x_50, 5, x_44);
lean_ctor_set_uint8(x_50, 6, x_45);
lean_ctor_set_uint8(x_50, 7, x_46);
lean_ctor_set_uint8(x_50, 8, x_47);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_39);
lean_ctor_set(x_51, 2, x_40);
lean_ctor_set(x_51, 3, x_41);
x_52 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_51, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_LevelDefEq___hyg_2828_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_isLevelDefEqAux___closed__1;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_9 = l_Lean_registerTraceClass(x_8, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_CollectMVars(lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_InferType(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_LevelDefEq(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_decLevel___closed__1 = _init_l_Lean_Meta_decLevel___closed__1();
lean_mark_persistent(l_Lean_Meta_decLevel___closed__1);
l_Lean_Meta_decLevel___closed__2 = _init_l_Lean_Meta_decLevel___closed__2();
lean_mark_persistent(l_Lean_Meta_decLevel___closed__2);
l_Lean_Meta_decLevel___closed__3 = _init_l_Lean_Meta_decLevel___closed__3();
lean_mark_persistent(l_Lean_Meta_decLevel___closed__3);
l_Lean_Meta_decLevel___closed__4 = _init_l_Lean_Meta_decLevel___closed__4();
lean_mark_persistent(l_Lean_Meta_decLevel___closed__4);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5);
l_Lean_Meta_isLevelDefEqAux___closed__1 = _init_l_Lean_Meta_isLevelDefEqAux___closed__1();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAux___closed__1);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__1);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__2 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__2);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__3 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__3);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__4 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__4);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__5 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__5);
l_Lean_Meta_mkLevelStuckErrorMessage___closed__1 = _init_l_Lean_Meta_mkLevelStuckErrorMessage___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLevelStuckErrorMessage___closed__1);
l_Lean_Meta_mkLevelErrorMessage___closed__1 = _init_l_Lean_Meta_mkLevelErrorMessage___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLevelErrorMessage___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__1);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4);
l_Lean_Meta_processPostponed_loop___closed__1 = _init_l_Lean_Meta_processPostponed_loop___closed__1();
lean_mark_persistent(l_Lean_Meta_processPostponed_loop___closed__1);
l_Lean_Meta_processPostponed_loop___closed__2 = _init_l_Lean_Meta_processPostponed_loop___closed__2();
lean_mark_persistent(l_Lean_Meta_processPostponed_loop___closed__2);
l_Lean_Meta_processPostponed_loop___closed__3 = _init_l_Lean_Meta_processPostponed_loop___closed__3();
lean_mark_persistent(l_Lean_Meta_processPostponed_loop___closed__3);
l_Lean_Meta_processPostponed_loop___closed__4 = _init_l_Lean_Meta_processPostponed_loop___closed__4();
lean_mark_persistent(l_Lean_Meta_processPostponed_loop___closed__4);
l_Lean_Meta_processPostponed_loop___closed__5 = _init_l_Lean_Meta_processPostponed_loop___closed__5();
lean_mark_persistent(l_Lean_Meta_processPostponed_loop___closed__5);
l_Lean_Meta_processPostponed_loop___closed__6 = _init_l_Lean_Meta_processPostponed_loop___closed__6();
lean_mark_persistent(l_Lean_Meta_processPostponed_loop___closed__6);
l_Lean_Meta_isLevelDefEq___closed__1 = _init_l_Lean_Meta_isLevelDefEq___closed__1();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___closed__1);
l_Lean_Meta_isLevelDefEq___closed__2 = _init_l_Lean_Meta_isLevelDefEq___closed__2();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___closed__2);
l_Lean_Meta_isLevelDefEq___closed__3 = _init_l_Lean_Meta_isLevelDefEq___closed__3();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___closed__3);
l_Lean_Meta_isLevelDefEq___closed__4 = _init_l_Lean_Meta_isLevelDefEq___closed__4();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___closed__4);
l_Lean_Meta_isLevelDefEq___closed__5 = _init_l_Lean_Meta_isLevelDefEq___closed__5();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___closed__5);
l_Lean_Meta_isLevelDefEq___closed__6 = _init_l_Lean_Meta_isLevelDefEq___closed__6();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___closed__6);
l_Lean_Meta_isExprDefEq___closed__1 = _init_l_Lean_Meta_isExprDefEq___closed__1();
lean_mark_persistent(l_Lean_Meta_isExprDefEq___closed__1);
l_Lean_Meta_isExprDefEq___closed__2 = _init_l_Lean_Meta_isExprDefEq___closed__2();
lean_mark_persistent(l_Lean_Meta_isExprDefEq___closed__2);
res = l_Lean_Meta_initFn____x40_Lean_Meta_LevelDefEq___hyg_2828_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

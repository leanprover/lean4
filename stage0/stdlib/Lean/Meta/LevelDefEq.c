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
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__4;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed_loop___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__1;
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Level_collectMVars(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_processPostponed_loop___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__2;
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__8;
uint8_t l_USize_decEq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isExprDefEq___closed__2;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__9;
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed_loop___lambda__2(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__1;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace_addTraceOptions(lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_append___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_12_(uint8_t, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_isLevelDefEq___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_decLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isLevelDefEq___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isExprDefEq___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffsetAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5;
lean_object* l_Lean_Level_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
static lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_processPostponed_loop___closed__1;
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2;
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__5;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isListLevelDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4;
lean_object* l_Lean_Expr_setPPUniverses(lean_object*, uint8_t);
uint8_t l_Lean_Level_isParam(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__10(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MetavarContext_getLevelAssignment_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__9(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_any(lean_object*, lean_object*);
lean_object* lean_level_mk_max_simp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__7;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__6;
lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLevelErrorMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__11(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___boxed(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__10;
uint8_t l_Std_PersistentArray_isEmpty___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DecLevelContext_canAssignMVars___default;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3;
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__7;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__5;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevelMVarDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_mkLevelStuckErrorMessage___closed__1;
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isLevelDefEq___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLevelStuckErrorMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_decLevel___closed__1;
size_t lean_ptr_addr(lean_object*);
static lean_object* l_Lean_Meta_getResetPostponed___closed__3;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelSucc(lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_decLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed_loop(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_decLevel___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_processPostponed_loop___closed__3;
uint8_t l_Lean_MetavarContext_hasAssignableLevelMVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_toArray___rarg(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_decLevel___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__1;
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__5;
lean_object* l_Lean_Level_normalize(lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isLevelDefEqAux___lambda__2___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isMVar(lean_object*);
static lean_object* l_Lean_Meta_processPostponed_loop___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isLevelDefEq___closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_processPostponed_loop___closed__4;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__2;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
lean_object* l_Lean_Level_getLevelOffset(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqNoConstantApprox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isLevelDefEq___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_processPostponed_loop___closed__2;
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_decLevel___closed__3;
static lean_object* l_Lean_Meta_isLevelDefEq___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__5(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__2;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getResetPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getResetPostponed___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_LevelDefEq___hyg_3284_(lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLevelErrorMessage___closed__1;
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed_loop___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getResetPostponed___closed__2;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__3;
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__2;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__2;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__5;
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isMax(lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static uint8_t _init_l_Lean_Meta_DecLevelContext_canAssignMVars___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_traceMsg");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_addTrace_addTraceOptions(x_11);
x_14 = lean_st_ref_take(x_7, x_12);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__2;
x_23 = l_Lean_Name_append(x_1, x_22);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__6;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_13);
x_30 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_9);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Std_PersistentArray_push___rarg(x_21, x_33);
lean_ctor_set(x_16, 0, x_34);
x_35 = lean_st_ref_set(x_7, x_15, x_17);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_42 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_43 = lean_ctor_get(x_16, 0);
lean_inc(x_43);
lean_dec(x_16);
x_44 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__2;
x_45 = l_Lean_Name_append(x_1, x_44);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_1);
x_47 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__4;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__6;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_13);
x_52 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_53);
lean_inc(x_9);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_9);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Std_PersistentArray_push___rarg(x_43, x_55);
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_42);
lean_ctor_set(x_15, 3, x_57);
x_58 = lean_st_ref_set(x_7, x_15, x_17);
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
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_63 = lean_ctor_get(x_15, 0);
x_64 = lean_ctor_get(x_15, 1);
x_65 = lean_ctor_get(x_15, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_15);
x_66 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_67 = lean_ctor_get(x_16, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_68 = x_16;
} else {
 lean_dec_ref(x_16);
 x_68 = lean_box(0);
}
x_69 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__2;
x_70 = l_Lean_Name_append(x_1, x_69);
x_71 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_71, 0, x_1);
x_72 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__4;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__6;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_13);
x_77 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_79, 0, x_70);
lean_ctor_set(x_79, 1, x_78);
lean_inc(x_9);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_9);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Std_PersistentArray_push___rarg(x_67, x_80);
if (lean_is_scalar(x_68)) {
 x_82 = lean_alloc_ctor(0, 1, 1);
} else {
 x_82 = x_68;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_66);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_63);
lean_ctor_set(x_83, 1, x_64);
lean_ctor_set(x_83, 2, x_65);
lean_ctor_set(x_83, 3, x_82);
x_84 = lean_st_ref_set(x_7, x_83, x_17);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_10 = l_Lean_mkLevelSucc(x_1);
x_11 = l_Lean_Meta_assignLevelMVar(x_2, x_10, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isLevelDefEq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__2;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("step");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("decAux?, ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" := ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(x_11, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(x_12, x_13, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_23);
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
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_level_mk_max_simp(x_23, x_35);
lean_ctor_set(x_25, 0, x_36);
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_level_mk_max_simp(x_23, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_24, 0, x_39);
return x_24;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_dec(x_24);
x_41 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_42 = x_25;
} else {
 lean_dec_ref(x_25);
 x_42 = lean_box(0);
}
x_43 = lean_level_mk_max_simp(x_23, x_41);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_23);
x_46 = !lean_is_exclusive(x_24);
if (x_46 == 0)
{
return x_24;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_24, 0);
x_48 = lean_ctor_get(x_24, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_24);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
return x_14;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_14, 0);
x_52 = lean_ctor_get(x_14, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_14);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
case 3:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_dec(x_1);
x_56 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_57 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(x_54, x_56, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
lean_dec(x_55);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
lean_dec(x_57);
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
lean_dec(x_58);
x_67 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(x_55, x_56, x_3, x_4, x_5, x_6, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
lean_dec(x_66);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
x_71 = lean_box(0);
lean_ctor_set(x_67, 0, x_71);
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_67);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_67, 0);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_68, 0);
x_79 = lean_level_mk_max_simp(x_66, x_78);
lean_ctor_set(x_68, 0, x_79);
return x_67;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_68, 0);
lean_inc(x_80);
lean_dec(x_68);
x_81 = lean_level_mk_max_simp(x_66, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_67, 0, x_82);
return x_67;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_67, 1);
lean_inc(x_83);
lean_dec(x_67);
x_84 = lean_ctor_get(x_68, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_85 = x_68;
} else {
 lean_dec_ref(x_68);
 x_85 = lean_box(0);
}
x_86 = lean_level_mk_max_simp(x_66, x_84);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_83);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_66);
x_89 = !lean_is_exclusive(x_67);
if (x_89 == 0)
{
return x_67;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_67, 0);
x_91 = lean_ctor_get(x_67, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_67);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_55);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_57);
if (x_93 == 0)
{
return x_57;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_57, 0);
x_95 = lean_ctor_get(x_57, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_57);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
case 5:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_1, 0);
lean_inc(x_97);
lean_dec(x_1);
x_98 = lean_st_ref_get(x_6, x_7);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_st_ref_get(x_4, x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_97);
x_104 = l_Lean_MetavarContext_getLevelAssignment_x3f(x_103, x_97);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
lean_inc(x_97);
x_105 = l_Lean_Meta_isReadOnlyLevelMVar(x_97, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
if (x_2 == 0)
{
uint8_t x_108; 
lean_dec(x_97);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
x_110 = lean_box(0);
lean_ctor_set(x_105, 0, x_110);
return x_105;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_dec(x_105);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_114 = lean_ctor_get(x_105, 1);
lean_inc(x_114);
lean_dec(x_105);
x_115 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
x_139 = lean_st_ref_get(x_6, x_117);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 3);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = 0;
x_119 = x_144;
x_120 = x_143;
goto block_138;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
lean_dec(x_139);
x_146 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__2(x_118, x_2, x_3, x_4, x_5, x_6, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_unbox(x_147);
lean_dec(x_147);
x_119 = x_149;
x_120 = x_148;
goto block_138;
}
block_138:
{
if (x_119 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_box(0);
x_122 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___lambda__1(x_116, x_97, x_121, x_2, x_3, x_4, x_5, x_6, x_120);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_inc(x_97);
x_123 = l_Lean_mkLevelMVar(x_97);
x_124 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__8;
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__10;
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
lean_inc(x_116);
x_129 = l_Lean_mkLevelSucc(x_116);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1(x_118, x_133, x_2, x_3, x_4, x_5, x_6, x_120);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___lambda__1(x_116, x_97, x_135, x_2, x_3, x_4, x_5, x_6, x_136);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_135);
return x_137;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_97);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_150 = !lean_is_exclusive(x_105);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_105, 0);
lean_dec(x_151);
x_152 = lean_box(0);
lean_ctor_set(x_105, 0, x_152);
return x_105;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_105, 1);
lean_inc(x_153);
lean_dec(x_105);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_97);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_156 = !lean_is_exclusive(x_105);
if (x_156 == 0)
{
return x_105;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_105, 0);
x_158 = lean_ctor_get(x_105, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_105);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
lean_object* x_160; 
lean_dec(x_97);
x_160 = lean_ctor_get(x_104, 0);
lean_inc(x_160);
lean_dec(x_104);
x_1 = x_160;
x_7 = x_102;
goto _start;
}
}
default: 
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_7);
return x_163;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___lambda__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
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
x_13 = 1;
lean_inc(x_5);
lean_inc(x_3);
x_14 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f(x_1, x_13, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_5, x_16);
lean_dec(x_5);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
lean_ctor_set(x_20, 0, x_12);
x_24 = lean_st_ref_set(x_3, x_20, x_21);
lean_dec(x_3);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_20, 1);
x_32 = lean_ctor_get(x_20, 2);
x_33 = lean_ctor_get(x_20, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_st_ref_set(x_3, x_34, x_21);
lean_dec(x_3);
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
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_14, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
return x_14;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_15, 0);
lean_inc(x_43);
lean_dec(x_15);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_14, 0, x_44);
return x_14;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_dec(x_14);
x_46 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_47 = x_15;
} else {
 lean_dec_ref(x_15);
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
else
{
uint8_t x_50; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
return x_14;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_14, 0);
x_52 = lean_ctor_get(x_14, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_14);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_decLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_decLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_1 = lean_mk_string("assertion violation: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("v.isMax\n  ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.LevelDefEq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.LevelDefEq.0.Lean.Meta.solveSelfMax");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6;
x_3 = lean_unsigned_to_nat(96u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_10 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7;
x_11 = lean_panic_fn(x_9, x_10);
x_12 = lean_apply_5(x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_addTrace_addTraceOptions(x_10);
x_13 = lean_st_ref_take(x_6, x_11);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__2;
x_22 = l_Lean_Name_append(x_1, x_21);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
x_29 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_8);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Std_PersistentArray_push___rarg(x_20, x_32);
lean_ctor_set(x_15, 0, x_33);
x_34 = lean_st_ref_set(x_6, x_14, x_16);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_41 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
lean_dec(x_15);
x_43 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__2;
x_44 = l_Lean_Name_append(x_1, x_43);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_1);
x_46 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__4;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__6;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_12);
x_51 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_8);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_8);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Std_PersistentArray_push___rarg(x_42, x_54);
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_41);
lean_ctor_set(x_14, 3, x_56);
x_57 = lean_st_ref_set(x_6, x_14, x_16);
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
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_62 = lean_ctor_get(x_14, 0);
x_63 = lean_ctor_get(x_14, 1);
x_64 = lean_ctor_get(x_14, 2);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_14);
x_65 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_66 = lean_ctor_get(x_15, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_67 = x_15;
} else {
 lean_dec_ref(x_15);
 x_67 = lean_box(0);
}
x_68 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__2;
x_69 = l_Lean_Name_append(x_1, x_68);
x_70 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_70, 0, x_1);
x_71 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__4;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__6;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_12);
x_76 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_77);
lean_inc(x_8);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Std_PersistentArray_push___rarg(x_66, x_79);
if (lean_is_scalar(x_67)) {
 x_81 = lean_alloc_ctor(0, 1, 1);
} else {
 x_81 = x_67;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_65);
x_82 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_82, 0, x_62);
lean_ctor_set(x_82, 1, x_63);
lean_ctor_set(x_82, 2, x_64);
lean_ctor_set(x_82, 3, x_81);
x_83 = lean_st_ref_set(x_6, x_82, x_16);
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
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_14, 3);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_4);
lean_ctor_set(x_19, 3, x_18);
x_20 = l_Std_PersistentArray_push___rarg(x_17, x_19);
lean_ctor_set(x_14, 3, x_20);
x_21 = lean_st_ref_set(x_7, x_14, x_15);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
x_30 = lean_ctor_get(x_14, 2);
x_31 = lean_ctor_get(x_14, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_32 = lean_ctor_get(x_1, 3);
lean_inc(x_32);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set(x_33, 3, x_32);
x_34 = l_Std_PersistentArray_push___rarg(x_31, x_33);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_30);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_st_ref_set(x_7, x_35, x_15);
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
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("stuck");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" =?= ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
x_9 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_27 = lean_st_ref_get(x_6, x_7);
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
x_10 = x_32;
x_11 = x_31;
goto block_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_9, x_3, x_4, x_5, x_6, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_10 = x_37;
x_11 = x_36;
goto block_26;
}
block_26:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1(x_3, x_8, x_1, x_2, x_12, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_1);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_2);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
x_22 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_9, x_21, x_3, x_4, x_5, x_6, x_11);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1(x_3, x_8, x_1, x_2, x_23, x_3, x_4, x_5, x_6, x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_23);
lean_dec(x_3);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Meta_getLevelMVarDepth(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_getLevelMVarDepth(x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_nat_dec_lt(x_14, x_10);
lean_dec(x_10);
lean_dec(x_14);
x_16 = lean_box(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_nat_dec_lt(x_17, x_10);
lean_dec(x_10);
lean_dec(x_17);
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
lean_dec(x_10);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
if (lean_obj_tag(x_2) == 5)
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = 2;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_7);
return x_71;
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_72);
lean_dec(x_1);
x_73 = l_Lean_Level_isParam(x_2);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Level_isMVar(x_72);
if (x_74 == 0)
{
lean_object* x_75; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_75 = l_Lean_Meta_decLevel_x3f(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
lean_dec(x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_75, 0);
lean_dec(x_78);
x_79 = 2;
x_80 = lean_box(x_79);
lean_ctor_set(x_75, 0, x_80);
return x_75;
}
else
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = 2;
x_83 = lean_box(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
lean_dec(x_75);
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
lean_dec(x_76);
x_87 = l_Lean_Meta_isLevelDefEqAux(x_72, x_86, x_3, x_4, x_5, x_6, x_85);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
x_91 = l_Bool_toLBool(x_90);
x_92 = lean_box(x_91);
lean_ctor_set(x_87, 0, x_92);
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_87, 0);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_87);
x_95 = lean_unbox(x_93);
lean_dec(x_93);
x_96 = l_Bool_toLBool(x_95);
x_97 = lean_box(x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_87);
if (x_99 == 0)
{
return x_87;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_87, 0);
x_101 = lean_ctor_get(x_87, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_87);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_103 = !lean_is_exclusive(x_75);
if (x_103 == 0)
{
return x_75;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_75, 0);
x_105 = lean_ctor_get(x_75, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_75);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
x_107 = l_Lean_Level_occurs(x_72, x_2);
if (x_107 == 0)
{
lean_object* x_108; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_108 = l_Lean_Meta_decLevel_x3f(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
lean_dec(x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_108, 0);
lean_dec(x_111);
x_112 = 2;
x_113 = lean_box(x_112);
lean_ctor_set(x_108, 0, x_113);
return x_108;
}
else
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_dec(x_108);
x_115 = 2;
x_116 = lean_box(x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_108, 1);
lean_inc(x_118);
lean_dec(x_108);
x_119 = lean_ctor_get(x_109, 0);
lean_inc(x_119);
lean_dec(x_109);
x_120 = l_Lean_Meta_isLevelDefEqAux(x_72, x_119, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
x_124 = l_Bool_toLBool(x_123);
x_125 = lean_box(x_124);
lean_ctor_set(x_120, 0, x_125);
return x_120;
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_120, 0);
x_127 = lean_ctor_get(x_120, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_120);
x_128 = lean_unbox(x_126);
lean_dec(x_126);
x_129 = l_Bool_toLBool(x_128);
x_130 = lean_box(x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_127);
return x_131;
}
}
else
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_120);
if (x_132 == 0)
{
return x_120;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_120, 0);
x_134 = lean_ctor_get(x_120, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_120);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = !lean_is_exclusive(x_108);
if (x_136 == 0)
{
return x_108;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_108, 0);
x_138 = lean_ctor_get(x_108, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_108);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_140 = 2;
x_141 = lean_box(x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_7);
return x_142;
}
}
}
else
{
uint8_t x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_143 = 0;
x_144 = lean_box(x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_7);
return x_145;
}
}
}
case 5:
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
lean_inc(x_146);
x_147 = l_Lean_Meta_isReadOnlyLevelMVar(x_146, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = l_Lean_Meta_getConfig(x_3, x_4, x_5, x_6, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_2);
x_154 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(x_2, x_146, x_3, x_4, x_5, x_6, x_153);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
x_155 = lean_ctor_get_uint8(x_152, 11);
lean_dec(x_152);
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_154);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_ctor_get(x_154, 1);
x_158 = lean_ctor_get(x_154, 0);
lean_dec(x_158);
x_159 = l_Lean_Level_occurs(x_1, x_2);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_free_object(x_154);
x_160 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_161 = l_Lean_Meta_assignLevelMVar(x_160, x_2, x_3, x_4, x_5, x_6, x_157);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; uint8_t x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_161, 0);
lean_dec(x_163);
x_164 = 1;
x_165 = lean_box(x_164);
lean_ctor_set(x_161, 0, x_165);
return x_161;
}
else
{
lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_161, 1);
lean_inc(x_166);
lean_dec(x_161);
x_167 = 1;
x_168 = lean_box(x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_166);
return x_169;
}
}
else
{
uint8_t x_170; 
x_170 = l_Lean_Level_isMax(x_2);
if (x_170 == 0)
{
uint8_t x_171; lean_object* x_172; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = 2;
x_172 = lean_box(x_171);
lean_ctor_set(x_154, 0, x_172);
return x_154;
}
else
{
uint8_t x_173; 
x_173 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
lean_free_object(x_154);
x_174 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_175 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(x_174, x_2, x_3, x_4, x_5, x_6, x_157);
if (lean_obj_tag(x_175) == 0)
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_175, 0);
lean_dec(x_177);
x_178 = 1;
x_179 = lean_box(x_178);
lean_ctor_set(x_175, 0, x_179);
return x_175;
}
else
{
lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
lean_dec(x_175);
x_181 = 1;
x_182 = lean_box(x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
}
else
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_175);
if (x_184 == 0)
{
return x_175;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_175, 0);
x_186 = lean_ctor_get(x_175, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_175);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; lean_object* x_189; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = 2;
x_189 = lean_box(x_188);
lean_ctor_set(x_154, 0, x_189);
return x_154;
}
}
}
}
else
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_154, 1);
lean_inc(x_190);
lean_dec(x_154);
x_191 = l_Lean_Level_occurs(x_1, x_2);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; 
x_192 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_193 = l_Lean_Meta_assignLevelMVar(x_192, x_2, x_3, x_4, x_5, x_6, x_190);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_195 = x_193;
} else {
 lean_dec_ref(x_193);
 x_195 = lean_box(0);
}
x_196 = 1;
x_197 = lean_box(x_196);
if (lean_is_scalar(x_195)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_195;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_194);
return x_198;
}
else
{
uint8_t x_199; 
x_199 = l_Lean_Level_isMax(x_2);
if (x_199 == 0)
{
uint8_t x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_200 = 2;
x_201 = lean_box(x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_190);
return x_202;
}
else
{
uint8_t x_203; 
x_203 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_205 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(x_204, x_2, x_3, x_4, x_5, x_6, x_190);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_207 = x_205;
} else {
 lean_dec_ref(x_205);
 x_207 = lean_box(0);
}
x_208 = 1;
x_209 = lean_box(x_208);
if (lean_is_scalar(x_207)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_207;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_206);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_205, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_205, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_213 = x_205;
} else {
 lean_dec_ref(x_205);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
uint8_t x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_215 = 2;
x_216 = lean_box(x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_190);
return x_217;
}
}
}
}
}
else
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_154, 0);
lean_inc(x_218);
x_219 = lean_unbox(x_218);
lean_dec(x_218);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_154);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_221 = lean_ctor_get(x_154, 1);
x_222 = lean_ctor_get(x_154, 0);
lean_dec(x_222);
x_223 = l_Lean_Level_occurs(x_1, x_2);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; 
lean_free_object(x_154);
x_224 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_225 = l_Lean_Meta_assignLevelMVar(x_224, x_2, x_3, x_4, x_5, x_6, x_221);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; uint8_t x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_225, 0);
lean_dec(x_227);
x_228 = 1;
x_229 = lean_box(x_228);
lean_ctor_set(x_225, 0, x_229);
return x_225;
}
else
{
lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
lean_dec(x_225);
x_231 = 1;
x_232 = lean_box(x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_230);
return x_233;
}
}
else
{
uint8_t x_234; 
x_234 = l_Lean_Level_isMax(x_2);
if (x_234 == 0)
{
uint8_t x_235; lean_object* x_236; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_235 = 2;
x_236 = lean_box(x_235);
lean_ctor_set(x_154, 0, x_236);
return x_154;
}
else
{
uint8_t x_237; 
x_237 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
lean_free_object(x_154);
x_238 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_239 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(x_238, x_2, x_3, x_4, x_5, x_6, x_221);
if (lean_obj_tag(x_239) == 0)
{
uint8_t x_240; 
x_240 = !lean_is_exclusive(x_239);
if (x_240 == 0)
{
lean_object* x_241; uint8_t x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_239, 0);
lean_dec(x_241);
x_242 = 1;
x_243 = lean_box(x_242);
lean_ctor_set(x_239, 0, x_243);
return x_239;
}
else
{
lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_239, 1);
lean_inc(x_244);
lean_dec(x_239);
x_245 = 1;
x_246 = lean_box(x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
return x_247;
}
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_239);
if (x_248 == 0)
{
return x_239;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_239, 0);
x_250 = lean_ctor_get(x_239, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_239);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
else
{
uint8_t x_252; lean_object* x_253; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_252 = 2;
x_253 = lean_box(x_252);
lean_ctor_set(x_154, 0, x_253);
return x_154;
}
}
}
}
else
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_154, 1);
lean_inc(x_254);
lean_dec(x_154);
x_255 = l_Lean_Level_occurs(x_1, x_2);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; 
x_256 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_257 = l_Lean_Meta_assignLevelMVar(x_256, x_2, x_3, x_4, x_5, x_6, x_254);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
x_260 = 1;
x_261 = lean_box(x_260);
if (lean_is_scalar(x_259)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_259;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_258);
return x_262;
}
else
{
uint8_t x_263; 
x_263 = l_Lean_Level_isMax(x_2);
if (x_263 == 0)
{
uint8_t x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_264 = 2;
x_265 = lean_box(x_264);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_254);
return x_266;
}
else
{
uint8_t x_267; 
x_267 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_269 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(x_268, x_2, x_3, x_4, x_5, x_6, x_254);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_271 = x_269;
} else {
 lean_dec_ref(x_269);
 x_271 = lean_box(0);
}
x_272 = 1;
x_273 = lean_box(x_272);
if (lean_is_scalar(x_271)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_271;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_270);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_269, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_269, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_277 = x_269;
} else {
 lean_dec_ref(x_269);
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
else
{
uint8_t x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_279 = 2;
x_280 = lean_box(x_279);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_254);
return x_281;
}
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_282 = lean_ctor_get(x_154, 1);
lean_inc(x_282);
lean_dec(x_154);
x_283 = l_Lean_Level_mvarId_x21(x_2);
lean_dec(x_2);
x_284 = l_Lean_Meta_assignLevelMVar(x_283, x_1, x_3, x_4, x_5, x_6, x_282);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
lean_object* x_286; uint8_t x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_284, 0);
lean_dec(x_286);
x_287 = 1;
x_288 = lean_box(x_287);
lean_ctor_set(x_284, 0, x_288);
return x_284;
}
else
{
lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_284, 1);
lean_inc(x_289);
lean_dec(x_284);
x_290 = 1;
x_291 = lean_box(x_290);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_289);
return x_292;
}
}
}
}
else
{
uint8_t x_293; 
lean_dec(x_152);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_293 = !lean_is_exclusive(x_154);
if (x_293 == 0)
{
return x_154;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_154, 0);
x_295 = lean_ctor_get(x_154, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_154);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
uint8_t x_297; 
lean_dec(x_146);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = !lean_is_exclusive(x_147);
if (x_297 == 0)
{
lean_object* x_298; uint8_t x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_147, 0);
lean_dec(x_298);
x_299 = 2;
x_300 = lean_box(x_299);
lean_ctor_set(x_147, 0, x_300);
return x_147;
}
else
{
lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_ctor_get(x_147, 1);
lean_inc(x_301);
lean_dec(x_147);
x_302 = 2;
x_303 = lean_box(x_302);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_301);
return x_304;
}
}
}
else
{
uint8_t x_305; 
lean_dec(x_146);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_147);
if (x_305 == 0)
{
return x_147;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_147, 0);
x_307 = lean_ctor_get(x_147, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_147);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
default: 
{
uint8_t x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_309 = 2;
x_310 = lean_box(x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_7);
return x_311;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAux___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_4);
lean_inc(x_1);
x_10 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Level_normalize(x_11);
lean_dec(x_11);
lean_inc(x_2);
x_14 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_2, x_5, x_6, x_7, x_8, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Level_normalize(x_15);
lean_dec(x_15);
x_18 = lean_level_eq(x_1, x_13);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Meta_isLevelDefEqAux(x_13, x_17, x_5, x_6, x_7, x_8, x_16);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_level_eq(x_2, x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Meta_isLevelDefEqAux(x_13, x_17, x_5, x_6, x_7, x_8, x_16);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_1, x_2, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = 2;
x_27 = lean_unbox(x_24);
x_28 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_12_(x_27, x_26);
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = 1;
x_30 = lean_unbox(x_24);
lean_dec(x_24);
x_31 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_12_(x_30, x_29);
x_32 = lean_box(x_31);
lean_ctor_set(x_22, 0, x_32);
return x_22;
}
else
{
lean_object* x_33; 
lean_free_object(x_22);
lean_dec(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_33 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_unbox(x_35);
x_38 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_12_(x_37, x_26);
if (x_38 == 0)
{
uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = 1;
x_40 = lean_unbox(x_35);
lean_dec(x_35);
x_41 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_12_(x_40, x_39);
x_42 = lean_box(x_41);
lean_ctor_set(x_33, 0, x_42);
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_free_object(x_33);
lean_dec(x_35);
x_43 = lean_st_ref_get(x_8, x_36);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_get(x_6, x_44);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_1);
lean_inc(x_49);
x_50 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_49, x_1);
if (x_50 == 0)
{
uint8_t x_51; 
lean_inc(x_2);
x_51 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_49, x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_5, 0);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_85, 4);
lean_dec(x_85);
if (x_86 == 0)
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = 0;
x_88 = lean_box(x_87);
lean_ctor_set(x_45, 0, x_88);
return x_45;
}
else
{
uint8_t x_89; 
x_89 = l_Lean_Level_isMVar(x_1);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_Level_isMVar(x_2);
if (x_90 == 0)
{
uint8_t x_91; lean_object* x_92; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = 0;
x_92 = lean_box(x_91);
lean_ctor_set(x_45, 0, x_92);
return x_45;
}
else
{
lean_object* x_93; 
lean_free_object(x_45);
x_93 = lean_box(0);
x_52 = x_93;
goto block_84;
}
}
else
{
lean_object* x_94; 
lean_free_object(x_45);
x_94 = lean_box(0);
x_52 = x_94;
goto block_84;
}
}
block_84:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_52);
x_53 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
x_54 = lean_name_mk_string(x_3, x_53);
x_73 = lean_st_ref_get(x_8, x_48);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 3);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = 0;
x_55 = x_78;
x_56 = x_77;
goto block_72;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_dec(x_73);
lean_inc(x_54);
x_80 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_54, x_5, x_6, x_7, x_8, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_unbox(x_81);
lean_dec(x_81);
x_55 = x_83;
x_56 = x_82;
goto block_72;
}
block_72:
{
lean_object* x_57; 
x_57 = l_Lean_Meta_isLevelDefEqAux___lambda__2___closed__1;
if (x_55 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_54);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_box(0);
x_59 = lean_apply_6(x_57, x_58, x_5, x_6, x_7, x_8, x_56);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_1);
x_61 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_2);
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_61);
x_68 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_54, x_67, x_5, x_6, x_7, x_8, x_56);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_apply_6(x_57, x_69, x_5, x_6, x_7, x_8, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_95; uint8_t x_96; 
lean_free_object(x_45);
lean_dec(x_3);
x_95 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_5, x_6, x_7, x_8, x_48);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
x_98 = 1;
x_99 = lean_box(x_98);
lean_ctor_set(x_95, 0, x_99);
return x_95;
}
else
{
lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_dec(x_95);
x_101 = 1;
x_102 = lean_box(x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
else
{
lean_object* x_104; uint8_t x_105; 
lean_dec(x_49);
lean_free_object(x_45);
lean_dec(x_3);
x_104 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_5, x_6, x_7, x_8, x_48);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_104, 0);
lean_dec(x_106);
x_107 = 1;
x_108 = lean_box(x_107);
lean_ctor_set(x_104, 0, x_108);
return x_104;
}
else
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
lean_dec(x_104);
x_110 = 1;
x_111 = lean_box(x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_45, 0);
x_114 = lean_ctor_get(x_45, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_45);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_1);
lean_inc(x_115);
x_116 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_115, x_1);
if (x_116 == 0)
{
uint8_t x_117; 
lean_inc(x_2);
x_117 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_115, x_2);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_5, 0);
lean_inc(x_151);
x_152 = lean_ctor_get_uint8(x_151, 4);
lean_dec(x_151);
if (x_152 == 0)
{
uint8_t x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = 0;
x_154 = lean_box(x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_114);
return x_155;
}
else
{
uint8_t x_156; 
x_156 = l_Lean_Level_isMVar(x_1);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = l_Lean_Level_isMVar(x_2);
if (x_157 == 0)
{
uint8_t x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = 0;
x_159 = lean_box(x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_114);
return x_160;
}
else
{
lean_object* x_161; 
x_161 = lean_box(0);
x_118 = x_161;
goto block_150;
}
}
else
{
lean_object* x_162; 
x_162 = lean_box(0);
x_118 = x_162;
goto block_150;
}
}
block_150:
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_118);
x_119 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
x_120 = lean_name_mk_string(x_3, x_119);
x_139 = lean_st_ref_get(x_8, x_114);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 3);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = 0;
x_121 = x_144;
x_122 = x_143;
goto block_138;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
lean_dec(x_139);
lean_inc(x_120);
x_146 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_120, x_5, x_6, x_7, x_8, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_unbox(x_147);
lean_dec(x_147);
x_121 = x_149;
x_122 = x_148;
goto block_138;
}
block_138:
{
lean_object* x_123; 
x_123 = l_Lean_Meta_isLevelDefEqAux___lambda__2___closed__1;
if (x_121 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_120);
lean_dec(x_2);
lean_dec(x_1);
x_124 = lean_box(0);
x_125 = lean_apply_6(x_123, x_124, x_5, x_6, x_7, x_8, x_122);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_126 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_126, 0, x_1);
x_127 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_130 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_131, 0, x_2);
x_132 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_127);
x_134 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_120, x_133, x_5, x_6, x_7, x_8, x_122);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_apply_6(x_123, x_135, x_5, x_6, x_7, x_8, x_136);
return x_137;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_3);
x_163 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_5, x_6, x_7, x_8, x_114);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
x_166 = 1;
x_167 = lean_box(x_166);
if (lean_is_scalar(x_165)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_165;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_164);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_115);
lean_dec(x_3);
x_169 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_5, x_6, x_7, x_8, x_114);
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
x_172 = 1;
x_173 = lean_box(x_172);
if (lean_is_scalar(x_171)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_171;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_170);
return x_174;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_178; 
x_175 = lean_ctor_get(x_33, 0);
x_176 = lean_ctor_get(x_33, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_33);
x_177 = lean_unbox(x_175);
x_178 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_12_(x_177, x_26);
if (x_178 == 0)
{
uint8_t x_179; uint8_t x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_179 = 1;
x_180 = lean_unbox(x_175);
lean_dec(x_175);
x_181 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_12_(x_180, x_179);
x_182 = lean_box(x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_176);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
lean_dec(x_175);
x_184 = lean_st_ref_get(x_8, x_176);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_st_ref_get(x_6, x_185);
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
lean_dec(x_187);
lean_inc(x_1);
lean_inc(x_190);
x_191 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_190, x_1);
if (x_191 == 0)
{
uint8_t x_192; 
lean_inc(x_2);
x_192 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_190, x_2);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_226; uint8_t x_227; 
x_226 = lean_ctor_get(x_5, 0);
lean_inc(x_226);
x_227 = lean_ctor_get_uint8(x_226, 4);
lean_dec(x_226);
if (x_227 == 0)
{
uint8_t x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_228 = 0;
x_229 = lean_box(x_228);
if (lean_is_scalar(x_189)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_189;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_188);
return x_230;
}
else
{
uint8_t x_231; 
x_231 = l_Lean_Level_isMVar(x_1);
if (x_231 == 0)
{
uint8_t x_232; 
x_232 = l_Lean_Level_isMVar(x_2);
if (x_232 == 0)
{
uint8_t x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_233 = 0;
x_234 = lean_box(x_233);
if (lean_is_scalar(x_189)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_189;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_188);
return x_235;
}
else
{
lean_object* x_236; 
lean_dec(x_189);
x_236 = lean_box(0);
x_193 = x_236;
goto block_225;
}
}
else
{
lean_object* x_237; 
lean_dec(x_189);
x_237 = lean_box(0);
x_193 = x_237;
goto block_225;
}
}
block_225:
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
lean_dec(x_193);
x_194 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
x_195 = lean_name_mk_string(x_3, x_194);
x_214 = lean_st_ref_get(x_8, x_188);
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
x_196 = x_219;
x_197 = x_218;
goto block_213;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_220 = lean_ctor_get(x_214, 1);
lean_inc(x_220);
lean_dec(x_214);
lean_inc(x_195);
x_221 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_195, x_5, x_6, x_7, x_8, x_220);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_unbox(x_222);
lean_dec(x_222);
x_196 = x_224;
x_197 = x_223;
goto block_213;
}
block_213:
{
lean_object* x_198; 
x_198 = l_Lean_Meta_isLevelDefEqAux___lambda__2___closed__1;
if (x_196 == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_195);
lean_dec(x_2);
lean_dec(x_1);
x_199 = lean_box(0);
x_200 = lean_apply_6(x_198, x_199, x_5, x_6, x_7, x_8, x_197);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_201 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_201, 0, x_1);
x_202 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_203 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_205 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_206, 0, x_2);
x_207 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_202);
x_209 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_195, x_208, x_5, x_6, x_7, x_8, x_197);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_apply_6(x_198, x_210, x_5, x_6, x_7, x_8, x_211);
return x_212;
}
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_189);
lean_dec(x_3);
x_238 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_5, x_6, x_7, x_8, x_188);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_240 = x_238;
} else {
 lean_dec_ref(x_238);
 x_240 = lean_box(0);
}
x_241 = 1;
x_242 = lean_box(x_241);
if (lean_is_scalar(x_240)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_240;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_239);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_3);
x_244 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_5, x_6, x_7, x_8, x_188);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_246 = x_244;
} else {
 lean_dec_ref(x_244);
 x_246 = lean_box(0);
}
x_247 = 1;
x_248 = lean_box(x_247);
if (lean_is_scalar(x_246)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_246;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_245);
return x_249;
}
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_33);
if (x_250 == 0)
{
return x_33;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_33, 0);
x_252 = lean_ctor_get(x_33, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_33);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; uint8_t x_257; uint8_t x_258; 
x_254 = lean_ctor_get(x_22, 0);
x_255 = lean_ctor_get(x_22, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_22);
x_256 = 2;
x_257 = lean_unbox(x_254);
x_258 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_12_(x_257, x_256);
if (x_258 == 0)
{
uint8_t x_259; uint8_t x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_259 = 1;
x_260 = lean_unbox(x_254);
lean_dec(x_254);
x_261 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_12_(x_260, x_259);
x_262 = lean_box(x_261);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_255);
return x_263;
}
else
{
lean_object* x_264; 
lean_dec(x_254);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_264 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_5, x_6, x_7, x_8, x_255);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; uint8_t x_269; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_267 = x_264;
} else {
 lean_dec_ref(x_264);
 x_267 = lean_box(0);
}
x_268 = lean_unbox(x_265);
x_269 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_12_(x_268, x_256);
if (x_269 == 0)
{
uint8_t x_270; uint8_t x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = 1;
x_271 = lean_unbox(x_265);
lean_dec(x_265);
x_272 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_12_(x_271, x_270);
x_273 = lean_box(x_272);
if (lean_is_scalar(x_267)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_267;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_266);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
lean_dec(x_267);
lean_dec(x_265);
x_275 = lean_st_ref_get(x_8, x_266);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_277 = lean_st_ref_get(x_6, x_276);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_280 = x_277;
} else {
 lean_dec_ref(x_277);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_278, 0);
lean_inc(x_281);
lean_dec(x_278);
lean_inc(x_1);
lean_inc(x_281);
x_282 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_281, x_1);
if (x_282 == 0)
{
uint8_t x_283; 
lean_inc(x_2);
x_283 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_281, x_2);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_317; uint8_t x_318; 
x_317 = lean_ctor_get(x_5, 0);
lean_inc(x_317);
x_318 = lean_ctor_get_uint8(x_317, 4);
lean_dec(x_317);
if (x_318 == 0)
{
uint8_t x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_319 = 0;
x_320 = lean_box(x_319);
if (lean_is_scalar(x_280)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_280;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_279);
return x_321;
}
else
{
uint8_t x_322; 
x_322 = l_Lean_Level_isMVar(x_1);
if (x_322 == 0)
{
uint8_t x_323; 
x_323 = l_Lean_Level_isMVar(x_2);
if (x_323 == 0)
{
uint8_t x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_324 = 0;
x_325 = lean_box(x_324);
if (lean_is_scalar(x_280)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_280;
}
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_279);
return x_326;
}
else
{
lean_object* x_327; 
lean_dec(x_280);
x_327 = lean_box(0);
x_284 = x_327;
goto block_316;
}
}
else
{
lean_object* x_328; 
lean_dec(x_280);
x_328 = lean_box(0);
x_284 = x_328;
goto block_316;
}
}
block_316:
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
lean_dec(x_284);
x_285 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
x_286 = lean_name_mk_string(x_3, x_285);
x_305 = lean_st_ref_get(x_8, x_279);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_306, 3);
lean_inc(x_307);
lean_dec(x_306);
x_308 = lean_ctor_get_uint8(x_307, sizeof(void*)*1);
lean_dec(x_307);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = lean_ctor_get(x_305, 1);
lean_inc(x_309);
lean_dec(x_305);
x_310 = 0;
x_287 = x_310;
x_288 = x_309;
goto block_304;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_311 = lean_ctor_get(x_305, 1);
lean_inc(x_311);
lean_dec(x_305);
lean_inc(x_286);
x_312 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_286, x_5, x_6, x_7, x_8, x_311);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_unbox(x_313);
lean_dec(x_313);
x_287 = x_315;
x_288 = x_314;
goto block_304;
}
block_304:
{
lean_object* x_289; 
x_289 = l_Lean_Meta_isLevelDefEqAux___lambda__2___closed__1;
if (x_287 == 0)
{
lean_object* x_290; lean_object* x_291; 
lean_dec(x_286);
lean_dec(x_2);
lean_dec(x_1);
x_290 = lean_box(0);
x_291 = lean_apply_6(x_289, x_290, x_5, x_6, x_7, x_8, x_288);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_292 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_292, 0, x_1);
x_293 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_294 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_292);
x_295 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_296 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_297, 0, x_2);
x_298 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_293);
x_300 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_286, x_299, x_5, x_6, x_7, x_8, x_288);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_apply_6(x_289, x_301, x_5, x_6, x_7, x_8, x_302);
return x_303;
}
}
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_280);
lean_dec(x_3);
x_329 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_5, x_6, x_7, x_8, x_279);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_331 = x_329;
} else {
 lean_dec_ref(x_329);
 x_331 = lean_box(0);
}
x_332 = 1;
x_333 = lean_box(x_332);
if (lean_is_scalar(x_331)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_331;
}
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_330);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_3);
x_335 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_5, x_6, x_7, x_8, x_279);
x_336 = lean_ctor_get(x_335, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_337 = x_335;
} else {
 lean_dec_ref(x_335);
 x_337 = lean_box(0);
}
x_338 = 1;
x_339 = lean_box(x_338);
if (lean_is_scalar(x_337)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_337;
}
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_336);
return x_340;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_341 = lean_ctor_get(x_264, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_264, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_343 = x_264;
} else {
 lean_dec_ref(x_264);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_342);
return x_344;
}
}
}
}
else
{
uint8_t x_345; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_345 = !lean_is_exclusive(x_22);
if (x_345 == 0)
{
return x_22;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_22, 0);
x_347 = lean_ctor_get(x_22, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_22);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_11 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
x_31 = lean_st_ref_get(x_6, x_7);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = 0;
x_12 = x_36;
x_13 = x_35;
goto block_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_11, x_3, x_4, x_5, x_6, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unbox(x_39);
lean_dec(x_39);
x_12 = x_41;
x_13 = x_40;
goto block_30;
}
block_30:
{
if (x_12 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_15 = lean_box(0);
x_16 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_14, x_15, x_3, x_4, x_5, x_6, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_1);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_2);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
x_25 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_11, x_24, x_3, x_4, x_5, x_6, x_13);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_29 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_28, x_26, x_3, x_4, x_5, x_6, x_27);
return x_29;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Lean_Level_getOffsetAux(x_1, x_42);
lean_dec(x_1);
x_44 = l_Lean_Level_getOffsetAux(x_2, x_42);
lean_dec(x_2);
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_7);
return x_47;
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = l_Lean_Level_getLevelOffset(x_1);
x_49 = l_Lean_Level_getLevelOffset(x_2);
x_50 = lean_level_eq(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_51 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
x_71 = lean_st_ref_get(x_6, x_7);
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
x_52 = x_76;
x_53 = x_75;
goto block_70;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_dec(x_71);
x_78 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_51, x_3, x_4, x_5, x_6, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_unbox(x_79);
lean_dec(x_79);
x_52 = x_81;
x_53 = x_80;
goto block_70;
}
block_70:
{
if (x_52 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_55 = lean_box(0);
x_56 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_54, x_55, x_3, x_4, x_5, x_6, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_inc(x_1);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_1);
x_58 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_inc(x_2);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_2);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
x_65 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_51, x_64, x_3, x_4, x_5, x_6, x_53);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_69 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_68, x_66, x_3, x_4, x_5, x_6, x_67);
return x_69;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Lean_Level_getOffsetAux(x_1, x_82);
lean_dec(x_1);
x_84 = l_Lean_Level_getOffsetAux(x_2, x_82);
lean_dec(x_2);
x_85 = lean_nat_dec_eq(x_83, x_84);
lean_dec(x_84);
lean_dec(x_83);
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_7);
return x_87;
}
}
case 1:
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
lean_dec(x_1);
x_89 = lean_ctor_get(x_2, 0);
lean_inc(x_89);
lean_dec(x_2);
x_1 = x_88;
x_2 = x_89;
goto _start;
}
case 2:
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = l_Lean_Level_getLevelOffset(x_1);
x_92 = l_Lean_Level_getLevelOffset(x_2);
x_93 = lean_level_eq(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_94 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
x_114 = lean_st_ref_get(x_6, x_7);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 3);
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_ctor_get_uint8(x_116, sizeof(void*)*1);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec(x_114);
x_119 = 0;
x_95 = x_119;
x_96 = x_118;
goto block_113;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_114, 1);
lean_inc(x_120);
lean_dec(x_114);
x_121 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_94, x_3, x_4, x_5, x_6, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_unbox(x_122);
lean_dec(x_122);
x_95 = x_124;
x_96 = x_123;
goto block_113;
}
block_113:
{
if (x_95 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_98 = lean_box(0);
x_99 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_97, x_98, x_3, x_4, x_5, x_6, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_inc(x_1);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_1);
x_101 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
lean_inc(x_2);
x_105 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_105, 0, x_2);
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_101);
x_108 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_94, x_107, x_3, x_4, x_5, x_6, x_96);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_112 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_111, x_109, x_3, x_4, x_5, x_6, x_110);
return x_112;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = lean_unsigned_to_nat(0u);
x_126 = l_Lean_Level_getOffsetAux(x_1, x_125);
lean_dec(x_1);
x_127 = l_Lean_Level_getOffsetAux(x_2, x_125);
lean_dec(x_2);
x_128 = lean_nat_dec_eq(x_126, x_127);
lean_dec(x_127);
lean_dec(x_126);
x_129 = lean_box(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_7);
return x_130;
}
}
case 3:
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = l_Lean_Level_getLevelOffset(x_1);
x_132 = l_Lean_Level_getLevelOffset(x_2);
x_133 = lean_level_eq(x_131, x_132);
lean_dec(x_132);
lean_dec(x_131);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_134 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
x_154 = lean_st_ref_get(x_6, x_7);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_155, 3);
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_ctor_get_uint8(x_156, sizeof(void*)*1);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_154, 1);
lean_inc(x_158);
lean_dec(x_154);
x_159 = 0;
x_135 = x_159;
x_136 = x_158;
goto block_153;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
lean_dec(x_154);
x_161 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_134, x_3, x_4, x_5, x_6, x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_unbox(x_162);
lean_dec(x_162);
x_135 = x_164;
x_136 = x_163;
goto block_153;
}
block_153:
{
if (x_135 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_138 = lean_box(0);
x_139 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_137, x_138, x_3, x_4, x_5, x_6, x_136);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_inc(x_1);
x_140 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_140, 0, x_1);
x_141 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_142 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_144 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_2);
x_145 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_145, 0, x_2);
x_146 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_141);
x_148 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_134, x_147, x_3, x_4, x_5, x_6, x_136);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_152 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_151, x_149, x_3, x_4, x_5, x_6, x_150);
return x_152;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_165 = lean_unsigned_to_nat(0u);
x_166 = l_Lean_Level_getOffsetAux(x_1, x_165);
lean_dec(x_1);
x_167 = l_Lean_Level_getOffsetAux(x_2, x_165);
lean_dec(x_2);
x_168 = lean_nat_dec_eq(x_166, x_167);
lean_dec(x_167);
lean_dec(x_166);
x_169 = lean_box(x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_7);
return x_170;
}
}
case 4:
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = l_Lean_Level_getLevelOffset(x_1);
x_172 = l_Lean_Level_getLevelOffset(x_2);
x_173 = lean_level_eq(x_171, x_172);
lean_dec(x_172);
lean_dec(x_171);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_174 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
x_194 = lean_st_ref_get(x_6, x_7);
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
x_175 = x_199;
x_176 = x_198;
goto block_193;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_200 = lean_ctor_get(x_194, 1);
lean_inc(x_200);
lean_dec(x_194);
x_201 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_174, x_3, x_4, x_5, x_6, x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_unbox(x_202);
lean_dec(x_202);
x_175 = x_204;
x_176 = x_203;
goto block_193;
}
block_193:
{
if (x_175 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_178 = lean_box(0);
x_179 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_177, x_178, x_3, x_4, x_5, x_6, x_176);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_inc(x_1);
x_180 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_180, 0, x_1);
x_181 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_182 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
x_183 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_184 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
lean_inc(x_2);
x_185 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_185, 0, x_2);
x_186 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_181);
x_188 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_174, x_187, x_3, x_4, x_5, x_6, x_176);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_192 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_191, x_189, x_3, x_4, x_5, x_6, x_190);
return x_192;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_205 = lean_unsigned_to_nat(0u);
x_206 = l_Lean_Level_getOffsetAux(x_1, x_205);
lean_dec(x_1);
x_207 = l_Lean_Level_getOffsetAux(x_2, x_205);
lean_dec(x_2);
x_208 = lean_nat_dec_eq(x_206, x_207);
lean_dec(x_207);
lean_dec(x_206);
x_209 = lean_box(x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_7);
return x_210;
}
}
default: 
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_211 = l_Lean_Level_getLevelOffset(x_1);
x_212 = l_Lean_Level_getLevelOffset(x_2);
x_213 = lean_level_eq(x_211, x_212);
lean_dec(x_212);
lean_dec(x_211);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_214 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
x_234 = lean_st_ref_get(x_6, x_7);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_235, 3);
lean_inc(x_236);
lean_dec(x_235);
x_237 = lean_ctor_get_uint8(x_236, sizeof(void*)*1);
lean_dec(x_236);
if (x_237 == 0)
{
lean_object* x_238; uint8_t x_239; 
x_238 = lean_ctor_get(x_234, 1);
lean_inc(x_238);
lean_dec(x_234);
x_239 = 0;
x_215 = x_239;
x_216 = x_238;
goto block_233;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_240 = lean_ctor_get(x_234, 1);
lean_inc(x_240);
lean_dec(x_234);
x_241 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_214, x_3, x_4, x_5, x_6, x_240);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_unbox(x_242);
lean_dec(x_242);
x_215 = x_244;
x_216 = x_243;
goto block_233;
}
block_233:
{
if (x_215 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_218 = lean_box(0);
x_219 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_217, x_218, x_3, x_4, x_5, x_6, x_216);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_inc(x_1);
x_220 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_220, 0, x_1);
x_221 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_222 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_220);
x_223 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_224 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
lean_inc(x_2);
x_225 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_225, 0, x_2);
x_226 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_221);
x_228 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_214, x_227, x_3, x_4, x_5, x_6, x_216);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_232 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_231, x_229, x_3, x_4, x_5, x_6, x_230);
return x_232;
}
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_245 = lean_unsigned_to_nat(0u);
x_246 = l_Lean_Level_getOffsetAux(x_1, x_245);
lean_dec(x_1);
x_247 = l_Lean_Level_getOffsetAux(x_2, x_245);
lean_dec(x_2);
x_248 = lean_nat_dec_eq(x_246, x_247);
lean_dec(x_247);
lean_dec(x_246);
x_249 = lean_box(x_248);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_7);
return x_250;
}
}
}
}
case 2:
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_251 = l_Lean_Level_getLevelOffset(x_1);
x_252 = l_Lean_Level_getLevelOffset(x_2);
x_253 = lean_level_eq(x_251, x_252);
lean_dec(x_252);
lean_dec(x_251);
if (x_253 == 0)
{
lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_254 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
x_274 = lean_st_ref_get(x_6, x_7);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_275, 3);
lean_inc(x_276);
lean_dec(x_275);
x_277 = lean_ctor_get_uint8(x_276, sizeof(void*)*1);
lean_dec(x_276);
if (x_277 == 0)
{
lean_object* x_278; uint8_t x_279; 
x_278 = lean_ctor_get(x_274, 1);
lean_inc(x_278);
lean_dec(x_274);
x_279 = 0;
x_255 = x_279;
x_256 = x_278;
goto block_273;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_280 = lean_ctor_get(x_274, 1);
lean_inc(x_280);
lean_dec(x_274);
x_281 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_254, x_3, x_4, x_5, x_6, x_280);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_unbox(x_282);
lean_dec(x_282);
x_255 = x_284;
x_256 = x_283;
goto block_273;
}
block_273:
{
if (x_255 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_258 = lean_box(0);
x_259 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_257, x_258, x_3, x_4, x_5, x_6, x_256);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_inc(x_1);
x_260 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_260, 0, x_1);
x_261 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_262 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
x_263 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_264 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
lean_inc(x_2);
x_265 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_265, 0, x_2);
x_266 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_261);
x_268 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_254, x_267, x_3, x_4, x_5, x_6, x_256);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_272 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_271, x_269, x_3, x_4, x_5, x_6, x_270);
return x_272;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_285 = lean_unsigned_to_nat(0u);
x_286 = l_Lean_Level_getOffsetAux(x_1, x_285);
lean_dec(x_1);
x_287 = l_Lean_Level_getOffsetAux(x_2, x_285);
lean_dec(x_2);
x_288 = lean_nat_dec_eq(x_286, x_287);
lean_dec(x_287);
lean_dec(x_286);
x_289 = lean_box(x_288);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_7);
return x_290;
}
}
case 3:
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_291 = l_Lean_Level_getLevelOffset(x_1);
x_292 = l_Lean_Level_getLevelOffset(x_2);
x_293 = lean_level_eq(x_291, x_292);
lean_dec(x_292);
lean_dec(x_291);
if (x_293 == 0)
{
lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_294 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
x_314 = lean_st_ref_get(x_6, x_7);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_315, 3);
lean_inc(x_316);
lean_dec(x_315);
x_317 = lean_ctor_get_uint8(x_316, sizeof(void*)*1);
lean_dec(x_316);
if (x_317 == 0)
{
lean_object* x_318; uint8_t x_319; 
x_318 = lean_ctor_get(x_314, 1);
lean_inc(x_318);
lean_dec(x_314);
x_319 = 0;
x_295 = x_319;
x_296 = x_318;
goto block_313;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_320 = lean_ctor_get(x_314, 1);
lean_inc(x_320);
lean_dec(x_314);
x_321 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_294, x_3, x_4, x_5, x_6, x_320);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
x_324 = lean_unbox(x_322);
lean_dec(x_322);
x_295 = x_324;
x_296 = x_323;
goto block_313;
}
block_313:
{
if (x_295 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_298 = lean_box(0);
x_299 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_297, x_298, x_3, x_4, x_5, x_6, x_296);
return x_299;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_inc(x_1);
x_300 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_300, 0, x_1);
x_301 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_302 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_300);
x_303 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_304 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
lean_inc(x_2);
x_305 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_305, 0, x_2);
x_306 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_301);
x_308 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_294, x_307, x_3, x_4, x_5, x_6, x_296);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_312 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_311, x_309, x_3, x_4, x_5, x_6, x_310);
return x_312;
}
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_325 = lean_unsigned_to_nat(0u);
x_326 = l_Lean_Level_getOffsetAux(x_1, x_325);
lean_dec(x_1);
x_327 = l_Lean_Level_getOffsetAux(x_2, x_325);
lean_dec(x_2);
x_328 = lean_nat_dec_eq(x_326, x_327);
lean_dec(x_327);
lean_dec(x_326);
x_329 = lean_box(x_328);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_7);
return x_330;
}
}
case 4:
{
lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_331 = l_Lean_Level_getLevelOffset(x_1);
x_332 = l_Lean_Level_getLevelOffset(x_2);
x_333 = lean_level_eq(x_331, x_332);
lean_dec(x_332);
lean_dec(x_331);
if (x_333 == 0)
{
lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_334 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
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
x_335 = x_359;
x_336 = x_358;
goto block_353;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_360 = lean_ctor_get(x_354, 1);
lean_inc(x_360);
lean_dec(x_354);
x_361 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_334, x_3, x_4, x_5, x_6, x_360);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = lean_unbox(x_362);
lean_dec(x_362);
x_335 = x_364;
x_336 = x_363;
goto block_353;
}
block_353:
{
if (x_335 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_338 = lean_box(0);
x_339 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_337, x_338, x_3, x_4, x_5, x_6, x_336);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_inc(x_1);
x_340 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_340, 0, x_1);
x_341 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_342 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_340);
x_343 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_344 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
lean_inc(x_2);
x_345 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_345, 0, x_2);
x_346 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_341);
x_348 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_334, x_347, x_3, x_4, x_5, x_6, x_336);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_352 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_351, x_349, x_3, x_4, x_5, x_6, x_350);
return x_352;
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_365 = lean_unsigned_to_nat(0u);
x_366 = l_Lean_Level_getOffsetAux(x_1, x_365);
lean_dec(x_1);
x_367 = l_Lean_Level_getOffsetAux(x_2, x_365);
lean_dec(x_2);
x_368 = lean_nat_dec_eq(x_366, x_367);
lean_dec(x_367);
lean_dec(x_366);
x_369 = lean_box(x_368);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_7);
return x_370;
}
}
default: 
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_371 = l_Lean_Level_getLevelOffset(x_1);
x_372 = l_Lean_Level_getLevelOffset(x_2);
x_373 = lean_level_eq(x_371, x_372);
lean_dec(x_372);
lean_dec(x_371);
if (x_373 == 0)
{
lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_374 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
x_394 = lean_st_ref_get(x_6, x_7);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_395, 3);
lean_inc(x_396);
lean_dec(x_395);
x_397 = lean_ctor_get_uint8(x_396, sizeof(void*)*1);
lean_dec(x_396);
if (x_397 == 0)
{
lean_object* x_398; uint8_t x_399; 
x_398 = lean_ctor_get(x_394, 1);
lean_inc(x_398);
lean_dec(x_394);
x_399 = 0;
x_375 = x_399;
x_376 = x_398;
goto block_393;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_400 = lean_ctor_get(x_394, 1);
lean_inc(x_400);
lean_dec(x_394);
x_401 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_374, x_3, x_4, x_5, x_6, x_400);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_unbox(x_402);
lean_dec(x_402);
x_375 = x_404;
x_376 = x_403;
goto block_393;
}
block_393:
{
if (x_375 == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_378 = lean_box(0);
x_379 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_377, x_378, x_3, x_4, x_5, x_6, x_376);
return x_379;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_inc(x_1);
x_380 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_380, 0, x_1);
x_381 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_382 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_380);
x_383 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_384 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
lean_inc(x_2);
x_385 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_385, 0, x_2);
x_386 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
x_387 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_381);
x_388 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_374, x_387, x_3, x_4, x_5, x_6, x_376);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_392 = l_Lean_Meta_isLevelDefEqAux___lambda__2(x_1, x_2, x_391, x_389, x_3, x_4, x_5, x_6, x_390);
return x_392;
}
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_405 = lean_unsigned_to_nat(0u);
x_406 = l_Lean_Level_getOffsetAux(x_1, x_405);
lean_dec(x_1);
x_407 = l_Lean_Level_getOffsetAux(x_2, x_405);
lean_dec(x_2);
x_408 = lean_nat_dec_eq(x_406, x_407);
lean_dec(x_407);
lean_dec(x_406);
x_409 = lean_box(x_408);
x_410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_7);
return x_410;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isLevelDefEqAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isListLevelDefEqAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getResetPostponed___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getResetPostponed___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getResetPostponed___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getResetPostponed___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_getResetPostponed___closed__2;
x_3 = l_Lean_Meta_getResetPostponed___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_getResetPostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = l_Lean_Meta_getPostponed___rarg(x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_getResetPostponed___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_getResetPostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses___spec__2(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__2___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Std_RBNode_findCore___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_instantiateMVars(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_2);
x_15 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses(x_13, x_2);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Meta_instantiateMVars(x_16, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_48; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_exposeRelevantUniverses(x_18, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_15);
x_48 = lean_infer_type(x_15, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_51 = lean_infer_type(x_20, x_7, x_8, x_9, x_10, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_stringToMessageData(x_4);
x_55 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_5);
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_6);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_55);
x_65 = l_Lean_indentD(x_64);
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_65);
x_67 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__2;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_15);
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_55);
lean_ctor_set(x_70, 1, x_69);
x_71 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__6;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_73, 0, x_49);
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_55);
x_76 = l_Lean_indentD(x_75);
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_76);
x_78 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__4;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_20);
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_55);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_71);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_52);
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_55);
x_86 = l_Lean_indentD(x_85);
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_55);
x_89 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_88, x_7, x_8, x_9, x_10, x_53);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_89;
}
else
{
lean_object* x_90; 
lean_dec(x_49);
x_90 = lean_ctor_get(x_51, 1);
lean_inc(x_90);
lean_dec(x_51);
x_21 = x_90;
goto block_47;
}
}
else
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_48, 1);
lean_inc(x_91);
lean_dec(x_48);
x_21 = x_91;
goto block_47;
}
block_47:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_22 = l_Lean_stringToMessageData(x_4);
x_23 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_5);
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_6);
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
x_33 = l_Lean_indentD(x_32);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__2;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_15);
x_38 = l_Lean_indentD(x_37);
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__4;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_20);
x_43 = l_Lean_indentD(x_42);
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_23);
x_46 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_45, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_46;
}
}
else
{
uint8_t x_92; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_17);
if (x_92 == 0)
{
return x_17;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_17, 0);
x_94 = lean_ctor_get(x_17, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_17);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_12);
if (x_96 == 0)
{
return x_12;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_12, 0);
x_98 = lean_ctor_get(x_12, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_12);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_10 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
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
x_16 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
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
x_31 = lean_box(0);
lean_inc(x_30);
x_32 = l_Lean_Level_collectMVars(x_30, x_31);
lean_inc(x_29);
x_33 = l_Lean_Level_collectMVars(x_29, x_32);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__2___boxed), 2, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___boxed), 11, 6);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_34);
lean_closure_set(x_36, 2, x_26);
lean_closure_set(x_36, 3, x_1);
lean_closure_set(x_36, 4, x_29);
lean_closure_set(x_36, 5, x_30);
x_37 = l_Lean_Meta_withLCtx___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__2___rarg(x_27, x_28, x_36, x_3, x_4, x_5, x_6, x_7);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_findCore___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkLevelStuckErrorMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkLevelErrorMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_mkLevelErrorMessage___closed__1;
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_18);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2(x_1, x_2, x_3, x_16, x_18, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_8, 0, x_24);
lean_ctor_set(x_20, 0, x_8);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_8, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_18);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_29);
lean_ctor_set(x_8, 0, x_4);
x_30 = 1;
x_31 = x_7 + x_30;
x_7 = x_31;
x_13 = x_28;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_8);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_37);
lean_inc(x_3);
lean_inc(x_2);
x_38 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2(x_1, x_2, x_3, x_16, x_37, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
lean_dec(x_37);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_inc(x_4);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_46);
x_48 = 1;
x_49 = x_7 + x_48;
x_7 = x_49;
x_8 = x_47;
x_13 = x_45;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_53 = x_38;
} else {
 lean_dec_ref(x_38);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_17 = x_7;
} else {
 lean_dec_ref(x_7);
 x_17 = lean_box(0);
}
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_15, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_8, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_8, 4);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_37 = l_Lean_Meta_isLevelDefEqAux(x_29, x_30, x_36, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
if (x_1 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_15);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3;
x_18 = x_41;
x_19 = x_40;
goto block_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = l_Lean_Meta_mkLevelErrorMessage___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_44 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(x_43, x_15, x_8, x_9, x_10, x_11, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_45, x_8, x_9, x_10, x_11, x_46);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_15);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
lean_dec(x_37);
lean_inc(x_2);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_2);
x_18 = x_57;
x_19 = x_56;
goto block_28;
}
}
else
{
uint8_t x_58; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_37);
if (x_58 == 0)
{
return x_37;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_37, 0);
x_60 = lean_ctor_get(x_37, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_37);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
block_28:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
lean_inc(x_3);
if (lean_is_scalar(x_17)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_17;
}
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = x_6 + x_25;
x_6 = x_26;
x_7 = x_24;
x_12 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
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
lean_dec(x_11);
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
lean_dec(x_3);
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
lean_dec(x_4);
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
lean_dec(x_34);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_17 = x_7;
} else {
 lean_dec_ref(x_7);
 x_17 = lean_box(0);
}
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_15, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_8, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_8, 4);
lean_inc(x_36);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_38 = l_Lean_Meta_isLevelDefEqAux(x_30, x_31, x_37, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
if (x_1 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_15);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3;
x_18 = x_42;
x_19 = x_41;
goto block_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = l_Lean_Meta_mkLevelErrorMessage___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_45 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(x_44, x_15, x_8, x_9, x_10, x_11, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_46, x_8, x_9, x_10, x_11, x_47);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_45, 0);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_45);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_15);
x_57 = lean_ctor_get(x_38, 1);
lean_inc(x_57);
lean_dec(x_38);
lean_inc(x_2);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_2);
x_18 = x_58;
x_19 = x_57;
goto block_29;
}
}
else
{
uint8_t x_59; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_38);
if (x_59 == 0)
{
return x_38;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_38, 0);
x_61 = lean_ctor_get(x_38, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_38);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
block_29:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_17)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_17;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
lean_inc(x_3);
if (lean_is_scalar(x_17)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_17;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = x_6 + x_26;
x_6 = x_27;
x_7 = x_25;
x_12 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_11 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2(x_1, x_2, x_4, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_dec(x_3);
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
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_get_size(x_21);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__5(x_1, x_2, x_22, x_21, x_25, x_26, x_23, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_21);
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
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(lean_object* x_1, lean_object* x_2) {
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
x_16 = l_Lean_Meta_getResetPostponed___closed__3;
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
x_23 = l_Lean_Meta_getResetPostponed___closed__3;
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
x_34 = l_Lean_Meta_getResetPostponed___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__9(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_18);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8(x_1, x_2, x_3, x_16, x_18, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_8, 0, x_24);
lean_ctor_set(x_20, 0, x_8);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_8, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_18);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_29);
lean_ctor_set(x_8, 0, x_4);
x_30 = 1;
x_31 = x_7 + x_30;
x_7 = x_31;
x_13 = x_28;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_8);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_37);
lean_inc(x_3);
lean_inc(x_2);
x_38 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8(x_1, x_2, x_3, x_16, x_37, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
lean_dec(x_37);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_inc(x_4);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_46);
x_48 = 1;
x_49 = x_7 + x_48;
x_7 = x_49;
x_8 = x_47;
x_13 = x_45;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_53 = x_38;
} else {
 lean_dec_ref(x_38);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__10(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_17 = x_7;
} else {
 lean_dec_ref(x_7);
 x_17 = lean_box(0);
}
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_15, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_8, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_8, 4);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_37 = l_Lean_Meta_isLevelDefEqAux(x_29, x_30, x_36, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
if (x_1 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_15);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3;
x_18 = x_41;
x_19 = x_40;
goto block_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = l_Lean_Meta_mkLevelErrorMessage___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_44 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(x_43, x_15, x_8, x_9, x_10, x_11, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_45, x_8, x_9, x_10, x_11, x_46);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_15);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
lean_dec(x_37);
lean_inc(x_2);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_2);
x_18 = x_57;
x_19 = x_56;
goto block_28;
}
}
else
{
uint8_t x_58; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_37);
if (x_58 == 0)
{
return x_37;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_37, 0);
x_60 = lean_ctor_get(x_37, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_37);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
block_28:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
lean_inc(x_3);
if (lean_is_scalar(x_17)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_17;
}
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = x_6 + x_25;
x_6 = x_26;
x_7 = x_24;
x_12 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
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
lean_dec(x_11);
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
lean_dec(x_3);
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
lean_dec(x_4);
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
lean_dec(x_34);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__11(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_17 = x_7;
} else {
 lean_dec_ref(x_7);
 x_17 = lean_box(0);
}
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_15, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_8, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_8, 4);
lean_inc(x_36);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_38 = l_Lean_Meta_isLevelDefEqAux(x_30, x_31, x_37, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
if (x_1 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_15);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__3;
x_18 = x_42;
x_19 = x_41;
goto block_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = l_Lean_Meta_mkLevelErrorMessage___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_45 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore(x_44, x_15, x_8, x_9, x_10, x_11, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_46, x_8, x_9, x_10, x_11, x_47);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_45, 0);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_45);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_15);
x_57 = lean_ctor_get(x_38, 1);
lean_inc(x_57);
lean_dec(x_38);
lean_inc(x_2);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_2);
x_18 = x_58;
x_19 = x_57;
goto block_29;
}
}
else
{
uint8_t x_59; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_38);
if (x_59 == 0)
{
return x_38;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_38, 0);
x_61 = lean_ctor_get(x_38, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_38);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
block_29:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_17)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_17;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
lean_inc(x_3);
if (lean_is_scalar(x_17)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_17;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = x_6 + x_26;
x_6 = x_27;
x_7 = x_25;
x_12 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_11 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8(x_1, x_2, x_4, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_dec(x_3);
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
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_get_size(x_21);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__11(x_1, x_2, x_22, x_21, x_25, x_26, x_23, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_21);
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
lean_dec(x_3);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_traceCtx");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_18 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__2;
x_19 = l_Lean_Name_append(x_2, x_18);
x_20 = l_Std_PersistentArray_toArray___rarg(x_16);
x_21 = lean_array_get_size(x_20);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = x_20;
x_25 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_22, x_23, x_24);
x_26 = x_25;
x_27 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Std_PersistentArray_push___rarg(x_1, x_29);
lean_ctor_set(x_11, 0, x_30);
x_31 = lean_st_ref_set(x_7, x_10, x_12);
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
lean_dec(x_16);
lean_dec(x_3);
lean_ctor_set(x_11, 0, x_1);
x_38 = lean_st_ref_set(x_7, x_10, x_12);
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
x_45 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
x_46 = lean_ctor_get(x_11, 0);
lean_inc(x_46);
lean_dec(x_11);
x_47 = l_Std_PersistentArray_isEmpty___rarg(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_48 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__2;
x_49 = l_Lean_Name_append(x_2, x_48);
x_50 = l_Std_PersistentArray_toArray___rarg(x_46);
x_51 = lean_array_get_size(x_50);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = 0;
x_54 = x_50;
x_55 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_52, x_53, x_54);
x_56 = x_55;
x_57 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Std_PersistentArray_push___rarg(x_1, x_59);
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_45);
lean_ctor_set(x_10, 3, x_61);
x_62 = lean_st_ref_set(x_7, x_10, x_12);
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
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_46);
lean_dec(x_3);
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_45);
lean_ctor_set(x_10, 3, x_67);
x_68 = lean_st_ref_set(x_7, x_10, x_12);
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
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_73 = lean_ctor_get(x_10, 0);
x_74 = lean_ctor_get(x_10, 1);
x_75 = lean_ctor_get(x_10, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_10);
x_76 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
x_77 = lean_ctor_get(x_11, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_78 = x_11;
} else {
 lean_dec_ref(x_11);
 x_78 = lean_box(0);
}
x_79 = l_Std_PersistentArray_isEmpty___rarg(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_80 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__2;
x_81 = l_Lean_Name_append(x_2, x_80);
x_82 = l_Std_PersistentArray_toArray___rarg(x_77);
x_83 = lean_array_get_size(x_82);
x_84 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_85 = 0;
x_86 = x_82;
x_87 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_84, x_85, x_86);
x_88 = x_87;
x_89 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_90, 0, x_81);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_3);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Std_PersistentArray_push___rarg(x_1, x_91);
if (lean_is_scalar(x_78)) {
 x_93 = lean_alloc_ctor(0, 1, 1);
} else {
 x_93 = x_78;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_76);
x_94 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_94, 0, x_73);
lean_ctor_set(x_94, 1, x_74);
lean_ctor_set(x_94, 2, x_75);
lean_ctor_set(x_94, 3, x_93);
x_95 = lean_st_ref_set(x_7, x_94, x_12);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_77);
lean_dec(x_3);
if (lean_is_scalar(x_78)) {
 x_100 = lean_alloc_ctor(0, 1, 1);
} else {
 x_100 = x_78;
}
lean_ctor_set(x_100, 0, x_1);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_76);
x_101 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_101, 0, x_73);
lean_ctor_set(x_101, 1, x_74);
lean_ctor_set(x_101, 2, x_75);
lean_ctor_set(x_101, 3, x_100);
x_102 = lean_st_ref_set(x_7, x_101, x_12);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
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
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_99 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_100 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1(x_1, x_99, x_97, x_99, x_2, x_3, x_4, x_5, x_98);
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
x_104 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__5;
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
x_168 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_169 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1(x_1, x_168, x_166, x_168, x_2, x_3, x_4, x_5, x_167);
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
x_173 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__5;
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
x_242 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_243 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1(x_1, x_242, x_240, x_242, x_2, x_3, x_4, x_5, x_241);
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
x_247 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__5;
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
x_267 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_268 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7(x_1, x_267, x_265, x_267, x_2, x_3, x_4, x_5, x_266);
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
x_272 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__5;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Std_PersistentArray_forInAux___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__8(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed_loop___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_processPostponed_loop___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no progress solving pending is-def-eq level constraints");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_processPostponed_loop___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_processPostponed_loop___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed_loop___lambda__2(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = 0;
x_17 = lean_box(x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___rarg(x_7, x_8, x_9, x_22);
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
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_24, x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = lean_nat_dec_lt(x_24, x_2);
lean_dec(x_2);
lean_dec(x_24);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_st_ref_get(x_9, x_25);
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
x_30 = x_48;
x_31 = x_47;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
lean_inc(x_4);
x_50 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_4, x_6, x_7, x_8, x_9, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
x_30 = x_53;
x_31 = x_52;
goto block_42;
}
block_42:
{
if (x_30 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_32 = lean_box(x_3);
if (lean_is_scalar(x_26)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_26;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_26);
x_34 = l_Lean_Meta_processPostponed_loop___lambda__2___closed__2;
x_35 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_4, x_34, x_6, x_7, x_8, x_9, x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(x_3);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_26);
lean_dec(x_4);
x_54 = l_Lean_Meta_processPostponed_loop(x_3, x_1, x_6, x_7, x_8, x_9, x_25);
return x_54;
}
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_55 = 1;
x_56 = lean_box(x_55);
if (lean_is_scalar(x_26)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_26;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_25);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_11);
if (x_58 == 0)
{
return x_11;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_11, 0);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_11);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l_Lean_Meta_processPostponed_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("processing #");
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
x_1 = lean_mk_string(" postponed is-def-eq level constraints");
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
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed_loop(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_free_object(x_8);
x_14 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_31 = lean_st_ref_get(x_6, x_11);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = 0;
x_15 = x_36;
x_16 = x_35;
goto block_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_14, x_3, x_4, x_5, x_6, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unbox(x_39);
lean_dec(x_39);
x_15 = x_41;
x_16 = x_40;
goto block_30;
}
block_30:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Meta_processPostponed_loop___lambda__2(x_2, x_10, x_1, x_14, x_17, x_3, x_4, x_5, x_6, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_10);
x_19 = l_Nat_repr(x_10);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Meta_processPostponed_loop___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Meta_processPostponed_loop___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_14, x_25, x_3, x_4, x_5, x_6, x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_processPostponed_loop___lambda__2(x_2, x_10, x_1, x_14, x_27, x_3, x_4, x_5, x_6, x_28);
return x_29;
}
}
}
else
{
uint8_t x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = 1;
x_43 = lean_box(x_42);
lean_ctor_set(x_8, 0, x_43);
return x_8;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_8);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_44, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_48 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2;
x_65 = lean_st_ref_get(x_6, x_45);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 3);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get_uint8(x_67, sizeof(void*)*1);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = 0;
x_49 = x_70;
x_50 = x_69;
goto block_64;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
x_72 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_48, x_3, x_4, x_5, x_6, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unbox(x_73);
lean_dec(x_73);
x_49 = x_75;
x_50 = x_74;
goto block_64;
}
block_64:
{
if (x_49 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
x_52 = l_Lean_Meta_processPostponed_loop___lambda__2(x_2, x_44, x_1, x_48, x_51, x_3, x_4, x_5, x_6, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_inc(x_44);
x_53 = l_Nat_repr(x_44);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_Meta_processPostponed_loop___closed__2;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Meta_processPostponed_loop___closed__4;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_48, x_59, x_3, x_4, x_5, x_6, x_50);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Meta_processPostponed_loop___lambda__2(x_2, x_44, x_1, x_48, x_61, x_3, x_4, x_5, x_6, x_62);
return x_63;
}
}
}
else
{
uint8_t x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_44);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_76 = 1;
x_77 = lean_box(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_45);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_processPostponed_loop___lambda__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed_loop___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_processPostponed_loop___lambda__2(x_11, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_processPostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; 
x_8 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_getResetPostponed(x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_13);
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
lean_dec(x_12);
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
lean_dec(x_12);
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
x_52 = l_Std_PersistentArray_append___rarg(x_12, x_50);
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
lean_dec(x_12);
x_62 = lean_ctor_get(x_37, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_37, 1);
lean_inc(x_63);
lean_dec(x_37);
x_14 = x_62;
x_15 = x_63;
goto block_21;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_12);
x_64 = lean_ctor_get(x_22, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_dec(x_22);
x_14 = x_64;
x_15 = x_65;
goto block_21;
}
block_21:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_checkpointDefEq(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_9 = l_Lean_Meta_saveState___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_isLevelDefEqAux(x_1, x_2, x_4, x_5, x_6, x_7, x_14);
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
lean_dec(x_13);
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
lean_dec(x_13);
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
x_53 = l_Std_PersistentArray_append___rarg(x_13, x_51);
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
lean_dec(x_13);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
x_15 = x_63;
x_16 = x_64;
goto block_22;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_13);
x_65 = lean_ctor_get(x_23, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_dec(x_23);
x_15 = x_65;
x_16 = x_66;
goto block_22;
}
block_22:
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_9 = l_Lean_Meta_saveState___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_isLevelDefEqAux(x_1, x_2, x_4, x_5, x_6, x_7, x_14);
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
lean_dec(x_13);
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
lean_dec(x_13);
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
x_53 = l_Std_PersistentArray_append___rarg(x_13, x_51);
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
lean_dec(x_13);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
x_15 = x_63;
x_16 = x_64;
goto block_22;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_13);
x_65 = lean_ctor_get(x_23, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_dec(x_23);
x_15 = x_65;
x_16 = x_66;
goto block_22;
}
block_22:
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
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
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_17; lean_object* x_18; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_415 = lean_st_ref_get(x_6, x_7);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_416, 3);
lean_inc(x_417);
lean_dec(x_416);
x_418 = lean_ctor_get_uint8(x_417, sizeof(void*)*1);
lean_dec(x_417);
if (x_418 == 0)
{
lean_object* x_419; uint8_t x_420; 
x_419 = lean_ctor_get(x_415, 1);
lean_inc(x_419);
lean_dec(x_415);
x_420 = 0;
x_17 = x_420;
x_18 = x_419;
goto block_414;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; 
x_421 = lean_ctor_get(x_415, 1);
lean_inc(x_421);
lean_dec(x_415);
x_422 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_423 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_422, x_3, x_4, x_5, x_6, x_421);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
x_426 = lean_unbox(x_424);
lean_dec(x_424);
x_17 = x_426;
x_18 = x_425;
goto block_414;
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
block_414:
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
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_114 = lean_st_ref_get(x_6, x_86);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 3);
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_ctor_get_uint8(x_116, sizeof(void*)*1);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec(x_114);
x_88 = x_31;
x_89 = x_118;
goto block_113;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
lean_dec(x_114);
x_120 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_87, x_3, x_4, x_5, x_6, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_unbox(x_121);
lean_dec(x_121);
x_88 = x_123;
x_89 = x_122;
goto block_113;
}
block_113:
{
if (x_88 == 0)
{
uint8_t x_90; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_unbox(x_85);
lean_dec(x_85);
x_34 = x_90;
x_35 = x_89;
goto block_82;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_91 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_91, 0, x_1);
x_92 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_93 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_96, 0, x_2);
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Meta_isLevelDefEq___closed__2;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_unbox(x_85);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = l_Lean_Meta_isLevelDefEq___closed__4;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_92);
x_104 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_87, x_103, x_3, x_4, x_5, x_6, x_89);
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
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_107 = l_Lean_Meta_isLevelDefEq___closed__6;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_99);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_92);
x_110 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_87, x_109, x_3, x_4, x_5, x_6, x_89);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_unbox(x_85);
lean_dec(x_85);
x_34 = x_112;
x_35 = x_111;
goto block_82;
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = lean_ctor_get(x_84, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_84, 1);
lean_inc(x_125);
lean_dec(x_84);
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
x_132 = !lean_is_exclusive(x_129);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_129, 3);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_130);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_23);
x_135 = lean_st_ref_set(x_6, x_129, x_131);
lean_dec(x_6);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_dec(x_137);
lean_ctor_set_tag(x_135, 1);
lean_ctor_set(x_135, 0, x_124);
return x_135;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_124);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_130, 0);
lean_inc(x_140);
lean_dec(x_130);
x_141 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set_uint8(x_141, sizeof(void*)*1, x_23);
lean_ctor_set(x_129, 3, x_141);
x_142 = lean_st_ref_set(x_6, x_129, x_131);
lean_dec(x_6);
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
lean_ctor_set(x_145, 0, x_124);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_146 = lean_ctor_get(x_129, 0);
x_147 = lean_ctor_get(x_129, 1);
x_148 = lean_ctor_get(x_129, 2);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_129);
x_149 = lean_ctor_get(x_130, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_150 = x_130;
} else {
 lean_dec_ref(x_130);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_23);
x_152 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_152, 0, x_146);
lean_ctor_set(x_152, 1, x_147);
lean_ctor_set(x_152, 2, x_148);
lean_ctor_set(x_152, 3, x_151);
x_153 = lean_st_ref_set(x_6, x_152, x_131);
lean_dec(x_6);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
 lean_ctor_set_tag(x_156, 1);
}
lean_ctor_set(x_156, 0, x_124);
lean_ctor_set(x_156, 1, x_154);
return x_156;
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
lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; uint8_t x_189; lean_object* x_190; 
x_157 = lean_ctor_get(x_26, 0);
lean_inc(x_157);
lean_dec(x_26);
x_158 = 0;
x_159 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_158);
lean_ctor_set(x_25, 3, x_159);
x_160 = lean_st_ref_set(x_6, x_25, x_27);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_189 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_190 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1, x_2, x_189, x_3, x_4, x_5, x_6, x_161);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_220 = lean_st_ref_get(x_6, x_192);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_221, 3);
lean_inc(x_222);
lean_dec(x_221);
x_223 = lean_ctor_get_uint8(x_222, sizeof(void*)*1);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_220, 1);
lean_inc(x_224);
lean_dec(x_220);
x_194 = x_158;
x_195 = x_224;
goto block_219;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_225 = lean_ctor_get(x_220, 1);
lean_inc(x_225);
lean_dec(x_220);
x_226 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_193, x_3, x_4, x_5, x_6, x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_unbox(x_227);
lean_dec(x_227);
x_194 = x_229;
x_195 = x_228;
goto block_219;
}
block_219:
{
if (x_194 == 0)
{
uint8_t x_196; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = lean_unbox(x_191);
lean_dec(x_191);
x_162 = x_196;
x_163 = x_195;
goto block_188;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_197 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_197, 0, x_1);
x_198 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_199 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_201 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_202, 0, x_2);
x_203 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Lean_Meta_isLevelDefEq___closed__2;
x_205 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_unbox(x_191);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_207 = l_Lean_Meta_isLevelDefEq___closed__4;
x_208 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_198);
x_210 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_193, x_209, x_3, x_4, x_5, x_6, x_195);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_unbox(x_191);
lean_dec(x_191);
x_162 = x_212;
x_163 = x_211;
goto block_188;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_213 = l_Lean_Meta_isLevelDefEq___closed__6;
x_214 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_214, 0, x_205);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_198);
x_216 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_193, x_215, x_3, x_4, x_5, x_6, x_195);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_unbox(x_191);
lean_dec(x_191);
x_162 = x_218;
x_163 = x_217;
goto block_188;
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_230 = lean_ctor_get(x_190, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_190, 1);
lean_inc(x_231);
lean_dec(x_190);
x_232 = lean_st_ref_get(x_6, x_231);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_234 = lean_st_ref_take(x_6, x_233);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_235, 3);
lean_inc(x_236);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_238 = lean_ctor_get(x_235, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_235, 2);
lean_inc(x_240);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_241 = x_235;
} else {
 lean_dec_ref(x_235);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_236, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 x_243 = x_236;
} else {
 lean_dec_ref(x_236);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(0, 1, 1);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set_uint8(x_244, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_241)) {
 x_245 = lean_alloc_ctor(0, 4, 0);
} else {
 x_245 = x_241;
}
lean_ctor_set(x_245, 0, x_238);
lean_ctor_set(x_245, 1, x_239);
lean_ctor_set(x_245, 2, x_240);
lean_ctor_set(x_245, 3, x_244);
x_246 = lean_st_ref_set(x_6, x_245, x_237);
lean_dec(x_6);
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
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
 lean_ctor_set_tag(x_249, 1);
}
lean_ctor_set(x_249, 0, x_230);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
block_188:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_164 = lean_st_ref_get(x_6, x_163);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_ctor_get(x_165, 3);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get_uint8(x_167, sizeof(void*)*1);
lean_dec(x_167);
x_169 = lean_st_ref_take(x_6, x_166);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_170, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_ctor_get(x_170, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_170, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_170, 2);
lean_inc(x_175);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 x_176 = x_170;
} else {
 lean_dec_ref(x_170);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_171, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_178 = x_171;
} else {
 lean_dec_ref(x_171);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 1, 1);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set_uint8(x_179, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_176)) {
 x_180 = lean_alloc_ctor(0, 4, 0);
} else {
 x_180 = x_176;
}
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_174);
lean_ctor_set(x_180, 2, x_175);
lean_ctor_set(x_180, 3, x_179);
x_181 = lean_st_ref_set(x_6, x_180, x_172);
lean_dec(x_6);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_183 = x_181;
} else {
 lean_dec_ref(x_181);
 x_183 = lean_box(0);
}
x_184 = lean_box(x_162);
x_185 = lean_box(x_168);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
if (lean_is_scalar(x_183)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_183;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_182);
x_8 = x_187;
goto block_16;
}
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; uint8_t x_287; lean_object* x_288; 
x_250 = lean_ctor_get(x_25, 0);
x_251 = lean_ctor_get(x_25, 1);
x_252 = lean_ctor_get(x_25, 2);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_25);
x_253 = lean_ctor_get(x_26, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_254 = x_26;
} else {
 lean_dec_ref(x_26);
 x_254 = lean_box(0);
}
x_255 = 0;
if (lean_is_scalar(x_254)) {
 x_256 = lean_alloc_ctor(0, 1, 1);
} else {
 x_256 = x_254;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set_uint8(x_256, sizeof(void*)*1, x_255);
x_257 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_257, 0, x_250);
lean_ctor_set(x_257, 1, x_251);
lean_ctor_set(x_257, 2, x_252);
lean_ctor_set(x_257, 3, x_256);
x_258 = lean_st_ref_set(x_6, x_257, x_27);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec(x_258);
x_287 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_288 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1, x_2, x_287, x_3, x_4, x_5, x_6, x_259);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_291 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_318 = lean_st_ref_get(x_6, x_290);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_319, 3);
lean_inc(x_320);
lean_dec(x_319);
x_321 = lean_ctor_get_uint8(x_320, sizeof(void*)*1);
lean_dec(x_320);
if (x_321 == 0)
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
lean_dec(x_318);
x_292 = x_255;
x_293 = x_322;
goto block_317;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_323 = lean_ctor_get(x_318, 1);
lean_inc(x_323);
lean_dec(x_318);
x_324 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_291, x_3, x_4, x_5, x_6, x_323);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = lean_unbox(x_325);
lean_dec(x_325);
x_292 = x_327;
x_293 = x_326;
goto block_317;
}
block_317:
{
if (x_292 == 0)
{
uint8_t x_294; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_294 = lean_unbox(x_289);
lean_dec(x_289);
x_260 = x_294;
x_261 = x_293;
goto block_286;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_295 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_295, 0, x_1);
x_296 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_297 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_295);
x_298 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_299 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_300, 0, x_2);
x_301 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Lean_Meta_isLevelDefEq___closed__2;
x_303 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_unbox(x_289);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_305 = l_Lean_Meta_isLevelDefEq___closed__4;
x_306 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_296);
x_308 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_291, x_307, x_3, x_4, x_5, x_6, x_293);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
lean_dec(x_308);
x_310 = lean_unbox(x_289);
lean_dec(x_289);
x_260 = x_310;
x_261 = x_309;
goto block_286;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_311 = l_Lean_Meta_isLevelDefEq___closed__6;
x_312 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_312, 0, x_303);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_296);
x_314 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_291, x_313, x_3, x_4, x_5, x_6, x_293);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
lean_dec(x_314);
x_316 = lean_unbox(x_289);
lean_dec(x_289);
x_260 = x_316;
x_261 = x_315;
goto block_286;
}
}
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_328 = lean_ctor_get(x_288, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_288, 1);
lean_inc(x_329);
lean_dec(x_288);
x_330 = lean_st_ref_get(x_6, x_329);
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
lean_dec(x_330);
x_332 = lean_st_ref_take(x_6, x_331);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_333, 3);
lean_inc(x_334);
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
lean_dec(x_332);
x_336 = lean_ctor_get(x_333, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_333, 1);
lean_inc(x_337);
x_338 = lean_ctor_get(x_333, 2);
lean_inc(x_338);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 lean_ctor_release(x_333, 2);
 lean_ctor_release(x_333, 3);
 x_339 = x_333;
} else {
 lean_dec_ref(x_333);
 x_339 = lean_box(0);
}
x_340 = lean_ctor_get(x_334, 0);
lean_inc(x_340);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 x_341 = x_334;
} else {
 lean_dec_ref(x_334);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(0, 1, 1);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set_uint8(x_342, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_339)) {
 x_343 = lean_alloc_ctor(0, 4, 0);
} else {
 x_343 = x_339;
}
lean_ctor_set(x_343, 0, x_336);
lean_ctor_set(x_343, 1, x_337);
lean_ctor_set(x_343, 2, x_338);
lean_ctor_set(x_343, 3, x_342);
x_344 = lean_st_ref_set(x_6, x_343, x_335);
lean_dec(x_6);
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_346 = x_344;
} else {
 lean_dec_ref(x_344);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 2, 0);
} else {
 x_347 = x_346;
 lean_ctor_set_tag(x_347, 1);
}
lean_ctor_set(x_347, 0, x_328);
lean_ctor_set(x_347, 1, x_345);
return x_347;
}
block_286:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_262 = lean_st_ref_get(x_6, x_261);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_ctor_get(x_263, 3);
lean_inc(x_265);
lean_dec(x_263);
x_266 = lean_ctor_get_uint8(x_265, sizeof(void*)*1);
lean_dec(x_265);
x_267 = lean_st_ref_take(x_6, x_264);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_268, 3);
lean_inc(x_269);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
lean_dec(x_267);
x_271 = lean_ctor_get(x_268, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_268, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_268, 2);
lean_inc(x_273);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 lean_ctor_release(x_268, 2);
 lean_ctor_release(x_268, 3);
 x_274 = x_268;
} else {
 lean_dec_ref(x_268);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_269, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 x_276 = x_269;
} else {
 lean_dec_ref(x_269);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 1, 1);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set_uint8(x_277, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_274)) {
 x_278 = lean_alloc_ctor(0, 4, 0);
} else {
 x_278 = x_274;
}
lean_ctor_set(x_278, 0, x_271);
lean_ctor_set(x_278, 1, x_272);
lean_ctor_set(x_278, 2, x_273);
lean_ctor_set(x_278, 3, x_277);
x_279 = lean_st_ref_set(x_6, x_278, x_270);
lean_dec(x_6);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_281 = x_279;
} else {
 lean_dec_ref(x_279);
 x_281 = lean_box(0);
}
x_282 = lean_box(x_260);
x_283 = lean_box(x_266);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
if (lean_is_scalar(x_281)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_281;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_280);
x_8 = x_285;
goto block_16;
}
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; 
x_348 = lean_ctor_get(x_5, 3);
lean_inc(x_348);
x_349 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(x_6, x_18);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_353 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__2(x_1, x_2, x_352, x_3, x_4, x_5, x_6, x_351);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_395 = lean_st_ref_get(x_6, x_355);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_396, 3);
lean_inc(x_397);
lean_dec(x_396);
x_398 = lean_ctor_get_uint8(x_397, sizeof(void*)*1);
lean_dec(x_397);
if (x_398 == 0)
{
lean_object* x_399; uint8_t x_400; 
x_399 = lean_ctor_get(x_395, 1);
lean_inc(x_399);
lean_dec(x_395);
x_400 = 0;
x_357 = x_400;
x_358 = x_399;
goto block_394;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_401 = lean_ctor_get(x_395, 1);
lean_inc(x_401);
lean_dec(x_395);
x_402 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_356, x_3, x_4, x_5, x_6, x_401);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_unbox(x_403);
lean_dec(x_403);
x_357 = x_405;
x_358 = x_404;
goto block_394;
}
block_394:
{
if (x_357 == 0)
{
lean_object* x_359; uint8_t x_360; 
lean_dec(x_2);
lean_dec(x_1);
x_359 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_350, x_356, x_348, x_3, x_4, x_5, x_6, x_358);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_360 = !lean_is_exclusive(x_359);
if (x_360 == 0)
{
lean_object* x_361; 
x_361 = lean_ctor_get(x_359, 0);
lean_dec(x_361);
lean_ctor_set(x_359, 0, x_354);
return x_359;
}
else
{
lean_object* x_362; lean_object* x_363; 
x_362 = lean_ctor_get(x_359, 1);
lean_inc(x_362);
lean_dec(x_359);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_354);
lean_ctor_set(x_363, 1, x_362);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_364 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_364, 0, x_1);
x_365 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_366 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_364);
x_367 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_368 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
x_369 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_369, 0, x_2);
x_370 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
x_371 = l_Lean_Meta_isLevelDefEq___closed__2;
x_372 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_unbox(x_354);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; 
x_374 = l_Lean_Meta_isLevelDefEq___closed__4;
x_375 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_374);
x_376 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_365);
x_377 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_356, x_376, x_3, x_4, x_5, x_6, x_358);
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
lean_dec(x_377);
x_379 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_350, x_356, x_348, x_3, x_4, x_5, x_6, x_378);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_380 = !lean_is_exclusive(x_379);
if (x_380 == 0)
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_379, 0);
lean_dec(x_381);
lean_ctor_set(x_379, 0, x_354);
return x_379;
}
else
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_379, 1);
lean_inc(x_382);
lean_dec(x_379);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_354);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; 
x_384 = l_Lean_Meta_isLevelDefEq___closed__6;
x_385 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_385, 0, x_372);
lean_ctor_set(x_385, 1, x_384);
x_386 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_365);
x_387 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_356, x_386, x_3, x_4, x_5, x_6, x_358);
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
x_389 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_350, x_356, x_348, x_3, x_4, x_5, x_6, x_388);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_390 = !lean_is_exclusive(x_389);
if (x_390 == 0)
{
lean_object* x_391; 
x_391 = lean_ctor_get(x_389, 0);
lean_dec(x_391);
lean_ctor_set(x_389, 0, x_354);
return x_389;
}
else
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_ctor_get(x_389, 1);
lean_inc(x_392);
lean_dec(x_389);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_354);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
}
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; 
lean_dec(x_2);
lean_dec(x_1);
x_406 = lean_ctor_get(x_353, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_353, 1);
lean_inc(x_407);
lean_dec(x_353);
x_408 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_409 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_350, x_408, x_348, x_3, x_4, x_5, x_6, x_407);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_410 = !lean_is_exclusive(x_409);
if (x_410 == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_409, 0);
lean_dec(x_411);
lean_ctor_set_tag(x_409, 1);
lean_ctor_set(x_409, 0, x_406);
return x_409;
}
else
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_409, 1);
lean_inc(x_412);
lean_dec(x_409);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_406);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_9 = l_Lean_Meta_saveState___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = lean_is_expr_def_eq(x_1, x_2, x_4, x_5, x_6, x_7, x_14);
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
lean_dec(x_13);
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
lean_dec(x_13);
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
x_53 = l_Std_PersistentArray_append___rarg(x_13, x_51);
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
lean_dec(x_13);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
x_15 = x_63;
x_16 = x_64;
goto block_22;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_13);
x_65 = lean_ctor_get(x_23, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_dec(x_23);
x_15 = x_65;
x_16 = x_66;
goto block_22;
}
block_22:
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_9 = l_Lean_Meta_saveState___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = lean_is_expr_def_eq(x_1, x_2, x_4, x_5, x_6, x_7, x_14);
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
lean_dec(x_13);
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
lean_dec(x_13);
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
x_53 = l_Std_PersistentArray_append___rarg(x_13, x_51);
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
lean_dec(x_13);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
x_15 = x_63;
x_16 = x_64;
goto block_22;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_13);
x_65 = lean_ctor_get(x_23, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_dec(x_23);
x_15 = x_65;
x_16 = x_66;
goto block_22;
}
block_22:
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
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
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__2;
x_2 = l_Lean_Meta_isExprDefEq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isExprDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_17; lean_object* x_18; lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; 
x_512 = lean_st_ref_get(x_6, x_7);
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_513, 3);
lean_inc(x_514);
lean_dec(x_513);
x_515 = lean_ctor_get_uint8(x_514, sizeof(void*)*1);
lean_dec(x_514);
if (x_515 == 0)
{
lean_object* x_516; uint8_t x_517; 
x_516 = lean_ctor_get(x_512, 1);
lean_inc(x_516);
lean_dec(x_512);
x_517 = 0;
x_17 = x_517;
x_18 = x_516;
goto block_511;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; uint8_t x_523; 
x_518 = lean_ctor_get(x_512, 1);
lean_inc(x_518);
lean_dec(x_512);
x_519 = l_Lean_Meta_isExprDefEq___closed__2;
x_520 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_519, x_3, x_4, x_5, x_6, x_518);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_520, 1);
lean_inc(x_522);
lean_dec(x_520);
x_523 = lean_unbox(x_521);
lean_dec(x_521);
x_17 = x_523;
x_18 = x_522;
goto block_511;
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
block_511:
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
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Meta_isExprDefEq___closed__2;
x_120 = lean_st_ref_get(x_6, x_92);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_121, 3);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_ctor_get_uint8(x_122, sizeof(void*)*1);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_dec(x_120);
x_94 = x_31;
x_95 = x_124;
goto block_119;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_dec(x_120);
x_126 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_93, x_3, x_4, x_5, x_6, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_unbox(x_127);
lean_dec(x_127);
x_94 = x_129;
x_95 = x_128;
goto block_119;
}
block_119:
{
if (x_94 == 0)
{
uint8_t x_96; 
lean_dec(x_3);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_unbox(x_91);
lean_dec(x_91);
x_34 = x_96;
x_35 = x_95;
goto block_82;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_1);
x_98 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_2);
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_Meta_isLevelDefEq___closed__2;
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_unbox(x_91);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_107 = l_Lean_Meta_isLevelDefEq___closed__4;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_98);
x_110 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_93, x_109, x_3, x_4, x_5, x_6, x_95);
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
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_113 = l_Lean_Meta_isLevelDefEq___closed__6;
x_114 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_98);
x_116 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_93, x_115, x_3, x_4, x_5, x_6, x_95);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_unbox(x_91);
lean_dec(x_91);
x_34 = x_118;
x_35 = x_117;
goto block_82;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_3);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_130 = lean_ctor_get(x_90, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_90, 1);
lean_inc(x_131);
lean_dec(x_90);
x_132 = lean_st_ref_get(x_6, x_131);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_st_ref_take(x_6, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = !lean_is_exclusive(x_135);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_135, 3);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_136);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_23);
x_141 = lean_st_ref_set(x_6, x_135, x_137);
lean_dec(x_6);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_141, 0);
lean_dec(x_143);
lean_ctor_set_tag(x_141, 1);
lean_ctor_set(x_141, 0, x_130);
return x_141;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_130);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_136, 0);
lean_inc(x_146);
lean_dec(x_136);
x_147 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_23);
lean_ctor_set(x_135, 3, x_147);
x_148 = lean_st_ref_set(x_6, x_135, x_137);
lean_dec(x_6);
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
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_130);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_152 = lean_ctor_get(x_135, 0);
x_153 = lean_ctor_get(x_135, 1);
x_154 = lean_ctor_get(x_135, 2);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_135);
x_155 = lean_ctor_get(x_136, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_156 = x_136;
} else {
 lean_dec_ref(x_136);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 1, 1);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_23);
x_158 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_153);
lean_ctor_set(x_158, 2, x_154);
lean_ctor_set(x_158, 3, x_157);
x_159 = lean_st_ref_set(x_6, x_158, x_137);
lean_dec(x_6);
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
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
 lean_ctor_set_tag(x_162, 1);
}
lean_ctor_set(x_162, 0, x_130);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; 
x_163 = lean_ctor_get(x_3, 0);
x_164 = lean_ctor_get(x_3, 1);
x_165 = lean_ctor_get(x_3, 2);
x_166 = lean_ctor_get(x_3, 4);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_3);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_2);
lean_inc(x_1);
x_167 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_167, 0, x_1);
lean_ctor_set(x_167, 1, x_2);
lean_ctor_set(x_167, 2, x_164);
lean_ctor_set(x_167, 3, x_165);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_169, 0, x_163);
lean_ctor_set(x_169, 1, x_164);
lean_ctor_set(x_169, 2, x_165);
lean_ctor_set(x_169, 3, x_168);
lean_ctor_set(x_169, 4, x_166);
x_170 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_169);
lean_inc(x_2);
lean_inc(x_1);
x_171 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(x_1, x_2, x_170, x_169, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Lean_Meta_isExprDefEq___closed__2;
x_201 = lean_st_ref_get(x_6, x_173);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_202, 3);
lean_inc(x_203);
lean_dec(x_202);
x_204 = lean_ctor_get_uint8(x_203, sizeof(void*)*1);
lean_dec(x_203);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
lean_dec(x_201);
x_175 = x_31;
x_176 = x_205;
goto block_200;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
lean_dec(x_201);
x_207 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_174, x_169, x_4, x_5, x_6, x_206);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_unbox(x_208);
lean_dec(x_208);
x_175 = x_210;
x_176 = x_209;
goto block_200;
}
block_200:
{
if (x_175 == 0)
{
uint8_t x_177; 
lean_dec(x_169);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_unbox(x_172);
lean_dec(x_172);
x_34 = x_177;
x_35 = x_176;
goto block_82;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_178 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_178, 0, x_1);
x_179 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_180 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
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
x_187 = lean_unbox(x_172);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_188 = l_Lean_Meta_isLevelDefEq___closed__4;
x_189 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_179);
x_191 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_174, x_190, x_169, x_4, x_5, x_6, x_176);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_169);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = lean_unbox(x_172);
lean_dec(x_172);
x_34 = x_193;
x_35 = x_192;
goto block_82;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_194 = l_Lean_Meta_isLevelDefEq___closed__6;
x_195 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_195, 0, x_186);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_179);
x_197 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_174, x_196, x_169, x_4, x_5, x_6, x_176);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_169);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_unbox(x_172);
lean_dec(x_172);
x_34 = x_199;
x_35 = x_198;
goto block_82;
}
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_169);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_211 = lean_ctor_get(x_171, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_171, 1);
lean_inc(x_212);
lean_dec(x_171);
x_213 = lean_st_ref_get(x_6, x_212);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_215 = lean_st_ref_take(x_6, x_214);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_216, 3);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_dec(x_215);
x_219 = lean_ctor_get(x_216, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_216, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_216, 2);
lean_inc(x_221);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 lean_ctor_release(x_216, 3);
 x_222 = x_216;
} else {
 lean_dec_ref(x_216);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_217, 0);
lean_inc(x_223);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_224 = x_217;
} else {
 lean_dec_ref(x_217);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(0, 1, 1);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set_uint8(x_225, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_222)) {
 x_226 = lean_alloc_ctor(0, 4, 0);
} else {
 x_226 = x_222;
}
lean_ctor_set(x_226, 0, x_219);
lean_ctor_set(x_226, 1, x_220);
lean_ctor_set(x_226, 2, x_221);
lean_ctor_set(x_226, 3, x_225);
x_227 = lean_st_ref_set(x_6, x_226, x_218);
lean_dec(x_6);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
 lean_ctor_set_tag(x_230, 1);
}
lean_ctor_set(x_230, 0, x_211);
lean_ctor_set(x_230, 1, x_228);
return x_230;
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
lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; 
x_231 = lean_ctor_get(x_26, 0);
lean_inc(x_231);
lean_dec(x_26);
x_232 = 0;
x_233 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set_uint8(x_233, sizeof(void*)*1, x_232);
lean_ctor_set(x_25, 3, x_233);
x_234 = lean_st_ref_set(x_6, x_25, x_27);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec(x_234);
x_263 = lean_ctor_get(x_3, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_3, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_3, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_3, 4);
lean_inc(x_266);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_267 = x_3;
} else {
 lean_dec_ref(x_3);
 x_267 = lean_box(0);
}
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_2);
lean_inc(x_1);
x_268 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_268, 0, x_1);
lean_ctor_set(x_268, 1, x_2);
lean_ctor_set(x_268, 2, x_264);
lean_ctor_set(x_268, 3, x_265);
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_268);
if (lean_is_scalar(x_267)) {
 x_270 = lean_alloc_ctor(0, 5, 0);
} else {
 x_270 = x_267;
}
lean_ctor_set(x_270, 0, x_263);
lean_ctor_set(x_270, 1, x_264);
lean_ctor_set(x_270, 2, x_265);
lean_ctor_set(x_270, 3, x_269);
lean_ctor_set(x_270, 4, x_266);
x_271 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_270);
lean_inc(x_2);
lean_inc(x_1);
x_272 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(x_1, x_2, x_271, x_270, x_4, x_5, x_6, x_235);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_275 = l_Lean_Meta_isExprDefEq___closed__2;
x_302 = lean_st_ref_get(x_6, x_274);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_303, 3);
lean_inc(x_304);
lean_dec(x_303);
x_305 = lean_ctor_get_uint8(x_304, sizeof(void*)*1);
lean_dec(x_304);
if (x_305 == 0)
{
lean_object* x_306; 
x_306 = lean_ctor_get(x_302, 1);
lean_inc(x_306);
lean_dec(x_302);
x_276 = x_232;
x_277 = x_306;
goto block_301;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_307 = lean_ctor_get(x_302, 1);
lean_inc(x_307);
lean_dec(x_302);
x_308 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_275, x_270, x_4, x_5, x_6, x_307);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_unbox(x_309);
lean_dec(x_309);
x_276 = x_311;
x_277 = x_310;
goto block_301;
}
block_301:
{
if (x_276 == 0)
{
uint8_t x_278; 
lean_dec(x_270);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_278 = lean_unbox(x_273);
lean_dec(x_273);
x_236 = x_278;
x_237 = x_277;
goto block_262;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_279 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_279, 0, x_1);
x_280 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_281 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_279);
x_282 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_283 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_284, 0, x_2);
x_285 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
x_286 = l_Lean_Meta_isLevelDefEq___closed__2;
x_287 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_unbox(x_273);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_289 = l_Lean_Meta_isLevelDefEq___closed__4;
x_290 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_280);
x_292 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_275, x_291, x_270, x_4, x_5, x_6, x_277);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_270);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec(x_292);
x_294 = lean_unbox(x_273);
lean_dec(x_273);
x_236 = x_294;
x_237 = x_293;
goto block_262;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_295 = l_Lean_Meta_isLevelDefEq___closed__6;
x_296 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_296, 0, x_287);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_280);
x_298 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_275, x_297, x_270, x_4, x_5, x_6, x_277);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_270);
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
x_300 = lean_unbox(x_273);
lean_dec(x_273);
x_236 = x_300;
x_237 = x_299;
goto block_262;
}
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_270);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_312 = lean_ctor_get(x_272, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_272, 1);
lean_inc(x_313);
lean_dec(x_272);
x_314 = lean_st_ref_get(x_6, x_313);
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
lean_dec(x_314);
x_316 = lean_st_ref_take(x_6, x_315);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_317, 3);
lean_inc(x_318);
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
lean_dec(x_316);
x_320 = lean_ctor_get(x_317, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_317, 1);
lean_inc(x_321);
x_322 = lean_ctor_get(x_317, 2);
lean_inc(x_322);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 lean_ctor_release(x_317, 2);
 lean_ctor_release(x_317, 3);
 x_323 = x_317;
} else {
 lean_dec_ref(x_317);
 x_323 = lean_box(0);
}
x_324 = lean_ctor_get(x_318, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 x_325 = x_318;
} else {
 lean_dec_ref(x_318);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(0, 1, 1);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set_uint8(x_326, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_323)) {
 x_327 = lean_alloc_ctor(0, 4, 0);
} else {
 x_327 = x_323;
}
lean_ctor_set(x_327, 0, x_320);
lean_ctor_set(x_327, 1, x_321);
lean_ctor_set(x_327, 2, x_322);
lean_ctor_set(x_327, 3, x_326);
x_328 = lean_st_ref_set(x_6, x_327, x_319);
lean_dec(x_6);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_330 = x_328;
} else {
 lean_dec_ref(x_328);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
 lean_ctor_set_tag(x_331, 1);
}
lean_ctor_set(x_331, 0, x_312);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
block_262:
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_238 = lean_st_ref_get(x_6, x_237);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_ctor_get(x_239, 3);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_ctor_get_uint8(x_241, sizeof(void*)*1);
lean_dec(x_241);
x_243 = lean_st_ref_take(x_6, x_240);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_244, 3);
lean_inc(x_245);
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
lean_dec(x_243);
x_247 = lean_ctor_get(x_244, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_244, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_244, 2);
lean_inc(x_249);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 lean_ctor_release(x_244, 2);
 lean_ctor_release(x_244, 3);
 x_250 = x_244;
} else {
 lean_dec_ref(x_244);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_245, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 x_252 = x_245;
} else {
 lean_dec_ref(x_245);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(0, 1, 1);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set_uint8(x_253, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_250)) {
 x_254 = lean_alloc_ctor(0, 4, 0);
} else {
 x_254 = x_250;
}
lean_ctor_set(x_254, 0, x_247);
lean_ctor_set(x_254, 1, x_248);
lean_ctor_set(x_254, 2, x_249);
lean_ctor_set(x_254, 3, x_253);
x_255 = lean_st_ref_set(x_6, x_254, x_246);
lean_dec(x_6);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_257 = x_255;
} else {
 lean_dec_ref(x_255);
 x_257 = lean_box(0);
}
x_258 = lean_box(x_236);
x_259 = lean_box(x_242);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
if (lean_is_scalar(x_257)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_257;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_256);
x_8 = x_261;
goto block_16;
}
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; 
x_332 = lean_ctor_get(x_25, 0);
x_333 = lean_ctor_get(x_25, 1);
x_334 = lean_ctor_get(x_25, 2);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_25);
x_335 = lean_ctor_get(x_26, 0);
lean_inc(x_335);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_336 = x_26;
} else {
 lean_dec_ref(x_26);
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
x_339 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_339, 0, x_332);
lean_ctor_set(x_339, 1, x_333);
lean_ctor_set(x_339, 2, x_334);
lean_ctor_set(x_339, 3, x_338);
x_340 = lean_st_ref_set(x_6, x_339, x_27);
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
lean_dec(x_340);
x_369 = lean_ctor_get(x_3, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_3, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_3, 2);
lean_inc(x_371);
x_372 = lean_ctor_get(x_3, 4);
lean_inc(x_372);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_373 = x_3;
} else {
 lean_dec_ref(x_3);
 x_373 = lean_box(0);
}
lean_inc(x_371);
lean_inc(x_370);
lean_inc(x_2);
lean_inc(x_1);
x_374 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_374, 0, x_1);
lean_ctor_set(x_374, 1, x_2);
lean_ctor_set(x_374, 2, x_370);
lean_ctor_set(x_374, 3, x_371);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_374);
if (lean_is_scalar(x_373)) {
 x_376 = lean_alloc_ctor(0, 5, 0);
} else {
 x_376 = x_373;
}
lean_ctor_set(x_376, 0, x_369);
lean_ctor_set(x_376, 1, x_370);
lean_ctor_set(x_376, 2, x_371);
lean_ctor_set(x_376, 3, x_375);
lean_ctor_set(x_376, 4, x_372);
x_377 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_376);
lean_inc(x_2);
lean_inc(x_1);
x_378 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(x_1, x_2, x_377, x_376, x_4, x_5, x_6, x_341);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = l_Lean_Meta_isExprDefEq___closed__2;
x_408 = lean_st_ref_get(x_6, x_380);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_409, 3);
lean_inc(x_410);
lean_dec(x_409);
x_411 = lean_ctor_get_uint8(x_410, sizeof(void*)*1);
lean_dec(x_410);
if (x_411 == 0)
{
lean_object* x_412; 
x_412 = lean_ctor_get(x_408, 1);
lean_inc(x_412);
lean_dec(x_408);
x_382 = x_337;
x_383 = x_412;
goto block_407;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_413 = lean_ctor_get(x_408, 1);
lean_inc(x_413);
lean_dec(x_408);
x_414 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_381, x_376, x_4, x_5, x_6, x_413);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = lean_unbox(x_415);
lean_dec(x_415);
x_382 = x_417;
x_383 = x_416;
goto block_407;
}
block_407:
{
if (x_382 == 0)
{
uint8_t x_384; 
lean_dec(x_376);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_384 = lean_unbox(x_379);
lean_dec(x_379);
x_342 = x_384;
x_343 = x_383;
goto block_368;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; 
x_385 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_385, 0, x_1);
x_386 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_387 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_385);
x_388 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_389 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_390, 0, x_2);
x_391 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
x_392 = l_Lean_Meta_isLevelDefEq___closed__2;
x_393 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
x_394 = lean_unbox(x_379);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
x_395 = l_Lean_Meta_isLevelDefEq___closed__4;
x_396 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_395);
x_397 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_386);
x_398 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_381, x_397, x_376, x_4, x_5, x_6, x_383);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_376);
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
lean_dec(x_398);
x_400 = lean_unbox(x_379);
lean_dec(x_379);
x_342 = x_400;
x_343 = x_399;
goto block_368;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_401 = l_Lean_Meta_isLevelDefEq___closed__6;
x_402 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_402, 0, x_393);
lean_ctor_set(x_402, 1, x_401);
x_403 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_386);
x_404 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_381, x_403, x_376, x_4, x_5, x_6, x_383);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_376);
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
lean_dec(x_404);
x_406 = lean_unbox(x_379);
lean_dec(x_379);
x_342 = x_406;
x_343 = x_405;
goto block_368;
}
}
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_376);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_418 = lean_ctor_get(x_378, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_378, 1);
lean_inc(x_419);
lean_dec(x_378);
x_420 = lean_st_ref_get(x_6, x_419);
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
lean_dec(x_420);
x_422 = lean_st_ref_take(x_6, x_421);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_423, 3);
lean_inc(x_424);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
lean_dec(x_422);
x_426 = lean_ctor_get(x_423, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_423, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_423, 2);
lean_inc(x_428);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 lean_ctor_release(x_423, 2);
 lean_ctor_release(x_423, 3);
 x_429 = x_423;
} else {
 lean_dec_ref(x_423);
 x_429 = lean_box(0);
}
x_430 = lean_ctor_get(x_424, 0);
lean_inc(x_430);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 x_431 = x_424;
} else {
 lean_dec_ref(x_424);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(0, 1, 1);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set_uint8(x_432, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_429)) {
 x_433 = lean_alloc_ctor(0, 4, 0);
} else {
 x_433 = x_429;
}
lean_ctor_set(x_433, 0, x_426);
lean_ctor_set(x_433, 1, x_427);
lean_ctor_set(x_433, 2, x_428);
lean_ctor_set(x_433, 3, x_432);
x_434 = lean_st_ref_set(x_6, x_433, x_425);
lean_dec(x_6);
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_436 = x_434;
} else {
 lean_dec_ref(x_434);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_436;
 lean_ctor_set_tag(x_437, 1);
}
lean_ctor_set(x_437, 0, x_418);
lean_ctor_set(x_437, 1, x_435);
return x_437;
}
block_368:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_344 = lean_st_ref_get(x_6, x_343);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
x_347 = lean_ctor_get(x_345, 3);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_ctor_get_uint8(x_347, sizeof(void*)*1);
lean_dec(x_347);
x_349 = lean_st_ref_take(x_6, x_346);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_350, 3);
lean_inc(x_351);
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
lean_dec(x_349);
x_353 = lean_ctor_get(x_350, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_350, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_350, 2);
lean_inc(x_355);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_356 = x_350;
} else {
 lean_dec_ref(x_350);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_351, 0);
lean_inc(x_357);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 x_358 = x_351;
} else {
 lean_dec_ref(x_351);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(0, 1, 1);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set_uint8(x_359, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_356)) {
 x_360 = lean_alloc_ctor(0, 4, 0);
} else {
 x_360 = x_356;
}
lean_ctor_set(x_360, 0, x_353);
lean_ctor_set(x_360, 1, x_354);
lean_ctor_set(x_360, 2, x_355);
lean_ctor_set(x_360, 3, x_359);
x_361 = lean_st_ref_set(x_6, x_360, x_352);
lean_dec(x_6);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_363 = x_361;
} else {
 lean_dec_ref(x_361);
 x_363 = lean_box(0);
}
x_364 = lean_box(x_342);
x_365 = lean_box(x_348);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
if (lean_is_scalar(x_363)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_363;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_362);
x_8 = x_367;
goto block_16;
}
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; 
x_438 = lean_ctor_get(x_5, 3);
lean_inc(x_438);
x_439 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(x_6, x_18);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_442 = lean_ctor_get(x_3, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_3, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_3, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_3, 4);
lean_inc(x_445);
lean_inc(x_444);
lean_inc(x_443);
lean_inc(x_2);
lean_inc(x_1);
x_446 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_446, 0, x_1);
lean_ctor_set(x_446, 1, x_2);
lean_ctor_set(x_446, 2, x_443);
lean_ctor_set(x_446, 3, x_444);
x_447 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_447, 0, x_446);
x_448 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_448, 0, x_442);
lean_ctor_set(x_448, 1, x_443);
lean_ctor_set(x_448, 2, x_444);
lean_ctor_set(x_448, 3, x_447);
lean_ctor_set(x_448, 4, x_445);
x_449 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_448);
lean_inc(x_2);
lean_inc(x_1);
x_450 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__2(x_1, x_2, x_449, x_448, x_4, x_5, x_6, x_441);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
x_453 = l_Lean_Meta_isExprDefEq___closed__2;
x_492 = lean_st_ref_get(x_6, x_452);
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_493, 3);
lean_inc(x_494);
lean_dec(x_493);
x_495 = lean_ctor_get_uint8(x_494, sizeof(void*)*1);
lean_dec(x_494);
if (x_495 == 0)
{
lean_object* x_496; uint8_t x_497; 
x_496 = lean_ctor_get(x_492, 1);
lean_inc(x_496);
lean_dec(x_492);
x_497 = 0;
x_454 = x_497;
x_455 = x_496;
goto block_491;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; 
x_498 = lean_ctor_get(x_492, 1);
lean_inc(x_498);
lean_dec(x_492);
x_499 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_453, x_448, x_4, x_5, x_6, x_498);
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec(x_499);
x_502 = lean_unbox(x_500);
lean_dec(x_500);
x_454 = x_502;
x_455 = x_501;
goto block_491;
}
block_491:
{
if (x_454 == 0)
{
lean_object* x_456; uint8_t x_457; 
lean_dec(x_448);
lean_dec(x_2);
lean_dec(x_1);
x_456 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_440, x_453, x_438, x_3, x_4, x_5, x_6, x_455);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_457 = !lean_is_exclusive(x_456);
if (x_457 == 0)
{
lean_object* x_458; 
x_458 = lean_ctor_get(x_456, 0);
lean_dec(x_458);
lean_ctor_set(x_456, 0, x_451);
return x_456;
}
else
{
lean_object* x_459; lean_object* x_460; 
x_459 = lean_ctor_get(x_456, 1);
lean_inc(x_459);
lean_dec(x_456);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_451);
lean_ctor_set(x_460, 1, x_459);
return x_460;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; 
x_461 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_461, 0, x_1);
x_462 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8;
x_463 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_461);
x_464 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_465 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set(x_465, 1, x_464);
x_466 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_466, 0, x_2);
x_467 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_467, 0, x_465);
lean_ctor_set(x_467, 1, x_466);
x_468 = l_Lean_Meta_isLevelDefEq___closed__2;
x_469 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
x_470 = lean_unbox(x_451);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; 
x_471 = l_Lean_Meta_isLevelDefEq___closed__4;
x_472 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_472, 0, x_469);
lean_ctor_set(x_472, 1, x_471);
x_473 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_462);
x_474 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_453, x_473, x_448, x_4, x_5, x_6, x_455);
lean_dec(x_448);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
lean_dec(x_474);
x_476 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_440, x_453, x_438, x_3, x_4, x_5, x_6, x_475);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_477 = !lean_is_exclusive(x_476);
if (x_477 == 0)
{
lean_object* x_478; 
x_478 = lean_ctor_get(x_476, 0);
lean_dec(x_478);
lean_ctor_set(x_476, 0, x_451);
return x_476;
}
else
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_476, 1);
lean_inc(x_479);
lean_dec(x_476);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_451);
lean_ctor_set(x_480, 1, x_479);
return x_480;
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; 
x_481 = l_Lean_Meta_isLevelDefEq___closed__6;
x_482 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_482, 0, x_469);
lean_ctor_set(x_482, 1, x_481);
x_483 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_462);
x_484 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_453, x_483, x_448, x_4, x_5, x_6, x_455);
lean_dec(x_448);
x_485 = lean_ctor_get(x_484, 1);
lean_inc(x_485);
lean_dec(x_484);
x_486 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_440, x_453, x_438, x_3, x_4, x_5, x_6, x_485);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_487 = !lean_is_exclusive(x_486);
if (x_487 == 0)
{
lean_object* x_488; 
x_488 = lean_ctor_get(x_486, 0);
lean_dec(x_488);
lean_ctor_set(x_486, 0, x_451);
return x_486;
}
else
{
lean_object* x_489; lean_object* x_490; 
x_489 = lean_ctor_get(x_486, 1);
lean_inc(x_489);
lean_dec(x_486);
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_451);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; 
lean_dec(x_448);
lean_dec(x_2);
lean_dec(x_1);
x_503 = lean_ctor_get(x_450, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_450, 1);
lean_inc(x_504);
lean_dec(x_450);
x_505 = l_Lean_Meta_isExprDefEq___closed__2;
x_506 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_440, x_505, x_438, x_3, x_4, x_5, x_6, x_504);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_507 = !lean_is_exclusive(x_506);
if (x_507 == 0)
{
lean_object* x_508; 
x_508 = lean_ctor_get(x_506, 0);
lean_dec(x_508);
lean_ctor_set_tag(x_506, 1);
lean_ctor_set(x_506, 0, x_503);
return x_506;
}
else
{
lean_object* x_509; lean_object* x_510; 
x_509 = lean_ctor_get(x_506, 1);
lean_inc(x_509);
lean_dec(x_506);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_503);
lean_ctor_set(x_510, 1, x_509);
return x_510;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isExprDefEq___spec__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqGuarded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isExprDefEqGuarded(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqNoConstantApprox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get_uint8(x_9, 3);
x_22 = lean_ctor_get_uint8(x_9, 4);
x_23 = lean_ctor_get_uint8(x_9, 5);
x_24 = lean_ctor_get_uint8(x_9, 6);
x_25 = lean_ctor_get_uint8(x_9, 7);
x_26 = lean_ctor_get_uint8(x_9, 8);
x_27 = lean_ctor_get_uint8(x_9, 9);
x_28 = lean_ctor_get_uint8(x_9, 10);
x_29 = lean_ctor_get_uint8(x_9, 11);
x_30 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_31 = 1;
x_32 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_32, 0, x_31);
lean_ctor_set_uint8(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, 2, x_31);
lean_ctor_set_uint8(x_32, 3, x_21);
lean_ctor_set_uint8(x_32, 4, x_22);
lean_ctor_set_uint8(x_32, 5, x_23);
lean_ctor_set_uint8(x_32, 6, x_24);
lean_ctor_set_uint8(x_32, 7, x_25);
lean_ctor_set_uint8(x_32, 8, x_26);
lean_ctor_set_uint8(x_32, 9, x_27);
lean_ctor_set_uint8(x_32, 10, x_28);
lean_ctor_set_uint8(x_32, 11, x_29);
lean_ctor_set_uint8(x_32, 12, x_30);
lean_ctor_set(x_3, 0, x_32);
x_33 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
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
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_40 = x_33;
} else {
 lean_dec_ref(x_33);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_42 = lean_ctor_get(x_3, 0);
x_43 = lean_ctor_get(x_3, 1);
x_44 = lean_ctor_get(x_3, 2);
x_45 = lean_ctor_get(x_3, 3);
x_46 = lean_ctor_get(x_3, 4);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_3);
x_47 = lean_ctor_get_uint8(x_42, 3);
x_48 = lean_ctor_get_uint8(x_42, 4);
x_49 = lean_ctor_get_uint8(x_42, 5);
x_50 = lean_ctor_get_uint8(x_42, 6);
x_51 = lean_ctor_get_uint8(x_42, 7);
x_52 = lean_ctor_get_uint8(x_42, 8);
x_53 = lean_ctor_get_uint8(x_42, 9);
x_54 = lean_ctor_get_uint8(x_42, 10);
x_55 = lean_ctor_get_uint8(x_42, 11);
x_56 = lean_ctor_get_uint8(x_42, 12);
if (lean_is_exclusive(x_42)) {
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
x_58 = 1;
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 0, 13);
} else {
 x_59 = x_57;
}
lean_ctor_set_uint8(x_59, 0, x_58);
lean_ctor_set_uint8(x_59, 1, x_58);
lean_ctor_set_uint8(x_59, 2, x_58);
lean_ctor_set_uint8(x_59, 3, x_47);
lean_ctor_set_uint8(x_59, 4, x_48);
lean_ctor_set_uint8(x_59, 5, x_49);
lean_ctor_set_uint8(x_59, 6, x_50);
lean_ctor_set_uint8(x_59, 7, x_51);
lean_ctor_set_uint8(x_59, 8, x_52);
lean_ctor_set_uint8(x_59, 9, x_53);
lean_ctor_set_uint8(x_59, 10, x_54);
lean_ctor_set_uint8(x_59, 11, x_55);
lean_ctor_set_uint8(x_59, 12, x_56);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_43);
lean_ctor_set(x_60, 2, x_44);
lean_ctor_set(x_60, 3, x_45);
lean_ctor_set(x_60, 4, x_46);
x_61 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_60, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_LevelDefEq___hyg_3284_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6;
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
LEAN_EXPORT lean_object* initialize_Lean_Meta_LevelDefEq(lean_object* w) {
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
l_Lean_Meta_DecLevelContext_canAssignMVars___default = _init_l_Lean_Meta_DecLevelContext_canAssignMVars___default();
l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__1 = _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__1);
l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__2 = _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__2);
l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__3 = _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__3();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__3);
l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__4 = _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__4();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__4);
l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__5 = _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__5();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__5);
l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__6 = _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__6();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__6);
l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__7 = _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__7();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__7);
l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8 = _init_l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___spec__1___closed__8);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__1);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__2 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__2);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__3 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__3);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__4);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__5 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__5();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__5);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__6);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__7 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__7();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__7);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__8 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__8();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__8);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__9 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__9();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__9);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__10 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__10();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_decAux_x3f___closed__10);
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
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
l_Lean_Meta_isLevelDefEqAux___lambda__2___closed__1 = _init_l_Lean_Meta_isLevelDefEqAux___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAux___lambda__2___closed__1);
l_Lean_Meta_getResetPostponed___closed__1 = _init_l_Lean_Meta_getResetPostponed___closed__1();
lean_mark_persistent(l_Lean_Meta_getResetPostponed___closed__1);
l_Lean_Meta_getResetPostponed___closed__2 = _init_l_Lean_Meta_getResetPostponed___closed__2();
lean_mark_persistent(l_Lean_Meta_getResetPostponed___closed__2);
l_Lean_Meta_getResetPostponed___closed__3 = _init_l_Lean_Meta_getResetPostponed___closed__3();
lean_mark_persistent(l_Lean_Meta_getResetPostponed___closed__3);
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
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__6 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__6();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__6);
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
l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__1);
l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12___closed__2);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__1);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__2);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__3);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__5 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__5();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__5);
l_Lean_Meta_processPostponed_loop___lambda__2___closed__1 = _init_l_Lean_Meta_processPostponed_loop___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_processPostponed_loop___lambda__2___closed__1);
l_Lean_Meta_processPostponed_loop___lambda__2___closed__2 = _init_l_Lean_Meta_processPostponed_loop___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_processPostponed_loop___lambda__2___closed__2);
l_Lean_Meta_processPostponed_loop___closed__1 = _init_l_Lean_Meta_processPostponed_loop___closed__1();
lean_mark_persistent(l_Lean_Meta_processPostponed_loop___closed__1);
l_Lean_Meta_processPostponed_loop___closed__2 = _init_l_Lean_Meta_processPostponed_loop___closed__2();
lean_mark_persistent(l_Lean_Meta_processPostponed_loop___closed__2);
l_Lean_Meta_processPostponed_loop___closed__3 = _init_l_Lean_Meta_processPostponed_loop___closed__3();
lean_mark_persistent(l_Lean_Meta_processPostponed_loop___closed__3);
l_Lean_Meta_processPostponed_loop___closed__4 = _init_l_Lean_Meta_processPostponed_loop___closed__4();
lean_mark_persistent(l_Lean_Meta_processPostponed_loop___closed__4);
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
res = l_Lean_Meta_initFn____x40_Lean_Meta_LevelDefEq___hyg_3284_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Meta.LevelDefEq
// Imports: Init Lean.Meta.Basic Lean.Meta.InferType
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
lean_object* l_Lean_Meta_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___closed__4;
lean_object* l_Lean_Meta_isDefEqNoConstantApprox___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize___main(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_findLevelDepth_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f___at_Lean_Meta_decLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_isDefEqNoConstantApprox___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_8__getLevelConstraintKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isLevelDefEq___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_isDefEqNoConstantApprox___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___rarg___lambda__1___closed__6;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___rarg___lambda__1___closed__4;
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_13__processPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___closed__3;
lean_object* l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_8__getLevelConstraintKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux___main___closed__5;
lean_object* l_Lean_Meta_isDefEqNoConstantApprox___rarg___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_decLevel___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux___main___closed__3;
extern lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
lean_object* l___private_Lean_Meta_LevelDefEq_10__getResetPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_9__getNumPostponed___boxed(lean_object*);
lean_object* l_Lean_Meta_decLevel___rarg___lambda__1___closed__1;
lean_object* l_Lean_Meta_decLevel___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3;
uint8_t l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isDefEqNoConstantApprox___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_10__getResetPostponed(lean_object*);
lean_object* l_Lean_Meta_isDefEqNoConstantApprox___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2;
lean_object* l_Lean_Meta_assignLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux___main___closed__1;
lean_object* l_Lean_Meta_isDefEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_13__processPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_10__getResetPostponed___boxed(lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__1;
uint8_t l_Lean_MetavarContext_hasAssignableLevelMVar___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux___main___closed__2;
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux(lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isExprDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__3;
lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
lean_object* l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isListLevelDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___at_Lean_Meta_getDecLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__1;
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__6;
lean_object* l_Lean_Meta_isLevelDefEqAux___main___closed__4;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4;
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_level_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__1;
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__8;
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__2;
lean_object* l_Lean_Meta_isLevelDefEqAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__9;
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isExprDefEq___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg(lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__4;
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___closed__1;
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__3;
lean_object* l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel(lean_object*);
lean_object* l_Lean_Meta_getLevel___at___private_Lean_Meta_InferType_5__inferForallType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux___main___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_6__solveSelfMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___lambda__1___closed__1;
lean_object* l_Lean_Meta_isDefEqNoConstantApprox___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_14__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_11__processPostponedStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isListLevelDefEqAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_9__getNumPostponed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__4;
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux___main___closed__6;
lean_object* l___private_Lean_Meta_LevelDefEq_2__decLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___closed__1;
lean_object* l_Lean_Meta_commitWhen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isListLevelDefEqAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEq(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__5;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f___at_Lean_Meta_decLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_6__solveSelfMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_isExprDefEq___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelSucc(lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__3;
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_occurs___main(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_toArray___rarg(lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_assign_level(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_isDefEqNoConstantApprox___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__3;
lean_object* l_Lean_Meta_isLevelDefEq___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isMVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___at_Lean_Meta_getDecLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isListLevelDefEqAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*);
lean_object* l_Lean_Meta_isDefEqNoConstantApprox(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___boxed(lean_object*);
lean_object* l_Lean_Meta_decLevel___rarg___lambda__1___closed__5;
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_10__getResetPostponed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___rarg___lambda__1___closed__3;
lean_object* l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__2;
lean_object* l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEqAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__2;
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___boxed(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__3;
lean_object* l___private_Lean_Meta_LevelDefEq_9__getNumPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_LevelDefEq_4__strictOccursMax(lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isDefEqNoConstantApprox___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__7;
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_1__decAux_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_4__strictOccursMax___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___closed__1;
lean_object* l_Lean_Meta_commitWhen___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_2__decLevelImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel___rarg___closed__1;
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_isExprDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_9__getNumPostponed(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___closed__2;
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_isLevelDefEq___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___boxed(lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f(lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__3;
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_11);
x_12 = l_Lean_MetavarContext_findLevelDepth_x3f(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_free_object(x_7);
x_13 = l_Lean_mkLevelMVar(x_1);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__3;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_18, x_2, x_3, x_4, x_5, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_1);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; 
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
else
{
uint8_t x_25; lean_object* x_26; 
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_29);
x_30 = l_Lean_MetavarContext_findLevelDepth_x3f(x_29, x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_29);
x_31 = l_Lean_mkLevelMVar(x_1);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__3;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_36, x_2, x_3, x_4, x_5, x_28);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_1);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec(x_29);
x_40 = lean_nat_dec_eq(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_41 = 1;
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_28);
return x_43;
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_28);
return x_46;
}
}
}
}
}
lean_object* l_Lean_Meta_assignLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_metavar_ctx_assign_level(x_12, x_1, x_2);
lean_ctor_set(x_9, 0, x_13);
x_14 = lean_st_ref_set(x_4, x_9, x_10);
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
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 2);
x_24 = lean_ctor_get(x_9, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_25 = lean_metavar_ctx_assign_level(x_21, x_1, x_2);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
x_27 = lean_st_ref_set(x_4, x_26, x_10);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main(x_10, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main(x_11, x_2, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_20, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = l_Lean_mkLevelMax(x_19, x_29);
lean_ctor_set(x_21, 0, x_30);
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = l_Lean_mkLevelMax(x_19, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_20, 0, x_33);
return x_20;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec(x_20);
x_35 = lean_ctor_get(x_21, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_36 = x_21;
} else {
 lean_dec_ref(x_21);
 x_36 = lean_box(0);
}
x_37 = l_Lean_mkLevelMax(x_19, x_35);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_19);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
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
lean_dec(x_11);
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
case 3:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
lean_dec(x_1);
x_50 = l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main(x_48, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_49);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main(x_49, x_2, x_3, x_4, x_5, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
lean_dec(x_57);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_58, 0);
lean_dec(x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_58);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_58, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_59, 0);
x_68 = l_Lean_mkLevelMax(x_57, x_67);
lean_ctor_set(x_59, 0, x_68);
return x_58;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
lean_dec(x_59);
x_70 = l_Lean_mkLevelMax(x_57, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_58, 0, x_71);
return x_58;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_58, 1);
lean_inc(x_72);
lean_dec(x_58);
x_73 = lean_ctor_get(x_59, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_74 = x_59;
} else {
 lean_dec_ref(x_59);
 x_74 = lean_box(0);
}
x_75 = l_Lean_mkLevelMax(x_57, x_73);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_72);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_57);
x_78 = !lean_is_exclusive(x_58);
if (x_78 == 0)
{
return x_58;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_58, 0);
x_80 = lean_ctor_get(x_58, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_58);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_49);
x_82 = !lean_is_exclusive(x_50);
if (x_82 == 0)
{
return x_50;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_50, 0);
x_84 = lean_ctor_get(x_50, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_50);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
case 5:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
lean_dec(x_1);
x_87 = lean_st_ref_get(x_3, x_6);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_86);
x_91 = lean_metavar_ctx_get_level_assignment(x_90, x_86);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
lean_inc(x_86);
x_92 = l_Lean_Meta_isReadOnlyLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__1(x_86, x_2, x_3, x_4, x_5, x_89);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(x_3, x_4, x_5, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_97);
x_99 = l_Lean_mkLevelSucc(x_97);
x_100 = l_Lean_Meta_assignLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__2(x_86, x_99, x_2, x_3, x_4, x_5, x_98);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 0);
lean_dec(x_102);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_100, 0, x_103);
return x_100;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_dec(x_100);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_97);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_dec(x_86);
x_107 = !lean_is_exclusive(x_92);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_92, 0);
lean_dec(x_108);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_92, 1);
lean_inc(x_109);
lean_dec(x_92);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_91);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_86);
x_111 = !lean_is_exclusive(x_92);
if (x_111 == 0)
{
return x_92;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_92, 0);
x_113 = lean_ctor_get(x_92, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_92);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; 
lean_dec(x_86);
x_115 = lean_ctor_get(x_91, 0);
lean_inc(x_115);
lean_dec(x_91);
x_1 = x_115;
x_6 = x_89;
goto _start;
}
}
default: 
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_1);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_6);
return x_118;
}
}
}
}
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isReadOnlyLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_assignLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_assignLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_1__decAux_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_LevelDefEq_1__decAux_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_2__decLevelImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_3, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
lean_ctor_set(x_15, 0, x_10);
x_19 = lean_st_ref_set(x_3, x_15, x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_12);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_ctor_get(x_15, 2);
x_26 = lean_ctor_get(x_15, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_st_ref_set(x_3, x_27, x_16);
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
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_11, 0);
lean_dec(x_33);
return x_11;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_dec(x_11);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_12);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_11, 0);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_11);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_2__decLevelImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_decLevel_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_2__decLevelImp___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_decLevel_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_decLevel_x3f___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_decLevel_x3f___at_Lean_Meta_decLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Meta_decLevel___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid universe level, ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_decLevel___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_decLevel___rarg___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_decLevel___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_decLevel___rarg___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_decLevel___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" is not greater than 0");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_decLevel___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_decLevel___rarg___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_decLevel___rarg___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_decLevel___rarg___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_decLevel___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = l_Lean_Meta_decLevel___rarg___lambda__1___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Meta_decLevel___rarg___lambda__1___closed__6;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
}
}
lean_object* l_Lean_Meta_decLevel___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_decLevel_x3f___at_Lean_Meta_decLevel___spec__1___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_decLevel___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_decLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_decLevel___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_decLevel_x3f___at_Lean_Meta_decLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_decLevel_x3f___at_Lean_Meta_decLevel___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_decLevel___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_decLevel___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_decLevel___at_Lean_Meta_getDecLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_11 = l_Lean_Meta_decLevel___rarg___lambda__1___closed__3;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_decLevel___rarg___lambda__1___closed__6;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_14, x_2, x_3, x_4, x_5, x_9);
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
lean_object* _init_l_Lean_Meta_getDecLevel___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_decLevel___at_Lean_Meta_getDecLevel___spec__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_getDecLevel___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___at___private_Lean_Meta_InferType_5__inferForallType___spec__1), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_getDecLevel___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_getDecLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getDecLevel___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_decLevel___at_Lean_Meta_getDecLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_decLevel___at_Lean_Meta_getDecLevel___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
uint8_t l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux___main(x_1, x_8);
if (x_10 == 0)
{
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_box(0);
x_3 = x_13;
goto block_7;
}
block_7:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = lean_level_eq(x_2, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Level_occurs___main(x_1, x_2);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Lean_Meta_LevelDefEq_4__strictOccursMax(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux___main(x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l___private_Lean_Meta_LevelDefEq_3__strictOccursMaxAux___main(x_1, x_4);
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
lean_object* l___private_Lean_Meta_LevelDefEq_4__strictOccursMax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_LevelDefEq_4__strictOccursMax(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff___main(x_1, x_4, x_3);
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
x_10 = l_Lean_mkLevelMax(x_3, x_2);
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
x_11 = l_Lean_mkLevelMax(x_3, x_2);
return x_11;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_6__solveSelfMax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_LevelDefEq_5__mkMaxArgsDiff___main(x_1, x_2, x_9);
x_12 = l_Lean_Meta_assignLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__2(x_1, x_11, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_6__solveSelfMax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_6__solveSelfMax(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
x_14 = l_Std_PersistentArray_push___rarg(x_12, x_13);
lean_ctor_set(x_9, 2, x_14);
x_15 = lean_st_ref_set(x_4, x_9, x_10);
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
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
x_24 = lean_ctor_get(x_9, 2);
x_25 = lean_ctor_get(x_9, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_2);
x_27 = l_Std_PersistentArray_push___rarg(x_24, x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = lean_st_ref_set(x_4, x_28, x_10);
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
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_8__getLevelConstraintKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lean_Meta_isReadOnlyLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = l_Lean_Level_occurs___main(x_1, x_2);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
uint8_t x_17; 
x_17 = l___private_Lean_Meta_LevelDefEq_4__strictOccursMax(x_1, x_2);
lean_dec(x_1);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
x_19 = lean_box(x_18);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
uint8_t x_20; lean_object* x_21; 
x_20 = 2;
x_21 = lean_box(x_20);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_dec(x_9);
x_23 = l_Lean_Level_occurs___main(x_1, x_2);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l___private_Lean_Meta_LevelDefEq_4__strictOccursMax(x_1, x_2);
lean_dec(x_1);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = 2;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_22);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_9);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_9, 0);
lean_dec(x_35);
x_36 = 2;
x_37 = lean_box(x_36);
lean_ctor_set(x_9, 0, x_37);
return x_9;
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_dec(x_9);
x_39 = 2;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
return x_9;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_9, 0);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_9);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_46 = 2;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_8__getLevelConstraintKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_8__getLevelConstraintKind(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 2);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_9);
x_20 = l_Std_PersistentArray_push___rarg(x_18, x_19);
lean_ctor_set(x_13, 0, x_20);
x_21 = lean_st_ref_set(x_6, x_12, x_14);
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
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_9);
x_31 = l_Std_PersistentArray_push___rarg(x_29, x_30);
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_28);
lean_ctor_set(x_12, 2, x_32);
x_33 = lean_st_ref_set(x_6, x_12, x_14);
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
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
x_40 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_42 = x_13;
} else {
 lean_dec_ref(x_13);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_9);
x_44 = l_Std_PersistentArray_push___rarg(x_41, x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 1, 1);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_40);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_st_ref_set(x_6, x_46, x_14);
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
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
lean_inc(x_1);
x_19 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1, x_3, x_4, x_5, x_6, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_box(0);
x_30 = lean_apply_1(x_2, x_29);
x_31 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3(x_1, x_30, x_3, x_4, x_5, x_6, x_28);
return x_31;
}
}
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" =?= ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_isLevelDefEqAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3;
x_6 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEqAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isLevelDefEq");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEqAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_isLevelDefEqAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEqAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("step");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEqAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isLevelDefEqAux___main___closed__2;
x_2 = l_Lean_Meta_isLevelDefEqAux___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEqAux___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("stuck");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEqAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isLevelDefEqAux___main___closed__2;
x_2 = l_Lean_Meta_isLevelDefEqAux___main___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_isLevelDefEqAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_1) == 1)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_565; lean_object* x_566; 
x_565 = lean_ctor_get(x_1, 0);
lean_inc(x_565);
lean_dec(x_1);
x_566 = lean_ctor_get(x_2, 0);
lean_inc(x_566);
lean_dec(x_2);
x_1 = x_565;
x_2 = x_566;
goto _start;
}
else
{
lean_object* x_568; 
x_568 = lean_box(0);
x_8 = x_568;
goto block_564;
}
}
else
{
lean_object* x_569; 
x_569 = lean_box(0);
x_8 = x_569;
goto block_564;
}
block_564:
{
uint8_t x_9; 
lean_dec(x_8);
x_9 = lean_level_eq(x_1, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAux___main___lambda__1___boxed), 3, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_Meta_isLevelDefEqAux___main___closed__4;
lean_inc(x_10);
x_12 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_11, x_10, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_1);
x_14 = l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_1, x_3, x_4, x_5, x_6, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Level_normalize___main(x_15);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_2, x_3, x_4, x_5, x_6, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Level_normalize___main(x_19);
lean_dec(x_19);
x_22 = lean_level_eq(x_1, x_17);
if (x_22 == 0)
{
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_17;
x_2 = x_21;
x_7 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = lean_level_eq(x_2, x_21);
if (x_24 == 0)
{
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_17;
x_2 = x_21;
x_7 = x_20;
goto _start;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_21);
lean_dec(x_17);
x_26 = lean_st_ref_get(x_4, x_20);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_356; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_30);
x_356 = l_Lean_MetavarContext_hasAssignableLevelMVar___main(x_30, x_1);
if (x_356 == 0)
{
uint8_t x_357; 
x_357 = l_Lean_MetavarContext_hasAssignableLevelMVar___main(x_30, x_2);
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; 
x_358 = lean_ctor_get(x_3, 0);
x_359 = lean_ctor_get_uint8(x_358, 4);
if (x_359 == 0)
{
uint8_t x_360; lean_object* x_361; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_360 = 0;
x_361 = lean_box(x_360);
lean_ctor_set(x_26, 0, x_361);
return x_26;
}
else
{
uint8_t x_362; 
x_362 = l_Lean_Level_isMVar(x_1);
lean_dec(x_1);
if (x_362 == 0)
{
uint8_t x_363; 
x_363 = l_Lean_Level_isMVar(x_2);
lean_dec(x_2);
if (x_363 == 0)
{
uint8_t x_364; lean_object* x_365; 
lean_dec(x_10);
x_364 = 0;
x_365 = lean_box(x_364);
lean_ctor_set(x_26, 0, x_365);
return x_26;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_free_object(x_26);
x_366 = l_Lean_Meta_isLevelDefEqAux___main___closed__6;
x_367 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_366, x_10, x_3, x_4, x_5, x_6, x_29);
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
lean_dec(x_367);
x_369 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_368);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_free_object(x_26);
lean_dec(x_2);
x_370 = l_Lean_Meta_isLevelDefEqAux___main___closed__6;
x_371 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_370, x_10, x_3, x_4, x_5, x_6, x_29);
x_372 = lean_ctor_get(x_371, 1);
lean_inc(x_372);
lean_dec(x_371);
x_373 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_372);
return x_373;
}
}
}
else
{
lean_object* x_374; 
lean_free_object(x_26);
lean_dec(x_10);
x_374 = lean_box(0);
x_31 = x_374;
goto block_355;
}
}
else
{
lean_object* x_375; 
lean_dec(x_30);
lean_free_object(x_26);
lean_dec(x_10);
x_375 = lean_box(0);
x_31 = x_375;
goto block_355;
}
block_355:
{
lean_object* x_32; 
lean_dec(x_31);
lean_inc(x_1);
x_32 = l___private_Lean_Meta_LevelDefEq_8__getLevelConstraintKind(x_1, x_2, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
switch (x_34) {
case 0:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_37 = l_Lean_Meta_assignLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__2(x_36, x_2, x_3, x_4, x_5, x_6, x_35);
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
case 1:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_dec(x_32);
x_47 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_48 = l___private_Lean_Meta_LevelDefEq_6__solveSelfMax(x_47, x_2, x_3, x_4, x_5, x_6, x_46);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = 1;
x_52 = lean_box(x_51);
lean_ctor_set(x_48, 0, x_52);
return x_48;
}
else
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_dec(x_48);
x_54 = 1;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
default: 
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_32);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_32, 1);
x_59 = lean_ctor_get(x_32, 0);
lean_dec(x_59);
lean_inc(x_2);
x_60 = l___private_Lean_Meta_LevelDefEq_8__getLevelConstraintKind(x_2, x_1, x_3, x_4, x_5, x_6, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; uint8_t x_118; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_118 = lean_unbox(x_61);
lean_dec(x_61);
switch (x_118) {
case 0:
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_63);
lean_free_object(x_32);
x_119 = l_Lean_Level_mvarId_x21(x_2);
lean_dec(x_2);
x_120 = l_Lean_Meta_assignLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__2(x_119, x_1, x_3, x_4, x_5, x_6, x_62);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_120, 0);
lean_dec(x_122);
x_123 = 1;
x_124 = lean_box(x_123);
lean_ctor_set(x_120, 0, x_124);
return x_120;
}
else
{
lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_dec(x_120);
x_126 = 1;
x_127 = lean_box(x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
}
case 1:
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_63);
lean_free_object(x_32);
x_129 = l_Lean_Level_mvarId_x21(x_2);
lean_dec(x_2);
x_130 = l___private_Lean_Meta_LevelDefEq_6__solveSelfMax(x_129, x_1, x_3, x_4, x_5, x_6, x_62);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_130, 0);
lean_dec(x_132);
x_133 = 1;
x_134 = lean_box(x_133);
lean_ctor_set(x_130, 0, x_134);
return x_130;
}
else
{
lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_130, 1);
lean_inc(x_135);
lean_dec(x_130);
x_136 = 1;
x_137 = lean_box(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
}
default: 
{
uint8_t x_139; 
x_139 = l_Lean_Level_isMVar(x_1);
if (x_139 == 0)
{
uint8_t x_140; 
x_140 = l_Lean_Level_isMVar(x_2);
if (x_140 == 0)
{
lean_free_object(x_32);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_1, 0);
lean_inc(x_141);
lean_inc(x_2);
x_142 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_2, x_3, x_4, x_5, x_6, x_62);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_141);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = 0;
x_64 = x_145;
x_65 = x_144;
goto block_117;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
lean_dec(x_142);
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
lean_dec(x_143);
x_148 = l_Lean_Meta_isLevelDefEqAux___main(x_141, x_147, x_3, x_4, x_5, x_6, x_146);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
x_64 = x_151;
x_65 = x_150;
goto block_117;
}
else
{
uint8_t x_152; 
lean_dec(x_63);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_148);
if (x_152 == 0)
{
return x_148;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_148, 0);
x_154 = lean_ctor_get(x_148, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_148);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_141);
lean_dec(x_63);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_142);
if (x_156 == 0)
{
return x_142;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_142, 0);
x_158 = lean_ctor_get(x_142, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_142);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
lean_dec(x_63);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_2, 0);
lean_inc(x_160);
lean_inc(x_1);
x_161 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_1, x_3, x_4, x_5, x_6, x_62);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_163);
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_164, 0);
lean_dec(x_166);
x_167 = 1;
x_168 = lean_box(x_167);
lean_ctor_set(x_164, 0, x_168);
return x_164;
}
else
{
lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_dec(x_164);
x_170 = 1;
x_171 = lean_box(x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_169);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_161, 1);
lean_inc(x_173);
lean_dec(x_161);
x_174 = lean_ctor_get(x_162, 0);
lean_inc(x_174);
lean_dec(x_162);
x_175 = l_Lean_Meta_isLevelDefEqAux___main(x_160, x_174, x_3, x_4, x_5, x_6, x_173);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_unbox(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_dec(x_176);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec(x_175);
x_179 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_178);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_179, 0);
lean_dec(x_181);
x_182 = 1;
x_183 = lean_box(x_182);
lean_ctor_set(x_179, 0, x_183);
return x_179;
}
else
{
lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_179, 1);
lean_inc(x_184);
lean_dec(x_179);
x_185 = 1;
x_186 = lean_box(x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_184);
return x_187;
}
}
else
{
uint8_t x_188; 
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_175);
if (x_188 == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_175, 0);
lean_dec(x_189);
return x_175;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_175, 1);
lean_inc(x_190);
lean_dec(x_175);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_176);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_2);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_175);
if (x_192 == 0)
{
return x_175;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_175, 0);
x_194 = lean_ctor_get(x_175, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_175);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_160);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_161);
if (x_196 == 0)
{
return x_161;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_161, 0);
x_198 = lean_ctor_get(x_161, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_161);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
lean_object* x_200; uint8_t x_201; 
x_200 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_62);
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_200, 0);
lean_dec(x_202);
x_203 = 1;
x_204 = lean_box(x_203);
lean_ctor_set(x_200, 0, x_204);
return x_200;
}
else
{
lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_200, 1);
lean_inc(x_205);
lean_dec(x_200);
x_206 = 1;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
return x_208;
}
}
}
}
else
{
uint8_t x_209; lean_object* x_210; 
lean_dec(x_63);
lean_dec(x_2);
lean_dec(x_1);
x_209 = 0;
x_210 = lean_box(x_209);
lean_ctor_set(x_32, 1, x_62);
lean_ctor_set(x_32, 0, x_210);
return x_32;
}
}
else
{
uint8_t x_211; lean_object* x_212; 
lean_dec(x_63);
lean_dec(x_2);
lean_dec(x_1);
x_211 = 0;
x_212 = lean_box(x_211);
lean_ctor_set(x_32, 1, x_62);
lean_ctor_set(x_32, 0, x_212);
return x_32;
}
}
}
block_117:
{
if (x_64 == 0)
{
lean_dec(x_63);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
lean_inc(x_1);
x_67 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_1, x_3, x_4, x_5, x_6, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_69);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
x_73 = 1;
x_74 = lean_box(x_73);
lean_ctor_set(x_70, 0, x_74);
return x_70;
}
else
{
lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_dec(x_70);
x_76 = 1;
x_77 = lean_box(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_dec(x_67);
x_80 = lean_ctor_get(x_68, 0);
lean_inc(x_80);
lean_dec(x_68);
x_81 = l_Lean_Meta_isLevelDefEqAux___main(x_66, x_80, x_3, x_4, x_5, x_6, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_82);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_84);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = 1;
x_89 = lean_box(x_88);
lean_ctor_set(x_85, 0, x_89);
return x_85;
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = 1;
x_92 = lean_box(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_81);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_81, 0);
lean_dec(x_95);
return x_81;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_81, 1);
lean_inc(x_96);
lean_dec(x_81);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_82);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_81);
if (x_98 == 0)
{
return x_81;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_81, 0);
x_100 = lean_ctor_get(x_81, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_81);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_66);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_67);
if (x_102 == 0)
{
return x_67;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_67, 0);
x_104 = lean_ctor_get(x_67, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_67);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_65);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_106, 0);
lean_dec(x_108);
x_109 = 1;
x_110 = lean_box(x_109);
lean_ctor_set(x_106, 0, x_110);
return x_106;
}
else
{
lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_112 = 1;
x_113 = lean_box(x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_2);
lean_dec(x_1);
x_115 = lean_box(x_64);
if (lean_is_scalar(x_63)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_63;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_65);
return x_116;
}
}
}
else
{
uint8_t x_213; 
lean_free_object(x_32);
lean_dec(x_2);
lean_dec(x_1);
x_213 = !lean_is_exclusive(x_60);
if (x_213 == 0)
{
return x_60;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_60, 0);
x_215 = lean_ctor_get(x_60, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_60);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_32, 1);
lean_inc(x_217);
lean_dec(x_32);
lean_inc(x_2);
x_218 = l___private_Lean_Meta_LevelDefEq_8__getLevelConstraintKind(x_2, x_1, x_3, x_4, x_5, x_6, x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; uint8_t x_266; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_221 = x_218;
} else {
 lean_dec_ref(x_218);
 x_221 = lean_box(0);
}
x_266 = lean_unbox(x_219);
lean_dec(x_219);
switch (x_266) {
case 0:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_221);
x_267 = l_Lean_Level_mvarId_x21(x_2);
lean_dec(x_2);
x_268 = l_Lean_Meta_assignLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__2(x_267, x_1, x_3, x_4, x_5, x_6, x_220);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_270 = x_268;
} else {
 lean_dec_ref(x_268);
 x_270 = lean_box(0);
}
x_271 = 1;
x_272 = lean_box(x_271);
if (lean_is_scalar(x_270)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_270;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_269);
return x_273;
}
case 1:
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_221);
x_274 = l_Lean_Level_mvarId_x21(x_2);
lean_dec(x_2);
x_275 = l___private_Lean_Meta_LevelDefEq_6__solveSelfMax(x_274, x_1, x_3, x_4, x_5, x_6, x_220);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_277 = x_275;
} else {
 lean_dec_ref(x_275);
 x_277 = lean_box(0);
}
x_278 = 1;
x_279 = lean_box(x_278);
if (lean_is_scalar(x_277)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_277;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_276);
return x_280;
}
default: 
{
uint8_t x_281; 
x_281 = l_Lean_Level_isMVar(x_1);
if (x_281 == 0)
{
uint8_t x_282; 
x_282 = l_Lean_Level_isMVar(x_2);
if (x_282 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_1, 0);
lean_inc(x_283);
lean_inc(x_2);
x_284 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_2, x_3, x_4, x_5, x_6, x_220);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; uint8_t x_287; 
lean_dec(x_283);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = 0;
x_222 = x_287;
x_223 = x_286;
goto block_265;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_284, 1);
lean_inc(x_288);
lean_dec(x_284);
x_289 = lean_ctor_get(x_285, 0);
lean_inc(x_289);
lean_dec(x_285);
x_290 = l_Lean_Meta_isLevelDefEqAux___main(x_283, x_289, x_3, x_4, x_5, x_6, x_288);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_unbox(x_291);
lean_dec(x_291);
x_222 = x_293;
x_223 = x_292;
goto block_265;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_221);
lean_dec(x_2);
lean_dec(x_1);
x_294 = lean_ctor_get(x_290, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_290, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_296 = x_290;
} else {
 lean_dec_ref(x_290);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_283);
lean_dec(x_221);
lean_dec(x_2);
lean_dec(x_1);
x_298 = lean_ctor_get(x_284, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_284, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_300 = x_284;
} else {
 lean_dec_ref(x_284);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
return x_301;
}
}
else
{
lean_dec(x_221);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_2, 0);
lean_inc(x_302);
lean_inc(x_1);
x_303 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_1, x_3, x_4, x_5, x_6, x_220);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_302);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_305);
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
x_309 = 1;
x_310 = lean_box(x_309);
if (lean_is_scalar(x_308)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_308;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_307);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_303, 1);
lean_inc(x_312);
lean_dec(x_303);
x_313 = lean_ctor_get(x_304, 0);
lean_inc(x_313);
lean_dec(x_304);
x_314 = l_Lean_Meta_isLevelDefEqAux___main(x_302, x_313, x_3, x_4, x_5, x_6, x_312);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; uint8_t x_316; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_unbox(x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_315);
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec(x_314);
x_318 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_317);
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
x_321 = 1;
x_322 = lean_box(x_321);
if (lean_is_scalar(x_320)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_320;
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_319);
return x_323;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_2);
lean_dec(x_1);
x_324 = lean_ctor_get(x_314, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_325 = x_314;
} else {
 lean_dec_ref(x_314);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_315);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_2);
lean_dec(x_1);
x_327 = lean_ctor_get(x_314, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_314, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_329 = x_314;
} else {
 lean_dec_ref(x_314);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_302);
lean_dec(x_2);
lean_dec(x_1);
x_331 = lean_ctor_get(x_303, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_303, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_333 = x_303;
} else {
 lean_dec_ref(x_303);
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
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; 
x_335 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_220);
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
uint8_t x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_221);
lean_dec(x_2);
lean_dec(x_1);
x_341 = 0;
x_342 = lean_box(x_341);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_220);
return x_343;
}
}
else
{
uint8_t x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_221);
lean_dec(x_2);
lean_dec(x_1);
x_344 = 0;
x_345 = lean_box(x_344);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_220);
return x_346;
}
}
}
block_265:
{
if (x_222 == 0)
{
lean_dec(x_221);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_2, 0);
lean_inc(x_224);
lean_inc(x_1);
x_225 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_1, x_3, x_4, x_5, x_6, x_223);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_224);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_227);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_230 = x_228;
} else {
 lean_dec_ref(x_228);
 x_230 = lean_box(0);
}
x_231 = 1;
x_232 = lean_box(x_231);
if (lean_is_scalar(x_230)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_230;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_229);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_225, 1);
lean_inc(x_234);
lean_dec(x_225);
x_235 = lean_ctor_get(x_226, 0);
lean_inc(x_235);
lean_dec(x_226);
x_236 = l_Lean_Meta_isLevelDefEqAux___main(x_224, x_235, x_3, x_4, x_5, x_6, x_234);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; uint8_t x_238; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_unbox(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_237);
x_239 = lean_ctor_get(x_236, 1);
lean_inc(x_239);
lean_dec(x_236);
x_240 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_239);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_242 = x_240;
} else {
 lean_dec_ref(x_240);
 x_242 = lean_box(0);
}
x_243 = 1;
x_244 = lean_box(x_243);
if (lean_is_scalar(x_242)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_242;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_241);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_2);
lean_dec(x_1);
x_246 = lean_ctor_get(x_236, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_247 = x_236;
} else {
 lean_dec_ref(x_236);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_237);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_2);
lean_dec(x_1);
x_249 = lean_ctor_get(x_236, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_236, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_251 = x_236;
} else {
 lean_dec_ref(x_236);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_224);
lean_dec(x_2);
lean_dec(x_1);
x_253 = lean_ctor_get(x_225, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_225, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_255 = x_225;
} else {
 lean_dec_ref(x_225);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; 
x_257 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_223);
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
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_2);
lean_dec(x_1);
x_263 = lean_box(x_222);
if (lean_is_scalar(x_221)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_221;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_223);
return x_264;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_2);
lean_dec(x_1);
x_347 = lean_ctor_get(x_218, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_218, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_349 = x_218;
} else {
 lean_dec_ref(x_218);
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
}
}
}
else
{
uint8_t x_351; 
lean_dec(x_2);
lean_dec(x_1);
x_351 = !lean_is_exclusive(x_32);
if (x_351 == 0)
{
return x_32;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_32, 0);
x_353 = lean_ctor_get(x_32, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_32);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_539; 
x_376 = lean_ctor_get(x_26, 0);
x_377 = lean_ctor_get(x_26, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_26);
x_378 = lean_ctor_get(x_376, 0);
lean_inc(x_378);
lean_dec(x_376);
lean_inc(x_378);
x_539 = l_Lean_MetavarContext_hasAssignableLevelMVar___main(x_378, x_1);
if (x_539 == 0)
{
uint8_t x_540; 
x_540 = l_Lean_MetavarContext_hasAssignableLevelMVar___main(x_378, x_2);
if (x_540 == 0)
{
lean_object* x_541; uint8_t x_542; 
x_541 = lean_ctor_get(x_3, 0);
x_542 = lean_ctor_get_uint8(x_541, 4);
if (x_542 == 0)
{
uint8_t x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_543 = 0;
x_544 = lean_box(x_543);
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_377);
return x_545;
}
else
{
uint8_t x_546; 
x_546 = l_Lean_Level_isMVar(x_1);
lean_dec(x_1);
if (x_546 == 0)
{
uint8_t x_547; 
x_547 = l_Lean_Level_isMVar(x_2);
lean_dec(x_2);
if (x_547 == 0)
{
uint8_t x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_10);
x_548 = 0;
x_549 = lean_box(x_548);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_377);
return x_550;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_551 = l_Lean_Meta_isLevelDefEqAux___main___closed__6;
x_552 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_551, x_10, x_3, x_4, x_5, x_6, x_377);
x_553 = lean_ctor_get(x_552, 1);
lean_inc(x_553);
lean_dec(x_552);
x_554 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_553);
return x_554;
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_2);
x_555 = l_Lean_Meta_isLevelDefEqAux___main___closed__6;
x_556 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_555, x_10, x_3, x_4, x_5, x_6, x_377);
x_557 = lean_ctor_get(x_556, 1);
lean_inc(x_557);
lean_dec(x_556);
x_558 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_557);
return x_558;
}
}
}
else
{
lean_object* x_559; 
lean_dec(x_10);
x_559 = lean_box(0);
x_379 = x_559;
goto block_538;
}
}
else
{
lean_object* x_560; 
lean_dec(x_378);
lean_dec(x_10);
x_560 = lean_box(0);
x_379 = x_560;
goto block_538;
}
block_538:
{
lean_object* x_380; 
lean_dec(x_379);
lean_inc(x_1);
x_380 = l___private_Lean_Meta_LevelDefEq_8__getLevelConstraintKind(x_1, x_2, x_3, x_4, x_5, x_6, x_377);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; uint8_t x_382; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_unbox(x_381);
lean_dec(x_381);
switch (x_382) {
case 0:
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; 
x_383 = lean_ctor_get(x_380, 1);
lean_inc(x_383);
lean_dec(x_380);
x_384 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_385 = l_Lean_Meta_assignLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__2(x_384, x_2, x_3, x_4, x_5, x_6, x_383);
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_387 = x_385;
} else {
 lean_dec_ref(x_385);
 x_387 = lean_box(0);
}
x_388 = 1;
x_389 = lean_box(x_388);
if (lean_is_scalar(x_387)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_387;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_386);
return x_390;
}
case 1:
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; 
x_391 = lean_ctor_get(x_380, 1);
lean_inc(x_391);
lean_dec(x_380);
x_392 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_393 = l___private_Lean_Meta_LevelDefEq_6__solveSelfMax(x_392, x_2, x_3, x_4, x_5, x_6, x_391);
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
x_396 = 1;
x_397 = lean_box(x_396);
if (lean_is_scalar(x_395)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_395;
}
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_394);
return x_398;
}
default: 
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_380, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_400 = x_380;
} else {
 lean_dec_ref(x_380);
 x_400 = lean_box(0);
}
lean_inc(x_2);
x_401 = l___private_Lean_Meta_LevelDefEq_8__getLevelConstraintKind(x_2, x_1, x_3, x_4, x_5, x_6, x_399);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; uint8_t x_449; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_404 = x_401;
} else {
 lean_dec_ref(x_401);
 x_404 = lean_box(0);
}
x_449 = lean_unbox(x_402);
lean_dec(x_402);
switch (x_449) {
case 0:
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_404);
lean_dec(x_400);
x_450 = l_Lean_Level_mvarId_x21(x_2);
lean_dec(x_2);
x_451 = l_Lean_Meta_assignLevelMVar___at___private_Lean_Meta_LevelDefEq_1__decAux_x3f___main___spec__2(x_450, x_1, x_3, x_4, x_5, x_6, x_403);
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_453 = x_451;
} else {
 lean_dec_ref(x_451);
 x_453 = lean_box(0);
}
x_454 = 1;
x_455 = lean_box(x_454);
if (lean_is_scalar(x_453)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_453;
}
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_452);
return x_456;
}
case 1:
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_404);
lean_dec(x_400);
x_457 = l_Lean_Level_mvarId_x21(x_2);
lean_dec(x_2);
x_458 = l___private_Lean_Meta_LevelDefEq_6__solveSelfMax(x_457, x_1, x_3, x_4, x_5, x_6, x_403);
x_459 = lean_ctor_get(x_458, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_460 = x_458;
} else {
 lean_dec_ref(x_458);
 x_460 = lean_box(0);
}
x_461 = 1;
x_462 = lean_box(x_461);
if (lean_is_scalar(x_460)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_460;
}
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_459);
return x_463;
}
default: 
{
uint8_t x_464; 
x_464 = l_Lean_Level_isMVar(x_1);
if (x_464 == 0)
{
uint8_t x_465; 
x_465 = l_Lean_Level_isMVar(x_2);
if (x_465 == 0)
{
lean_dec(x_400);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_466; lean_object* x_467; 
x_466 = lean_ctor_get(x_1, 0);
lean_inc(x_466);
lean_inc(x_2);
x_467 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_2, x_3, x_4, x_5, x_6, x_403);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; uint8_t x_470; 
lean_dec(x_466);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_470 = 0;
x_405 = x_470;
x_406 = x_469;
goto block_448;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_467, 1);
lean_inc(x_471);
lean_dec(x_467);
x_472 = lean_ctor_get(x_468, 0);
lean_inc(x_472);
lean_dec(x_468);
x_473 = l_Lean_Meta_isLevelDefEqAux___main(x_466, x_472, x_3, x_4, x_5, x_6, x_471);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
lean_dec(x_473);
x_476 = lean_unbox(x_474);
lean_dec(x_474);
x_405 = x_476;
x_406 = x_475;
goto block_448;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_404);
lean_dec(x_2);
lean_dec(x_1);
x_477 = lean_ctor_get(x_473, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_473, 1);
lean_inc(x_478);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_479 = x_473;
} else {
 lean_dec_ref(x_473);
 x_479 = lean_box(0);
}
if (lean_is_scalar(x_479)) {
 x_480 = lean_alloc_ctor(1, 2, 0);
} else {
 x_480 = x_479;
}
lean_ctor_set(x_480, 0, x_477);
lean_ctor_set(x_480, 1, x_478);
return x_480;
}
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
lean_dec(x_466);
lean_dec(x_404);
lean_dec(x_2);
lean_dec(x_1);
x_481 = lean_ctor_get(x_467, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_467, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_483 = x_467;
} else {
 lean_dec_ref(x_467);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_483)) {
 x_484 = lean_alloc_ctor(1, 2, 0);
} else {
 x_484 = x_483;
}
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_482);
return x_484;
}
}
else
{
lean_dec(x_404);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_2, 0);
lean_inc(x_485);
lean_inc(x_1);
x_486 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_1, x_3, x_4, x_5, x_6, x_403);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_485);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_489 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_488);
x_490 = lean_ctor_get(x_489, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_491 = x_489;
} else {
 lean_dec_ref(x_489);
 x_491 = lean_box(0);
}
x_492 = 1;
x_493 = lean_box(x_492);
if (lean_is_scalar(x_491)) {
 x_494 = lean_alloc_ctor(0, 2, 0);
} else {
 x_494 = x_491;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_490);
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_486, 1);
lean_inc(x_495);
lean_dec(x_486);
x_496 = lean_ctor_get(x_487, 0);
lean_inc(x_496);
lean_dec(x_487);
x_497 = l_Lean_Meta_isLevelDefEqAux___main(x_485, x_496, x_3, x_4, x_5, x_6, x_495);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; uint8_t x_499; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_unbox(x_498);
if (x_499 == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_498);
x_500 = lean_ctor_get(x_497, 1);
lean_inc(x_500);
lean_dec(x_497);
x_501 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_500);
x_502 = lean_ctor_get(x_501, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_503 = x_501;
} else {
 lean_dec_ref(x_501);
 x_503 = lean_box(0);
}
x_504 = 1;
x_505 = lean_box(x_504);
if (lean_is_scalar(x_503)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_503;
}
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_502);
return x_506;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_2);
lean_dec(x_1);
x_507 = lean_ctor_get(x_497, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_508 = x_497;
} else {
 lean_dec_ref(x_497);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(0, 2, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_498);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_2);
lean_dec(x_1);
x_510 = lean_ctor_get(x_497, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_497, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_512 = x_497;
} else {
 lean_dec_ref(x_497);
 x_512 = lean_box(0);
}
if (lean_is_scalar(x_512)) {
 x_513 = lean_alloc_ctor(1, 2, 0);
} else {
 x_513 = x_512;
}
lean_ctor_set(x_513, 0, x_510);
lean_ctor_set(x_513, 1, x_511);
return x_513;
}
}
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
lean_dec(x_485);
lean_dec(x_2);
lean_dec(x_1);
x_514 = lean_ctor_get(x_486, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_486, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_516 = x_486;
} else {
 lean_dec_ref(x_486);
 x_516 = lean_box(0);
}
if (lean_is_scalar(x_516)) {
 x_517 = lean_alloc_ctor(1, 2, 0);
} else {
 x_517 = x_516;
}
lean_ctor_set(x_517, 0, x_514);
lean_ctor_set(x_517, 1, x_515);
return x_517;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; lean_object* x_522; lean_object* x_523; 
x_518 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_403);
x_519 = lean_ctor_get(x_518, 1);
lean_inc(x_519);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 x_520 = x_518;
} else {
 lean_dec_ref(x_518);
 x_520 = lean_box(0);
}
x_521 = 1;
x_522 = lean_box(x_521);
if (lean_is_scalar(x_520)) {
 x_523 = lean_alloc_ctor(0, 2, 0);
} else {
 x_523 = x_520;
}
lean_ctor_set(x_523, 0, x_522);
lean_ctor_set(x_523, 1, x_519);
return x_523;
}
}
}
else
{
uint8_t x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_404);
lean_dec(x_2);
lean_dec(x_1);
x_524 = 0;
x_525 = lean_box(x_524);
if (lean_is_scalar(x_400)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_400;
}
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_403);
return x_526;
}
}
else
{
uint8_t x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_404);
lean_dec(x_2);
lean_dec(x_1);
x_527 = 0;
x_528 = lean_box(x_527);
if (lean_is_scalar(x_400)) {
 x_529 = lean_alloc_ctor(0, 2, 0);
} else {
 x_529 = x_400;
}
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_403);
return x_529;
}
}
}
block_448:
{
if (x_405 == 0)
{
lean_dec(x_404);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_ctor_get(x_2, 0);
lean_inc(x_407);
lean_inc(x_1);
x_408 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_1, x_3, x_4, x_5, x_6, x_406);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_407);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_410);
x_412 = lean_ctor_get(x_411, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_413 = x_411;
} else {
 lean_dec_ref(x_411);
 x_413 = lean_box(0);
}
x_414 = 1;
x_415 = lean_box(x_414);
if (lean_is_scalar(x_413)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_413;
}
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_412);
return x_416;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_417 = lean_ctor_get(x_408, 1);
lean_inc(x_417);
lean_dec(x_408);
x_418 = lean_ctor_get(x_409, 0);
lean_inc(x_418);
lean_dec(x_409);
x_419 = l_Lean_Meta_isLevelDefEqAux___main(x_407, x_418, x_3, x_4, x_5, x_6, x_417);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; uint8_t x_421; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_unbox(x_420);
if (x_421 == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_420);
x_422 = lean_ctor_get(x_419, 1);
lean_inc(x_422);
lean_dec(x_419);
x_423 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_422);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_425 = x_423;
} else {
 lean_dec_ref(x_423);
 x_425 = lean_box(0);
}
x_426 = 1;
x_427 = lean_box(x_426);
if (lean_is_scalar(x_425)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_425;
}
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_424);
return x_428;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_2);
lean_dec(x_1);
x_429 = lean_ctor_get(x_419, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_430 = x_419;
} else {
 lean_dec_ref(x_419);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_420);
lean_ctor_set(x_431, 1, x_429);
return x_431;
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_2);
lean_dec(x_1);
x_432 = lean_ctor_get(x_419, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_419, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_434 = x_419;
} else {
 lean_dec_ref(x_419);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 2, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_433);
return x_435;
}
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_407);
lean_dec(x_2);
lean_dec(x_1);
x_436 = lean_ctor_get(x_408, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_408, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_438 = x_408;
} else {
 lean_dec_ref(x_408);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; 
x_440 = l___private_Lean_Meta_LevelDefEq_7__postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_406);
x_441 = lean_ctor_get(x_440, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_442 = x_440;
} else {
 lean_dec_ref(x_440);
 x_442 = lean_box(0);
}
x_443 = 1;
x_444 = lean_box(x_443);
if (lean_is_scalar(x_442)) {
 x_445 = lean_alloc_ctor(0, 2, 0);
} else {
 x_445 = x_442;
}
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_441);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; 
lean_dec(x_2);
lean_dec(x_1);
x_446 = lean_box(x_405);
if (lean_is_scalar(x_404)) {
 x_447 = lean_alloc_ctor(0, 2, 0);
} else {
 x_447 = x_404;
}
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_406);
return x_447;
}
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_400);
lean_dec(x_2);
lean_dec(x_1);
x_530 = lean_ctor_get(x_401, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_401, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_532 = x_401;
} else {
 lean_dec_ref(x_401);
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
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_2);
lean_dec(x_1);
x_534 = lean_ctor_get(x_380, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_380, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_536 = x_380;
} else {
 lean_dec_ref(x_380);
 x_536 = lean_box(0);
}
if (lean_is_scalar(x_536)) {
 x_537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_537 = x_536;
}
lean_ctor_set(x_537, 0, x_534);
lean_ctor_set(x_537, 1, x_535);
return x_537;
}
}
}
}
}
}
else
{
uint8_t x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_2);
lean_dec(x_1);
x_561 = 1;
x_562 = lean_box(x_561);
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_7);
return x_563;
}
}
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_isLevelDefEqAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isLevelDefEqAux___main___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_isLevelDefEqAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isLevelDefEqAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_isLevelDefEqAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isLevelDefEqAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_isLevelDefEqAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isLevelDefEqAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_isListLevelDefEqAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
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
x_21 = l_Lean_Meta_isLevelDefEqAux___main(x_17, x_19, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Lean_Meta_isListLevelDefEqAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isListLevelDefEqAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_isListLevelDefEqAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isListLevelDefEqAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_isListLevelDefEqAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isListLevelDefEqAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_9__getNumPostponed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_9__getNumPostponed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_9__getNumPostponed___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_9__getNumPostponed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_LevelDefEq_9__getNumPostponed___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_9__getNumPostponed___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_LevelDefEq_9__getNumPostponed(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_10__getResetPostponed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_take(x_1, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 2);
lean_dec(x_13);
x_14 = l_Std_PersistentArray_empty___closed__3;
lean_ctor_set(x_10, 2, x_14);
x_15 = lean_st_ref_set(x_1, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_8);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_23 = l_Std_PersistentArray_empty___closed__3;
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_22);
x_25 = lean_st_ref_set(x_1, x_24, x_11);
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
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_10__getResetPostponed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_10__getResetPostponed___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_10__getResetPostponed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_LevelDefEq_10__getResetPostponed___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_10__getResetPostponed___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_LevelDefEq_10__getResetPostponed(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_box(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_fget(x_2, x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_17 = l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__2(x_14, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unbox(x_18);
lean_dec(x_18);
x_3 = x_16;
x_4 = x_20;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_box(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_fget(x_2, x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
if (x_4 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = 0;
x_3 = x_16;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Lean_Meta_isLevelDefEqAux___main(x_19, x_20, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unbox(x_22);
lean_dec(x_22);
x_3 = x_16;
x_4 = x_24;
x_9 = x_23;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
lean_object* l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__3(x_8, x_8, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__4(x_11, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_box(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_fget(x_2, x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
if (x_4 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = 0;
x_3 = x_16;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Lean_Meta_isLevelDefEqAux___main(x_19, x_20, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unbox(x_22);
lean_dec(x_22);
x_3 = x_16;
x_4 = x_24;
x_9 = x_23;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unbox(x_10);
lean_dec(x_10);
x_15 = l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__5(x_1, x_12, x_13, x_14, x_3, x_4, x_5, x_6, x_11);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 2);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = l_Std_PersistentArray_empty___closed__3;
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
x_23 = l_Std_PersistentArray_empty___closed__3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_22);
lean_ctor_set(x_9, 2, x_24);
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_32 = x_10;
} else {
 lean_dec_ref(x_10);
 x_32 = lean_box(0);
}
x_33 = l_Std_PersistentArray_empty___closed__3;
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 1, 1);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_31);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_st_ref_set(x_1, x_35, x_11);
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
lean_ctor_set(x_39, 0, x_7);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_st_ref_take(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 2);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = l_Std_PersistentArray_toArray___rarg(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Std_PersistentArray_push___rarg(x_1, x_18);
lean_ctor_set(x_10, 0, x_19);
x_20 = lean_st_ref_set(x_6, x_9, x_11);
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
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
x_28 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
lean_dec(x_10);
x_29 = l_Std_PersistentArray_toArray___rarg(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Std_PersistentArray_push___rarg(x_1, x_31);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_27);
lean_ctor_set(x_9, 2, x_33);
x_34 = lean_st_ref_set(x_6, x_9, x_11);
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
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_41 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_43 = x_10;
} else {
 lean_dec_ref(x_10);
 x_43 = lean_box(0);
}
x_44 = l_Std_PersistentArray_toArray___rarg(x_42);
lean_dec(x_42);
x_45 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Std_PersistentArray_push___rarg(x_1, x_46);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 1, 1);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_41);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_st_ref_set(x_6, x_49, x_11);
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
lean_object* _init_l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("postponed");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isLevelDefEqAux___main___closed__2;
x_2 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2;
x_2 = l_Lean_Meta_isLevelDefEqAux___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_11__processPostponedStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_19; lean_object* x_20; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_251 = lean_st_ref_get(x_4, x_5);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_252, 2);
lean_inc(x_253);
lean_dec(x_252);
x_254 = lean_ctor_get_uint8(x_253, sizeof(void*)*1);
lean_dec(x_253);
if (x_254 == 0)
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_ctor_get(x_251, 1);
lean_inc(x_255);
lean_dec(x_251);
x_256 = 0;
x_19 = x_256;
x_20 = x_255;
goto block_250;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_257 = lean_ctor_get(x_251, 1);
lean_inc(x_257);
lean_dec(x_251);
x_258 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__3;
x_259 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_258, x_1, x_2, x_3, x_4, x_257);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_unbox(x_260);
lean_dec(x_260);
x_19 = x_262;
x_20 = x_261;
goto block_250;
}
block_18:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
block_250:
{
if (x_19 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_st_ref_get(x_4, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
lean_dec(x_23);
x_26 = lean_st_ref_take(x_4, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 2);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_33 = 0;
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_33);
x_34 = lean_st_ref_set(x_4, x_27, x_29);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l___private_Lean_Meta_LevelDefEq_10__getResetPostponed___rarg(x_2, x_3, x_4, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = 1;
x_40 = l_Std_PersistentArray_foldlM___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__1(x_37, x_39, x_1, x_2, x_3, x_4, x_38);
lean_dec(x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_4, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 2);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*1);
lean_dec(x_46);
x_48 = lean_st_ref_take(x_4, x_45);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_49, 2);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_25);
x_55 = lean_st_ref_set(x_4, x_49, x_51);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = lean_box(x_47);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_41);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_55, 0, x_59);
x_6 = x_55;
goto block_18;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_box(x_47);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_41);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_6 = x_63;
goto block_18;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_50, 0);
lean_inc(x_64);
lean_dec(x_50);
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_25);
lean_ctor_set(x_49, 2, x_65);
x_66 = lean_st_ref_set(x_4, x_49, x_51);
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
x_69 = lean_box(x_47);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_41);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
x_6 = x_71;
goto block_18;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_72 = lean_ctor_get(x_49, 0);
x_73 = lean_ctor_get(x_49, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_49);
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
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_25);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_76);
x_78 = lean_st_ref_set(x_4, x_77, x_51);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_box(x_47);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_41);
lean_ctor_set(x_82, 1, x_81);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
x_6 = x_83;
goto block_18;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_84 = lean_ctor_get(x_40, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_40, 1);
lean_inc(x_85);
lean_dec(x_40);
x_86 = lean_st_ref_get(x_4, x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_st_ref_take(x_4, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_89, 2);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_90);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_25);
x_95 = lean_st_ref_set(x_4, x_89, x_91);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set_tag(x_95, 1);
lean_ctor_set(x_95, 0, x_84);
x_6 = x_95;
goto block_18;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_84);
lean_ctor_set(x_99, 1, x_98);
x_6 = x_99;
goto block_18;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_90, 0);
lean_inc(x_100);
lean_dec(x_90);
x_101 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_25);
lean_ctor_set(x_89, 2, x_101);
x_102 = lean_st_ref_set(x_4, x_89, x_91);
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
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
 lean_ctor_set_tag(x_105, 1);
}
lean_ctor_set(x_105, 0, x_84);
lean_ctor_set(x_105, 1, x_103);
x_6 = x_105;
goto block_18;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_106 = lean_ctor_get(x_89, 0);
x_107 = lean_ctor_get(x_89, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_89);
x_108 = lean_ctor_get(x_90, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_109 = x_90;
} else {
 lean_dec_ref(x_90);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 1, 1);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_25);
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_107);
lean_ctor_set(x_111, 2, x_110);
x_112 = lean_st_ref_set(x_4, x_111, x_91);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
 lean_ctor_set_tag(x_115, 1);
}
lean_ctor_set(x_115, 0, x_84);
lean_ctor_set(x_115, 1, x_113);
x_6 = x_115;
goto block_18;
}
}
}
else
{
lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; 
x_116 = lean_ctor_get(x_28, 0);
lean_inc(x_116);
lean_dec(x_28);
x_117 = 0;
x_118 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_117);
lean_ctor_set(x_27, 2, x_118);
x_119 = lean_st_ref_set(x_4, x_27, x_29);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = l___private_Lean_Meta_LevelDefEq_10__getResetPostponed___rarg(x_2, x_3, x_4, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = 1;
x_125 = l_Std_PersistentArray_foldlM___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__1(x_122, x_124, x_1, x_2, x_3, x_4, x_123);
lean_dec(x_122);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_st_ref_get(x_4, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 2);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get_uint8(x_131, sizeof(void*)*1);
lean_dec(x_131);
x_133 = lean_st_ref_take(x_4, x_130);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 lean_ctor_release(x_134, 2);
 x_139 = x_134;
} else {
 lean_dec_ref(x_134);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_141 = x_135;
} else {
 lean_dec_ref(x_135);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 1, 1);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_25);
if (lean_is_scalar(x_139)) {
 x_143 = lean_alloc_ctor(0, 3, 0);
} else {
 x_143 = x_139;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_138);
lean_ctor_set(x_143, 2, x_142);
x_144 = lean_st_ref_set(x_4, x_143, x_136);
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
x_147 = lean_box(x_132);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_126);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_146)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_146;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_145);
x_6 = x_149;
goto block_18;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_150 = lean_ctor_get(x_125, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_125, 1);
lean_inc(x_151);
lean_dec(x_125);
x_152 = lean_st_ref_get(x_4, x_151);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_st_ref_take(x_4, x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_155, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_156, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_162 = x_156;
} else {
 lean_dec_ref(x_156);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(0, 1, 1);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_25);
if (lean_is_scalar(x_160)) {
 x_164 = lean_alloc_ctor(0, 3, 0);
} else {
 x_164 = x_160;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_159);
lean_ctor_set(x_164, 2, x_163);
x_165 = lean_st_ref_set(x_4, x_164, x_157);
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
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
 lean_ctor_set_tag(x_168, 1);
}
lean_ctor_set(x_168, 0, x_150);
lean_ctor_set(x_168, 1, x_166);
x_6 = x_168;
goto block_18;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; 
x_169 = lean_ctor_get(x_27, 0);
x_170 = lean_ctor_get(x_27, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_27);
x_171 = lean_ctor_get(x_28, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_172 = x_28;
} else {
 lean_dec_ref(x_28);
 x_172 = lean_box(0);
}
x_173 = 0;
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 1, 1);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_173);
x_175 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_175, 0, x_169);
lean_ctor_set(x_175, 1, x_170);
lean_ctor_set(x_175, 2, x_174);
x_176 = lean_st_ref_set(x_4, x_175, x_29);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = l___private_Lean_Meta_LevelDefEq_10__getResetPostponed___rarg(x_2, x_3, x_4, x_177);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = 1;
x_182 = l_Std_PersistentArray_foldlM___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__1(x_179, x_181, x_1, x_2, x_3, x_4, x_180);
lean_dec(x_179);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_st_ref_get(x_4, x_184);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_ctor_get(x_186, 2);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_ctor_get_uint8(x_188, sizeof(void*)*1);
lean_dec(x_188);
x_190 = lean_st_ref_take(x_4, x_187);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_191, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec(x_190);
x_194 = lean_ctor_get(x_191, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 lean_ctor_release(x_191, 2);
 x_196 = x_191;
} else {
 lean_dec_ref(x_191);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_192, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_198 = x_192;
} else {
 lean_dec_ref(x_192);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 1, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_25);
if (lean_is_scalar(x_196)) {
 x_200 = lean_alloc_ctor(0, 3, 0);
} else {
 x_200 = x_196;
}
lean_ctor_set(x_200, 0, x_194);
lean_ctor_set(x_200, 1, x_195);
lean_ctor_set(x_200, 2, x_199);
x_201 = lean_st_ref_set(x_4, x_200, x_193);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
x_204 = lean_box(x_189);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_183);
lean_ctor_set(x_205, 1, x_204);
if (lean_is_scalar(x_203)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_203;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_202);
x_6 = x_206;
goto block_18;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_207 = lean_ctor_get(x_182, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_182, 1);
lean_inc(x_208);
lean_dec(x_182);
x_209 = lean_st_ref_get(x_4, x_208);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_211 = lean_st_ref_take(x_4, x_210);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_212, 2);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 lean_ctor_release(x_212, 2);
 x_217 = x_212;
} else {
 lean_dec_ref(x_212);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_213, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_219 = x_213;
} else {
 lean_dec_ref(x_213);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(0, 1, 1);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set_uint8(x_220, sizeof(void*)*1, x_25);
if (lean_is_scalar(x_217)) {
 x_221 = lean_alloc_ctor(0, 3, 0);
} else {
 x_221 = x_217;
}
lean_ctor_set(x_221, 0, x_215);
lean_ctor_set(x_221, 1, x_216);
lean_ctor_set(x_221, 2, x_220);
x_222 = lean_st_ref_set(x_4, x_221, x_214);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
 lean_ctor_set_tag(x_225, 1);
}
lean_ctor_set(x_225, 0, x_207);
lean_ctor_set(x_225, 1, x_223);
x_6 = x_225;
goto block_18;
}
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; 
x_226 = l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___rarg(x_4, x_20);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = l___private_Lean_Meta_LevelDefEq_10__getResetPostponed___rarg(x_2, x_3, x_4, x_228);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = 1;
x_233 = l_Std_PersistentArray_foldlM___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__1(x_230, x_232, x_1, x_2, x_3, x_4, x_231);
lean_dec(x_230);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__3;
x_237 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_227, x_236, x_1, x_2, x_3, x_4, x_235);
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_237, 0);
lean_dec(x_239);
lean_ctor_set(x_237, 0, x_234);
return x_237;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_234);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_242 = lean_ctor_get(x_233, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_233, 1);
lean_inc(x_243);
lean_dec(x_233);
x_244 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__3;
x_245 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_227, x_244, x_1, x_2, x_3, x_4, x_243);
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_245, 0);
lean_dec(x_247);
lean_ctor_set_tag(x_245, 1);
lean_ctor_set(x_245, 0, x_242);
return x_245;
}
else
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_248);
lean_dec(x_245);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_242);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__3(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__4(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Array_iterateMAux___main___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__5(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Std_PersistentArray_foldlM___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("processing #");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" postponed is-def-eq level constraints");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Nat_repr(x_1);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__3;
x_7 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__6;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
lean_object* _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no progress solving pending is-def-eq level constraints");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__3;
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lean_Meta_LevelDefEq_9__getNumPostponed___rarg(x_2, x_3, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_6);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_8);
x_13 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2;
x_14 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_13, x_12, x_1, x_2, x_3, x_4, x_9);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep(x_1, x_2, x_3, x_4, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_17);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = l___private_Lean_Meta_LevelDefEq_9__getNumPostponed___rarg(x_2, x_3, x_4, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_nat_dec_eq(x_26, x_10);
if (x_28 == 0)
{
uint8_t x_29; 
lean_free_object(x_24);
x_29 = lean_nat_dec_lt(x_26, x_8);
lean_dec(x_8);
lean_dec(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___closed__1;
x_31 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_13, x_30, x_1, x_2, x_3, x_4, x_27);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = 0;
x_35 = lean_box(x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
x_5 = x_27;
goto _start;
}
}
else
{
uint8_t x_41; lean_object* x_42; 
lean_dec(x_26);
lean_dec(x_8);
x_41 = 1;
x_42 = lean_box(x_41);
lean_ctor_set(x_24, 0, x_42);
return x_24;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_24, 0);
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_24);
x_45 = lean_nat_dec_eq(x_43, x_10);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = lean_nat_dec_lt(x_43, x_8);
lean_dec(x_8);
lean_dec(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_47 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___closed__1;
x_48 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_13, x_47, x_1, x_2, x_3, x_4, x_44);
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
x_51 = 0;
x_52 = lean_box(x_51);
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
x_5 = x_44;
goto _start;
}
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_43);
lean_dec(x_8);
x_55 = 1;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_44);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_8);
x_58 = !lean_is_exclusive(x_16);
if (x_58 == 0)
{
return x_16;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_16, 0);
x_60 = lean_ctor_get(x_16, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_16);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; lean_object* x_63; 
lean_dec(x_8);
x_62 = 1;
x_63 = lean_box(x_62);
lean_ctor_set(x_6, 0, x_63);
return x_6;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_6, 0);
x_65 = lean_ctor_get(x_6, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_6);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_64, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_inc(x_64);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_68, 0, x_64);
x_69 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2;
x_70 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_69, x_68, x_1, x_2, x_3, x_4, x_65);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep(x_1, x_2, x_3, x_4, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_64);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_73);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = l___private_Lean_Meta_LevelDefEq_9__getNumPostponed___rarg(x_2, x_3, x_4, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_nat_dec_eq(x_80, x_66);
if (x_83 == 0)
{
uint8_t x_84; 
lean_dec(x_82);
x_84 = lean_nat_dec_lt(x_80, x_64);
lean_dec(x_64);
lean_dec(x_80);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_85 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___closed__1;
x_86 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_69, x_85, x_1, x_2, x_3, x_4, x_81);
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
x_89 = 0;
x_90 = lean_box(x_89);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
return x_91;
}
else
{
x_5 = x_81;
goto _start;
}
}
else
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_80);
lean_dec(x_64);
x_93 = 1;
x_94 = lean_box(x_93);
if (lean_is_scalar(x_82)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_82;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_81);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_64);
x_96 = lean_ctor_get(x_72, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_72, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_98 = x_72;
} else {
 lean_dec_ref(x_72);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
uint8_t x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_64);
x_100 = 1;
x_101 = lean_box(x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_65);
return x_102;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_13__processPostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lean_Meta_LevelDefEq_9__getNumPostponed___rarg(x_2, x_3, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_8, x_10);
lean_dec(x_8);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_free_object(x_6);
x_207 = lean_st_ref_get(x_4, x_9);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_208, 2);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_ctor_get_uint8(x_209, sizeof(void*)*1);
lean_dec(x_209);
if (x_210 == 0)
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_ctor_get(x_207, 1);
lean_inc(x_211);
lean_dec(x_207);
x_212 = 0;
x_12 = x_212;
x_13 = x_211;
goto block_206;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_213 = lean_ctor_get(x_207, 1);
lean_inc(x_213);
lean_dec(x_207);
x_214 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2;
x_215 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_214, x_1, x_2, x_3, x_4, x_213);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_unbox(x_216);
lean_dec(x_216);
x_12 = x_218;
x_13 = x_217;
goto block_206;
}
block_206:
{
if (x_12 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_st_ref_get(x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
lean_dec(x_16);
x_19 = lean_st_ref_take(x_4, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 2);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = 0;
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_26);
x_27 = lean_st_ref_set(x_4, x_20, x_22);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg(x_1, x_2, x_3, x_4, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_4, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_take(x_4, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_35, 2);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_18);
x_41 = lean_st_ref_set(x_4, x_35, x_37);
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
lean_ctor_set(x_35, 2, x_47);
x_48 = lean_st_ref_set(x_4, x_35, x_37);
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_54 = lean_ctor_get(x_36, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_55 = x_36;
} else {
 lean_dec_ref(x_36);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 1, 1);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_18);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_st_ref_set(x_4, x_57, x_37);
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
lean_ctor_set(x_61, 0, x_30);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_62 = lean_ctor_get(x_29, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_29, 1);
lean_inc(x_63);
lean_dec(x_29);
x_64 = lean_st_ref_get(x_4, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_take(x_4, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_67, 2);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_18);
x_73 = lean_st_ref_set(x_4, x_67, x_69);
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
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_18);
lean_ctor_set(x_67, 2, x_79);
x_80 = lean_st_ref_set(x_4, x_67, x_69);
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
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_67, 0);
x_85 = lean_ctor_get(x_67, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_67);
x_86 = lean_ctor_get(x_68, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_87 = x_68;
} else {
 lean_dec_ref(x_68);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 1, 1);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_18);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_88);
x_90 = lean_st_ref_set(x_4, x_89, x_69);
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
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
 lean_ctor_set_tag(x_93, 1);
}
lean_ctor_set(x_93, 0, x_62);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_21, 0);
lean_inc(x_94);
lean_dec(x_21);
x_95 = 0;
x_96 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_95);
lean_ctor_set(x_20, 2, x_96);
x_97 = lean_st_ref_set(x_4, x_20, x_22);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg(x_1, x_2, x_3, x_4, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_st_ref_get(x_4, x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_st_ref_take(x_4, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_105, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 lean_ctor_release(x_105, 2);
 x_110 = x_105;
} else {
 lean_dec_ref(x_105);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_112 = x_106;
} else {
 lean_dec_ref(x_106);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 1, 1);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_18);
if (lean_is_scalar(x_110)) {
 x_114 = lean_alloc_ctor(0, 3, 0);
} else {
 x_114 = x_110;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_113);
x_115 = lean_st_ref_set(x_4, x_114, x_107);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_100);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_119 = lean_ctor_get(x_99, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_99, 1);
lean_inc(x_120);
lean_dec(x_99);
x_121 = lean_st_ref_get(x_4, x_120);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_st_ref_take(x_4, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 x_129 = x_124;
} else {
 lean_dec_ref(x_124);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 1, 1);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_18);
if (lean_is_scalar(x_129)) {
 x_133 = lean_alloc_ctor(0, 3, 0);
} else {
 x_133 = x_129;
}
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_128);
lean_ctor_set(x_133, 2, x_132);
x_134 = lean_st_ref_set(x_4, x_133, x_126);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
 lean_ctor_set_tag(x_137, 1);
}
lean_ctor_set(x_137, 0, x_119);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_138 = lean_ctor_get(x_20, 0);
x_139 = lean_ctor_get(x_20, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_20);
x_140 = lean_ctor_get(x_21, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_141 = x_21;
} else {
 lean_dec_ref(x_21);
 x_141 = lean_box(0);
}
x_142 = 0;
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 1, 1);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set_uint8(x_143, sizeof(void*)*1, x_142);
x_144 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_139);
lean_ctor_set(x_144, 2, x_143);
x_145 = lean_st_ref_set(x_4, x_144, x_22);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg(x_1, x_2, x_3, x_4, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_st_ref_get(x_4, x_149);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_st_ref_take(x_4, x_151);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_153, 2);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 x_158 = x_153;
} else {
 lean_dec_ref(x_153);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_154, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 x_160 = x_154;
} else {
 lean_dec_ref(x_154);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(0, 1, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set_uint8(x_161, sizeof(void*)*1, x_18);
if (lean_is_scalar(x_158)) {
 x_162 = lean_alloc_ctor(0, 3, 0);
} else {
 x_162 = x_158;
}
lean_ctor_set(x_162, 0, x_156);
lean_ctor_set(x_162, 1, x_157);
lean_ctor_set(x_162, 2, x_161);
x_163 = lean_st_ref_set(x_4, x_162, x_155);
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
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_148);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_167 = lean_ctor_get(x_147, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_147, 1);
lean_inc(x_168);
lean_dec(x_147);
x_169 = lean_st_ref_get(x_4, x_168);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_st_ref_take(x_4, x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_172, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 x_177 = x_172;
} else {
 lean_dec_ref(x_172);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_173, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_179 = x_173;
} else {
 lean_dec_ref(x_173);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 1, 1);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set_uint8(x_180, sizeof(void*)*1, x_18);
if (lean_is_scalar(x_177)) {
 x_181 = lean_alloc_ctor(0, 3, 0);
} else {
 x_181 = x_177;
}
lean_ctor_set(x_181, 0, x_175);
lean_ctor_set(x_181, 1, x_176);
lean_ctor_set(x_181, 2, x_180);
x_182 = lean_st_ref_set(x_4, x_181, x_174);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_184 = x_182;
} else {
 lean_dec_ref(x_182);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
 lean_ctor_set_tag(x_185, 1);
}
lean_ctor_set(x_185, 0, x_167);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___rarg(x_4, x_13);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg(x_1, x_2, x_3, x_4, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2;
x_193 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_187, x_192, x_1, x_2, x_3, x_4, x_191);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_193, 0);
lean_dec(x_195);
lean_ctor_set(x_193, 0, x_190);
return x_193;
}
else
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_190);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_198 = lean_ctor_get(x_189, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_189, 1);
lean_inc(x_199);
lean_dec(x_189);
x_200 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2;
x_201 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_187, x_200, x_1, x_2, x_3, x_4, x_199);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_201, 0);
lean_dec(x_203);
lean_ctor_set_tag(x_201, 1);
lean_ctor_set(x_201, 0, x_198);
return x_201;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
lean_dec(x_201);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_198);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
}
}
else
{
uint8_t x_219; lean_object* x_220; 
x_219 = 1;
x_220 = lean_box(x_219);
lean_ctor_set(x_6, 0, x_220);
return x_6;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_221 = lean_ctor_get(x_6, 0);
x_222 = lean_ctor_get(x_6, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_6);
x_223 = lean_unsigned_to_nat(0u);
x_224 = lean_nat_dec_eq(x_221, x_223);
lean_dec(x_221);
if (x_224 == 0)
{
uint8_t x_225; lean_object* x_226; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_304 = lean_st_ref_get(x_4, x_222);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_305, 2);
lean_inc(x_306);
lean_dec(x_305);
x_307 = lean_ctor_get_uint8(x_306, sizeof(void*)*1);
lean_dec(x_306);
if (x_307 == 0)
{
lean_object* x_308; uint8_t x_309; 
x_308 = lean_ctor_get(x_304, 1);
lean_inc(x_308);
lean_dec(x_304);
x_309 = 0;
x_225 = x_309;
x_226 = x_308;
goto block_303;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_310 = lean_ctor_get(x_304, 1);
lean_inc(x_310);
lean_dec(x_304);
x_311 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2;
x_312 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_311, x_1, x_2, x_3, x_4, x_310);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_unbox(x_313);
lean_dec(x_313);
x_225 = x_315;
x_226 = x_314;
goto block_303;
}
block_303:
{
if (x_225 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_227 = lean_st_ref_get(x_4, x_226);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_228, 2);
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec(x_227);
x_231 = lean_ctor_get_uint8(x_229, sizeof(void*)*1);
lean_dec(x_229);
x_232 = lean_st_ref_take(x_4, x_230);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_233, 2);
lean_inc(x_234);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
lean_dec(x_232);
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_233, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 lean_ctor_release(x_233, 2);
 x_238 = x_233;
} else {
 lean_dec_ref(x_233);
 x_238 = lean_box(0);
}
x_239 = lean_ctor_get(x_234, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 x_240 = x_234;
} else {
 lean_dec_ref(x_234);
 x_240 = lean_box(0);
}
x_241 = 0;
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(0, 1, 1);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set_uint8(x_242, sizeof(void*)*1, x_241);
if (lean_is_scalar(x_238)) {
 x_243 = lean_alloc_ctor(0, 3, 0);
} else {
 x_243 = x_238;
}
lean_ctor_set(x_243, 0, x_236);
lean_ctor_set(x_243, 1, x_237);
lean_ctor_set(x_243, 2, x_242);
x_244 = lean_st_ref_set(x_4, x_243, x_235);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
x_246 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg(x_1, x_2, x_3, x_4, x_245);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_st_ref_get(x_4, x_248);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
lean_dec(x_249);
x_251 = lean_st_ref_take(x_4, x_250);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_252, 2);
lean_inc(x_253);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_ctor_get(x_252, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_252, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 lean_ctor_release(x_252, 2);
 x_257 = x_252;
} else {
 lean_dec_ref(x_252);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_253, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_259 = x_253;
} else {
 lean_dec_ref(x_253);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(0, 1, 1);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set_uint8(x_260, sizeof(void*)*1, x_231);
if (lean_is_scalar(x_257)) {
 x_261 = lean_alloc_ctor(0, 3, 0);
} else {
 x_261 = x_257;
}
lean_ctor_set(x_261, 0, x_255);
lean_ctor_set(x_261, 1, x_256);
lean_ctor_set(x_261, 2, x_260);
x_262 = lean_st_ref_set(x_4, x_261, x_254);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_264 = x_262;
} else {
 lean_dec_ref(x_262);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_247);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_266 = lean_ctor_get(x_246, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_246, 1);
lean_inc(x_267);
lean_dec(x_246);
x_268 = lean_st_ref_get(x_4, x_267);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_270 = lean_st_ref_take(x_4, x_269);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_271, 2);
lean_inc(x_272);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec(x_270);
x_274 = lean_ctor_get(x_271, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_271, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 x_276 = x_271;
} else {
 lean_dec_ref(x_271);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_272, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 x_278 = x_272;
} else {
 lean_dec_ref(x_272);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 1, 1);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set_uint8(x_279, sizeof(void*)*1, x_231);
if (lean_is_scalar(x_276)) {
 x_280 = lean_alloc_ctor(0, 3, 0);
} else {
 x_280 = x_276;
}
lean_ctor_set(x_280, 0, x_274);
lean_ctor_set(x_280, 1, x_275);
lean_ctor_set(x_280, 2, x_279);
x_281 = lean_st_ref_set(x_4, x_280, x_273);
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
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
 lean_ctor_set_tag(x_284, 1);
}
lean_ctor_set(x_284, 0, x_266);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___rarg(x_4, x_226);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg(x_1, x_2, x_3, x_4, x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_291 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2;
x_292 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_286, x_291, x_1, x_2, x_3, x_4, x_290);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_294 = x_292;
} else {
 lean_dec_ref(x_292);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_289);
lean_ctor_set(x_295, 1, x_293);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_296 = lean_ctor_get(x_288, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_288, 1);
lean_inc(x_297);
lean_dec(x_288);
x_298 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2;
x_299 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_286, x_298, x_1, x_2, x_3, x_4, x_297);
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_301 = x_299;
} else {
 lean_dec_ref(x_299);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
 lean_ctor_set_tag(x_302, 1);
}
lean_ctor_set(x_302, 0, x_296);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
}
}
else
{
uint8_t x_316; lean_object* x_317; lean_object* x_318; 
x_316 = 1;
x_317 = lean_box(x_316);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_222);
return x_318;
}
}
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_13__processPostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 0, x_2);
x_17 = lean_st_ref_set(x_5, x_12, x_13);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_3);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_st_ref_set(x_5, x_26, x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
lean_object* l_Lean_Meta_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_restore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_3, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_st_ref_take(x_3, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_32; 
x_20 = lean_ctor_get(x_17, 2);
lean_dec(x_20);
x_21 = l_Std_PersistentArray_empty___closed__3;
lean_ctor_set(x_17, 2, x_21);
x_22 = lean_st_ref_set(x_3, x_17, x_18);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_32 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_restore(x_10, x_14, x_15, x_2, x_3, x_4, x_5, x_34);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_33);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_2, x_3, x_4, x_5, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_33);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lean_Meta_restore(x_10, x_14, x_15, x_2, x_3, x_4, x_5, x_44);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_41, 0);
lean_dec(x_53);
lean_ctor_set(x_41, 0, x_33);
return x_41;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_dec(x_41);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_33);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_33);
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
lean_dec(x_41);
x_24 = x_56;
x_25 = x_57;
goto block_31;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_32, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_32, 1);
lean_inc(x_59);
lean_dec(x_32);
x_24 = x_58;
x_25 = x_59;
goto block_31;
}
block_31:
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Meta_restore(x_10, x_14, x_15, x_2, x_3, x_4, x_5, x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_74; 
x_60 = lean_ctor_get(x_17, 0);
x_61 = lean_ctor_get(x_17, 1);
x_62 = lean_ctor_get(x_17, 3);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_17);
x_63 = l_Std_PersistentArray_empty___closed__3;
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_62);
x_65 = lean_st_ref_set(x_3, x_64, x_18);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_74 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_66);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Meta_restore(x_10, x_14, x_15, x_2, x_3, x_4, x_5, x_76);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
lean_dec(x_74);
x_82 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_2, x_3, x_4, x_5, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = l_Lean_Meta_restore(x_10, x_14, x_15, x_2, x_3, x_4, x_5, x_85);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_92 = x_82;
} else {
 lean_dec_ref(x_82);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_75);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
x_94 = lean_ctor_get(x_82, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_82, 1);
lean_inc(x_95);
lean_dec(x_82);
x_67 = x_94;
x_68 = x_95;
goto block_73;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_74, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_74, 1);
lean_inc(x_97);
lean_dec(x_74);
x_67 = x_96;
x_68 = x_97;
goto block_73;
}
block_73:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = l_Lean_Meta_restore(x_10, x_14, x_15, x_2, x_3, x_4, x_5, x_68);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_commitWhenSome_x3f___rarg), 6, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_commitWhen___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_commitWhen___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_1 == 0)
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
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Meta_commitWhen___lambda__1___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
lean_object* _init_l_Lean_Meta_commitWhen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_commitWhen___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_commitWhen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__2;
x_8 = l_Lean_Meta_commitWhen___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, lean_box(0));
lean_closure_set(x_9, 3, x_1);
lean_closure_set(x_9, 4, x_8);
x_10 = l_Lean_Meta_commitWhenSome_x3f___rarg(x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
uint8_t x_20; 
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
x_22 = 1;
x_23 = lean_box(x_22);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Meta_commitWhen___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_Meta_commitWhen___lambda__1(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_14__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_isLevelDefEqAux___main___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_isLevelDefEqAux___main___closed__4;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2;
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
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isLevelDefEq___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAux___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_st_ref_take(x_4, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_19, 2);
lean_dec(x_22);
x_23 = l_Std_PersistentArray_empty___closed__3;
lean_ctor_set(x_19, 2, x_23);
x_24 = lean_st_ref_set(x_4, x_19, x_20);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_34 = l_Lean_Meta_commitWhen___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_8, x_34, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_36);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_44);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_44, 0);
lean_dec(x_56);
lean_ctor_set(x_44, 0, x_36);
return x_44;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_dec(x_44);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_36);
x_59 = lean_ctor_get(x_44, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
lean_dec(x_44);
x_26 = x_59;
x_27 = x_60;
goto block_33;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_35, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_dec(x_35);
x_26 = x_61;
x_27 = x_62;
goto block_33;
}
block_33:
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_77; lean_object* x_78; 
x_63 = lean_ctor_get(x_19, 0);
x_64 = lean_ctor_get(x_19, 1);
x_65 = lean_ctor_get(x_19, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_19);
x_66 = l_Std_PersistentArray_empty___closed__3;
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_65);
x_68 = lean_st_ref_set(x_4, x_67, x_20);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_77 = l_Lean_Meta_commitWhen___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_78 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_8, x_77, x_3, x_4, x_5, x_6, x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_80);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_3, x_4, x_5, x_6, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_79);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_89);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_96 = x_86;
} else {
 lean_dec_ref(x_86);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_79);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_79);
x_98 = lean_ctor_get(x_86, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_86, 1);
lean_inc(x_99);
lean_dec(x_86);
x_70 = x_98;
x_71 = x_99;
goto block_76;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
lean_dec(x_78);
x_70 = x_100;
x_71 = x_101;
goto block_76;
}
block_76:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_71);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
 lean_ctor_set_tag(x_75, 1);
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_isLevelDefEq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isLevelDefEq___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_dec(x_8);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isLevelDefEq___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAux___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_st_ref_take(x_4, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_19, 2);
lean_dec(x_22);
x_23 = l_Std_PersistentArray_empty___closed__3;
lean_ctor_set(x_19, 2, x_23);
x_24 = lean_st_ref_set(x_4, x_19, x_20);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_34 = l_Lean_Meta_commitWhen___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_8, x_34, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_36);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_44);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_44, 0);
lean_dec(x_56);
lean_ctor_set(x_44, 0, x_36);
return x_44;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_dec(x_44);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_36);
x_59 = lean_ctor_get(x_44, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
lean_dec(x_44);
x_26 = x_59;
x_27 = x_60;
goto block_33;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_35, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_dec(x_35);
x_26 = x_61;
x_27 = x_62;
goto block_33;
}
block_33:
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_77; lean_object* x_78; 
x_63 = lean_ctor_get(x_19, 0);
x_64 = lean_ctor_get(x_19, 1);
x_65 = lean_ctor_get(x_19, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_19);
x_66 = l_Std_PersistentArray_empty___closed__3;
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_65);
x_68 = lean_st_ref_set(x_4, x_67, x_20);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_77 = l_Lean_Meta_commitWhen___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_78 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_8, x_77, x_3, x_4, x_5, x_6, x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_80);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_3, x_4, x_5, x_6, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_79);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_89);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_96 = x_86;
} else {
 lean_dec_ref(x_86);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_79);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_79);
x_98 = lean_ctor_get(x_86, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_86, 1);
lean_inc(x_99);
lean_dec(x_86);
x_70 = x_98;
x_71 = x_99;
goto block_76;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
lean_dec(x_78);
x_70 = x_100;
x_71 = x_101;
goto block_76;
}
block_76:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_71);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
 lean_ctor_set_tag(x_75, 1);
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_isLevelDefEq___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isLevelDefEq___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_dec(x_8);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
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
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ... ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failure");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("success");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3;
x_7 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
if (x_3 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__9;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_4 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_8, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 2);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_58; 
x_22 = 0;
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_22);
x_23 = lean_st_ref_set(x_8, x_16, x_18);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_Meta_commitWhen___at_Lean_Meta_isLevelDefEq___spec__1(x_1, x_2, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_59);
x_61 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___boxed), 4, 3);
lean_closure_set(x_61, 0, x_1);
lean_closure_set(x_61, 1, x_2);
lean_closure_set(x_61, 2, x_59);
x_62 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_3, x_61, x_5, x_6, x_7, x_8, x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_st_ref_get(x_8, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_take(x_8, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_67, 2);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_14);
x_73 = lean_st_ref_set(x_8, x_67, x_69);
lean_dec(x_8);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
lean_ctor_set(x_73, 0, x_59);
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_59);
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
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_14);
lean_ctor_set(x_67, 2, x_79);
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
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_59);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_67, 0);
x_85 = lean_ctor_get(x_67, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_67);
x_86 = lean_ctor_get(x_68, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_87 = x_68;
} else {
 lean_dec_ref(x_68);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 1, 1);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_14);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_88);
x_90 = lean_st_ref_set(x_8, x_89, x_69);
lean_dec(x_8);
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
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_59);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_58, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_58, 1);
lean_inc(x_95);
lean_dec(x_58);
x_25 = x_94;
x_26 = x_95;
goto block_57;
}
block_57:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_st_ref_get(x_8, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_take(x_8, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 2);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_14);
x_36 = lean_st_ref_set(x_8, x_30, x_32);
lean_dec(x_8);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_25);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_14);
lean_ctor_set(x_30, 2, x_42);
x_43 = lean_st_ref_set(x_8, x_30, x_32);
lean_dec(x_8);
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
lean_ctor_set(x_46, 0, x_25);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
x_49 = lean_ctor_get(x_31, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_50 = x_31;
} else {
 lean_dec_ref(x_31);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 1, 1);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_14);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_51);
x_53 = lean_st_ref_set(x_8, x_52, x_32);
lean_dec(x_8);
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
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_25);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_121; 
x_96 = lean_ctor_get(x_17, 0);
lean_inc(x_96);
lean_dec(x_17);
x_97 = 0;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
lean_ctor_set(x_16, 2, x_98);
x_99 = lean_st_ref_set(x_8, x_16, x_18);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_121 = l_Lean_Meta_commitWhen___at_Lean_Meta_isLevelDefEq___spec__1(x_1, x_2, x_5, x_6, x_7, x_8, x_100);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_122);
x_124 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___boxed), 4, 3);
lean_closure_set(x_124, 0, x_1);
lean_closure_set(x_124, 1, x_2);
lean_closure_set(x_124, 2, x_122);
x_125 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_3, x_124, x_5, x_6, x_7, x_8, x_123);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_st_ref_get(x_8, x_126);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_st_ref_take(x_8, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 x_135 = x_130;
} else {
 lean_dec_ref(x_130);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_131, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_137 = x_131;
} else {
 lean_dec_ref(x_131);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 1, 1);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set_uint8(x_138, sizeof(void*)*1, x_14);
if (lean_is_scalar(x_135)) {
 x_139 = lean_alloc_ctor(0, 3, 0);
} else {
 x_139 = x_135;
}
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_139, 2, x_138);
x_140 = lean_st_ref_set(x_8, x_139, x_132);
lean_dec(x_8);
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
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_122);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_144 = lean_ctor_get(x_121, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_121, 1);
lean_inc(x_145);
lean_dec(x_121);
x_101 = x_144;
x_102 = x_145;
goto block_120;
}
block_120:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_103 = lean_st_ref_get(x_8, x_102);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_st_ref_take(x_8, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 x_111 = x_106;
} else {
 lean_dec_ref(x_106);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_113 = x_107;
} else {
 lean_dec_ref(x_107);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 1, 1);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_14);
if (lean_is_scalar(x_111)) {
 x_115 = lean_alloc_ctor(0, 3, 0);
} else {
 x_115 = x_111;
}
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_110);
lean_ctor_set(x_115, 2, x_114);
x_116 = lean_st_ref_set(x_8, x_115, x_108);
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
lean_ctor_set(x_119, 0, x_101);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_175; 
x_146 = lean_ctor_get(x_16, 0);
x_147 = lean_ctor_get(x_16, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_16);
x_148 = lean_ctor_get(x_17, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_149 = x_17;
} else {
 lean_dec_ref(x_17);
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
x_152 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_152, 0, x_146);
lean_ctor_set(x_152, 1, x_147);
lean_ctor_set(x_152, 2, x_151);
x_153 = lean_st_ref_set(x_8, x_152, x_18);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_175 = l_Lean_Meta_commitWhen___at_Lean_Meta_isLevelDefEq___spec__1(x_1, x_2, x_5, x_6, x_7, x_8, x_154);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
lean_inc(x_176);
x_178 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___boxed), 4, 3);
lean_closure_set(x_178, 0, x_1);
lean_closure_set(x_178, 1, x_2);
lean_closure_set(x_178, 2, x_176);
x_179 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_3, x_178, x_5, x_6, x_7, x_8, x_177);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_st_ref_get(x_8, x_180);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_st_ref_take(x_8, x_182);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_184, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_187 = lean_ctor_get(x_184, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 x_189 = x_184;
} else {
 lean_dec_ref(x_184);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_185, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_191 = x_185;
} else {
 lean_dec_ref(x_185);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(0, 1, 1);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set_uint8(x_192, sizeof(void*)*1, x_14);
if (lean_is_scalar(x_189)) {
 x_193 = lean_alloc_ctor(0, 3, 0);
} else {
 x_193 = x_189;
}
lean_ctor_set(x_193, 0, x_187);
lean_ctor_set(x_193, 1, x_188);
lean_ctor_set(x_193, 2, x_192);
x_194 = lean_st_ref_set(x_8, x_193, x_186);
lean_dec(x_8);
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
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_176);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_ctor_get(x_175, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_175, 1);
lean_inc(x_199);
lean_dec(x_175);
x_155 = x_198;
x_156 = x_199;
goto block_174;
}
block_174:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_157 = lean_st_ref_get(x_8, x_156);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_st_ref_take(x_8, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 x_165 = x_160;
} else {
 lean_dec_ref(x_160);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_161, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_167 = x_161;
} else {
 lean_dec_ref(x_161);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 1, 1);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_14);
if (lean_is_scalar(x_165)) {
 x_169 = lean_alloc_ctor(0, 3, 0);
} else {
 x_169 = x_165;
}
lean_ctor_set(x_169, 0, x_163);
lean_ctor_set(x_169, 1, x_164);
lean_ctor_set(x_169, 2, x_168);
x_170 = lean_st_ref_set(x_8, x_169, x_162);
lean_dec(x_8);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
 lean_ctor_set_tag(x_173, 1);
}
lean_ctor_set(x_173, 0, x_155);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___rarg(x_8, x_9);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_203 = l_Lean_Meta_commitWhen___at_Lean_Meta_isLevelDefEq___spec__3(x_1, x_2, x_5, x_6, x_7, x_8, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
lean_inc(x_204);
x_206 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___boxed), 4, 3);
lean_closure_set(x_206, 0, x_1);
lean_closure_set(x_206, 1, x_2);
lean_closure_set(x_206, 2, x_204);
lean_inc(x_3);
x_207 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_3, x_206, x_5, x_6, x_7, x_8, x_205);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_201, x_3, x_5, x_6, x_7, x_8, x_208);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_209, 0);
lean_dec(x_211);
lean_ctor_set(x_209, 0, x_204);
return x_209;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_204);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
lean_dec(x_2);
lean_dec(x_1);
x_214 = lean_ctor_get(x_203, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_203, 1);
lean_inc(x_215);
lean_dec(x_203);
x_216 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_201, x_3, x_5, x_6, x_7, x_8, x_215);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_216, 0);
lean_dec(x_218);
lean_ctor_set_tag(x_216, 1);
lean_ctor_set(x_216, 0, x_214);
return x_216;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_214);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEqAux___main___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg___lambda__2___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_isLevelDefEq___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___closed__2;
x_2 = l_Lean_Meta_isLevelDefEq___rarg___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_isLevelDefEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Meta_isLevelDefEqAux___main___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg___lambda__4___boxed), 9, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
x_6 = l_Lean_Meta_isLevelDefEq___rarg___closed__4;
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_isLevelDefEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_isLevelDefEq___rarg___lambda__4(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isExprDefEq___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_st_ref_take(x_4, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_19, 2);
lean_dec(x_22);
x_23 = l_Std_PersistentArray_empty___closed__3;
lean_ctor_set(x_19, 2, x_23);
x_24 = lean_st_ref_set(x_4, x_19, x_20);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_34 = l_Lean_Meta_commitWhen___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_8, x_34, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_36);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_44);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_44, 0);
lean_dec(x_56);
lean_ctor_set(x_44, 0, x_36);
return x_44;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_dec(x_44);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_36);
x_59 = lean_ctor_get(x_44, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
lean_dec(x_44);
x_26 = x_59;
x_27 = x_60;
goto block_33;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_35, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_dec(x_35);
x_26 = x_61;
x_27 = x_62;
goto block_33;
}
block_33:
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_77; lean_object* x_78; 
x_63 = lean_ctor_get(x_19, 0);
x_64 = lean_ctor_get(x_19, 1);
x_65 = lean_ctor_get(x_19, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_19);
x_66 = l_Std_PersistentArray_empty___closed__3;
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_65);
x_68 = lean_st_ref_set(x_4, x_67, x_20);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_77 = l_Lean_Meta_commitWhen___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_78 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_8, x_77, x_3, x_4, x_5, x_6, x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_80);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_3, x_4, x_5, x_6, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_79);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_89);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_96 = x_86;
} else {
 lean_dec_ref(x_86);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_79);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_79);
x_98 = lean_ctor_get(x_86, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_86, 1);
lean_inc(x_99);
lean_dec(x_86);
x_70 = x_98;
x_71 = x_99;
goto block_76;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
lean_dec(x_78);
x_70 = x_100;
x_71 = x_101;
goto block_76;
}
block_76:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_71);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
 lean_ctor_set_tag(x_75, 1);
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_isExprDefEq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isExprDefEq___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_dec(x_8);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isExprDefEq___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_st_ref_take(x_4, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_19, 2);
lean_dec(x_22);
x_23 = l_Std_PersistentArray_empty___closed__3;
lean_ctor_set(x_19, 2, x_23);
x_24 = lean_st_ref_set(x_4, x_19, x_20);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_34 = l_Lean_Meta_commitWhen___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_8, x_34, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_36);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_44);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_44, 0);
lean_dec(x_56);
lean_ctor_set(x_44, 0, x_36);
return x_44;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_dec(x_44);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_36);
x_59 = lean_ctor_get(x_44, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
lean_dec(x_44);
x_26 = x_59;
x_27 = x_60;
goto block_33;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_35, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_dec(x_35);
x_26 = x_61;
x_27 = x_62;
goto block_33;
}
block_33:
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_77; lean_object* x_78; 
x_63 = lean_ctor_get(x_19, 0);
x_64 = lean_ctor_get(x_19, 1);
x_65 = lean_ctor_get(x_19, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_19);
x_66 = l_Std_PersistentArray_empty___closed__3;
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_65);
x_68 = lean_st_ref_set(x_4, x_67, x_20);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_77 = l_Lean_Meta_commitWhen___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_78 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_8, x_77, x_3, x_4, x_5, x_6, x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_80);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_3, x_4, x_5, x_6, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_79);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_89);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_96 = x_86;
} else {
 lean_dec_ref(x_86);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_79);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_79);
x_98 = lean_ctor_get(x_86, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_86, 1);
lean_inc(x_99);
lean_dec(x_86);
x_70 = x_98;
x_71 = x_99;
goto block_76;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
lean_dec(x_78);
x_70 = x_100;
x_71 = x_101;
goto block_76;
}
block_76:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_71);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
 lean_ctor_set_tag(x_75, 1);
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_isExprDefEq___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isExprDefEq___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_dec(x_8);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3;
x_7 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
if (x_3 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__9;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_4 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_8, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 2);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_58; 
x_22 = 0;
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_22);
x_23 = lean_st_ref_set(x_8, x_16, x_18);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_Meta_commitWhen___at_Lean_Meta_isExprDefEq___spec__1(x_1, x_2, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_59);
x_61 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_61, 0, x_1);
lean_closure_set(x_61, 1, x_2);
lean_closure_set(x_61, 2, x_59);
x_62 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_3, x_61, x_5, x_6, x_7, x_8, x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_st_ref_get(x_8, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_take(x_8, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_67, 2);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_14);
x_73 = lean_st_ref_set(x_8, x_67, x_69);
lean_dec(x_8);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
lean_ctor_set(x_73, 0, x_59);
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_59);
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
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_14);
lean_ctor_set(x_67, 2, x_79);
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
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_59);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_67, 0);
x_85 = lean_ctor_get(x_67, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_67);
x_86 = lean_ctor_get(x_68, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_87 = x_68;
} else {
 lean_dec_ref(x_68);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 1, 1);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_14);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_88);
x_90 = lean_st_ref_set(x_8, x_89, x_69);
lean_dec(x_8);
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
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_59);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_58, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_58, 1);
lean_inc(x_95);
lean_dec(x_58);
x_25 = x_94;
x_26 = x_95;
goto block_57;
}
block_57:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_st_ref_get(x_8, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_take(x_8, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 2);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_14);
x_36 = lean_st_ref_set(x_8, x_30, x_32);
lean_dec(x_8);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_25);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_14);
lean_ctor_set(x_30, 2, x_42);
x_43 = lean_st_ref_set(x_8, x_30, x_32);
lean_dec(x_8);
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
lean_ctor_set(x_46, 0, x_25);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
x_49 = lean_ctor_get(x_31, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_50 = x_31;
} else {
 lean_dec_ref(x_31);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 1, 1);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_14);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_51);
x_53 = lean_st_ref_set(x_8, x_52, x_32);
lean_dec(x_8);
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
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_25);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_121; 
x_96 = lean_ctor_get(x_17, 0);
lean_inc(x_96);
lean_dec(x_17);
x_97 = 0;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
lean_ctor_set(x_16, 2, x_98);
x_99 = lean_st_ref_set(x_8, x_16, x_18);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_121 = l_Lean_Meta_commitWhen___at_Lean_Meta_isExprDefEq___spec__1(x_1, x_2, x_5, x_6, x_7, x_8, x_100);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_122);
x_124 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_124, 0, x_1);
lean_closure_set(x_124, 1, x_2);
lean_closure_set(x_124, 2, x_122);
x_125 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_3, x_124, x_5, x_6, x_7, x_8, x_123);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_st_ref_get(x_8, x_126);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_st_ref_take(x_8, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 x_135 = x_130;
} else {
 lean_dec_ref(x_130);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_131, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_137 = x_131;
} else {
 lean_dec_ref(x_131);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 1, 1);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set_uint8(x_138, sizeof(void*)*1, x_14);
if (lean_is_scalar(x_135)) {
 x_139 = lean_alloc_ctor(0, 3, 0);
} else {
 x_139 = x_135;
}
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_139, 2, x_138);
x_140 = lean_st_ref_set(x_8, x_139, x_132);
lean_dec(x_8);
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
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_122);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_144 = lean_ctor_get(x_121, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_121, 1);
lean_inc(x_145);
lean_dec(x_121);
x_101 = x_144;
x_102 = x_145;
goto block_120;
}
block_120:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_103 = lean_st_ref_get(x_8, x_102);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_st_ref_take(x_8, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 x_111 = x_106;
} else {
 lean_dec_ref(x_106);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_113 = x_107;
} else {
 lean_dec_ref(x_107);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 1, 1);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_14);
if (lean_is_scalar(x_111)) {
 x_115 = lean_alloc_ctor(0, 3, 0);
} else {
 x_115 = x_111;
}
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_110);
lean_ctor_set(x_115, 2, x_114);
x_116 = lean_st_ref_set(x_8, x_115, x_108);
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
lean_ctor_set(x_119, 0, x_101);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_175; 
x_146 = lean_ctor_get(x_16, 0);
x_147 = lean_ctor_get(x_16, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_16);
x_148 = lean_ctor_get(x_17, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_149 = x_17;
} else {
 lean_dec_ref(x_17);
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
x_152 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_152, 0, x_146);
lean_ctor_set(x_152, 1, x_147);
lean_ctor_set(x_152, 2, x_151);
x_153 = lean_st_ref_set(x_8, x_152, x_18);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_175 = l_Lean_Meta_commitWhen___at_Lean_Meta_isExprDefEq___spec__1(x_1, x_2, x_5, x_6, x_7, x_8, x_154);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
lean_inc(x_176);
x_178 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_178, 0, x_1);
lean_closure_set(x_178, 1, x_2);
lean_closure_set(x_178, 2, x_176);
x_179 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_3, x_178, x_5, x_6, x_7, x_8, x_177);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_st_ref_get(x_8, x_180);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_st_ref_take(x_8, x_182);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_184, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_187 = lean_ctor_get(x_184, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 x_189 = x_184;
} else {
 lean_dec_ref(x_184);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_185, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_191 = x_185;
} else {
 lean_dec_ref(x_185);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(0, 1, 1);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set_uint8(x_192, sizeof(void*)*1, x_14);
if (lean_is_scalar(x_189)) {
 x_193 = lean_alloc_ctor(0, 3, 0);
} else {
 x_193 = x_189;
}
lean_ctor_set(x_193, 0, x_187);
lean_ctor_set(x_193, 1, x_188);
lean_ctor_set(x_193, 2, x_192);
x_194 = lean_st_ref_set(x_8, x_193, x_186);
lean_dec(x_8);
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
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_176);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_ctor_get(x_175, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_175, 1);
lean_inc(x_199);
lean_dec(x_175);
x_155 = x_198;
x_156 = x_199;
goto block_174;
}
block_174:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_157 = lean_st_ref_get(x_8, x_156);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_st_ref_take(x_8, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 x_165 = x_160;
} else {
 lean_dec_ref(x_160);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_161, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_167 = x_161;
} else {
 lean_dec_ref(x_161);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 1, 1);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_14);
if (lean_is_scalar(x_165)) {
 x_169 = lean_alloc_ctor(0, 3, 0);
} else {
 x_169 = x_165;
}
lean_ctor_set(x_169, 0, x_163);
lean_ctor_set(x_169, 1, x_164);
lean_ctor_set(x_169, 2, x_168);
x_170 = lean_st_ref_set(x_8, x_169, x_162);
lean_dec(x_8);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
 lean_ctor_set_tag(x_173, 1);
}
lean_ctor_set(x_173, 0, x_155);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___rarg(x_8, x_9);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_203 = l_Lean_Meta_commitWhen___at_Lean_Meta_isExprDefEq___spec__3(x_1, x_2, x_5, x_6, x_7, x_8, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
lean_inc(x_204);
x_206 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_206, 0, x_1);
lean_closure_set(x_206, 1, x_2);
lean_closure_set(x_206, 2, x_204);
lean_inc(x_3);
x_207 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_3, x_206, x_5, x_6, x_7, x_8, x_205);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_201, x_3, x_5, x_6, x_7, x_8, x_208);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_209, 0);
lean_dec(x_211);
lean_ctor_set(x_209, 0, x_204);
return x_209;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_204);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
lean_dec(x_2);
lean_dec(x_1);
x_214 = lean_ctor_get(x_203, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_203, 1);
lean_inc(x_215);
lean_dec(x_203);
x_216 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_201, x_3, x_5, x_6, x_7, x_8, x_215);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_216, 0);
lean_dec(x_218);
lean_ctor_set_tag(x_216, 1);
lean_ctor_set(x_216, 0, x_214);
return x_216;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_214);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
}
}
lean_object* _init_l_Lean_Meta_isExprDefEq___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isDefEq");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_isExprDefEq___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_isExprDefEq___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_isExprDefEq___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg___lambda__2___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_isExprDefEq___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___closed__2;
x_2 = l_Lean_Meta_isExprDefEq___rarg___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_isExprDefEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__2___boxed), 9, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
x_6 = l_Lean_Meta_isExprDefEq___rarg___closed__4;
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_isExprDefEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Meta_isExprDefEq___rarg___lambda__1(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_isExprDefEq___rarg___lambda__2(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_isDefEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isExprDefEq___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_isDefEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isDefEqNoConstantApprox___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_st_ref_take(x_4, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_19, 2);
lean_dec(x_22);
x_23 = l_Std_PersistentArray_empty___closed__3;
lean_ctor_set(x_19, 2, x_23);
x_24 = lean_st_ref_set(x_4, x_19, x_20);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_34 = l_Lean_Meta_commitWhen___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_8, x_34, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_36);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_44);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_44, 0);
lean_dec(x_56);
lean_ctor_set(x_44, 0, x_36);
return x_44;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_dec(x_44);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_36);
x_59 = lean_ctor_get(x_44, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
lean_dec(x_44);
x_26 = x_59;
x_27 = x_60;
goto block_33;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_35, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_dec(x_35);
x_26 = x_61;
x_27 = x_62;
goto block_33;
}
block_33:
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_77; lean_object* x_78; 
x_63 = lean_ctor_get(x_19, 0);
x_64 = lean_ctor_get(x_19, 1);
x_65 = lean_ctor_get(x_19, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_19);
x_66 = l_Std_PersistentArray_empty___closed__3;
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_65);
x_68 = lean_st_ref_set(x_4, x_67, x_20);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_77 = l_Lean_Meta_commitWhen___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_78 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_8, x_77, x_3, x_4, x_5, x_6, x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_80);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_3, x_4, x_5, x_6, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_79);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_89);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_96 = x_86;
} else {
 lean_dec_ref(x_86);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_79);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_79);
x_98 = lean_ctor_get(x_86, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_86, 1);
lean_inc(x_99);
lean_dec(x_86);
x_70 = x_98;
x_71 = x_99;
goto block_76;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
lean_dec(x_78);
x_70 = x_100;
x_71 = x_101;
goto block_76;
}
block_76:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_71);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
 lean_ctor_set_tag(x_75, 1);
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_isDefEqNoConstantApprox___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isDefEqNoConstantApprox___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_dec(x_8);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isDefEqNoConstantApprox___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_st_ref_take(x_4, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_19, 2);
lean_dec(x_22);
x_23 = l_Std_PersistentArray_empty___closed__3;
lean_ctor_set(x_19, 2, x_23);
x_24 = lean_st_ref_set(x_4, x_19, x_20);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_34 = l_Lean_Meta_commitWhen___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_8, x_34, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_36);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_44);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_44, 0);
lean_dec(x_56);
lean_ctor_set(x_44, 0, x_36);
return x_44;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_dec(x_44);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_36);
x_59 = lean_ctor_get(x_44, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
lean_dec(x_44);
x_26 = x_59;
x_27 = x_60;
goto block_33;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_35, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_dec(x_35);
x_26 = x_61;
x_27 = x_62;
goto block_33;
}
block_33:
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_77; lean_object* x_78; 
x_63 = lean_ctor_get(x_19, 0);
x_64 = lean_ctor_get(x_19, 1);
x_65 = lean_ctor_get(x_19, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_19);
x_66 = l_Std_PersistentArray_empty___closed__3;
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_65);
x_68 = lean_st_ref_set(x_4, x_67, x_20);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_77 = l_Lean_Meta_commitWhen___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_78 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_8, x_77, x_3, x_4, x_5, x_6, x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_80);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = l___private_Lean_Meta_LevelDefEq_13__processPostponed(x_3, x_4, x_5, x_6, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_79);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_89);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_96 = x_86;
} else {
 lean_dec_ref(x_86);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_79);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_79);
x_98 = lean_ctor_get(x_86, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_86, 1);
lean_inc(x_99);
lean_dec(x_86);
x_70 = x_98;
x_71 = x_99;
goto block_76;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
lean_dec(x_78);
x_70 = x_100;
x_71 = x_101;
goto block_76;
}
block_76:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = l_Lean_Meta_restore(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_71);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
 lean_ctor_set_tag(x_75, 1);
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_isDefEqNoConstantApprox___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Meta_isDefEqNoConstantApprox___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_dec(x_8);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_227 = lean_st_ref_get(x_6, x_7);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_228, 2);
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_ctor_get_uint8(x_229, sizeof(void*)*1);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; uint8_t x_232; 
x_231 = lean_ctor_get(x_227, 1);
lean_inc(x_231);
lean_dec(x_227);
x_232 = 0;
x_8 = x_232;
x_9 = x_231;
goto block_226;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_233 = lean_ctor_get(x_227, 1);
lean_inc(x_233);
lean_dec(x_227);
x_234 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_235 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_234, x_3, x_4, x_5, x_6, x_233);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = lean_unbox(x_236);
lean_dec(x_236);
x_8 = x_238;
x_9 = x_237;
goto block_226;
}
block_226:
{
if (x_8 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_6, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 2);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_58; 
x_22 = 0;
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_22);
x_23 = lean_st_ref_set(x_6, x_16, x_18);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_Meta_commitWhen___at_Lean_Meta_isDefEqNoConstantApprox___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_24);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_59);
x_61 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_61, 0, x_1);
lean_closure_set(x_61, 1, x_2);
lean_closure_set(x_61, 2, x_59);
x_62 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_63 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_62, x_61, x_3, x_4, x_5, x_6, x_60);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_get(x_6, x_64);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_take(x_6, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_68, 2);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_14);
x_74 = lean_st_ref_set(x_6, x_68, x_70);
lean_dec(x_6);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set(x_74, 0, x_59);
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_59);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_69, 0);
lean_inc(x_79);
lean_dec(x_69);
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_14);
lean_ctor_set(x_68, 2, x_80);
x_81 = lean_st_ref_set(x_6, x_68, x_70);
lean_dec(x_6);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_59);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_85 = lean_ctor_get(x_68, 0);
x_86 = lean_ctor_get(x_68, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_68);
x_87 = lean_ctor_get(x_69, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_88 = x_69;
} else {
 lean_dec_ref(x_69);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 1, 1);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_14);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_86);
lean_ctor_set(x_90, 2, x_89);
x_91 = lean_st_ref_set(x_6, x_90, x_70);
lean_dec(x_6);
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
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_59);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_58, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_58, 1);
lean_inc(x_96);
lean_dec(x_58);
x_25 = x_95;
x_26 = x_96;
goto block_57;
}
block_57:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_st_ref_get(x_6, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_take(x_6, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 2);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_14);
x_36 = lean_st_ref_set(x_6, x_30, x_32);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_25);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_14);
lean_ctor_set(x_30, 2, x_42);
x_43 = lean_st_ref_set(x_6, x_30, x_32);
lean_dec(x_6);
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
lean_ctor_set(x_46, 0, x_25);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
x_49 = lean_ctor_get(x_31, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_50 = x_31;
} else {
 lean_dec_ref(x_31);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 1, 1);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_14);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_51);
x_53 = lean_st_ref_set(x_6, x_52, x_32);
lean_dec(x_6);
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
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_25);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_122; 
x_97 = lean_ctor_get(x_17, 0);
lean_inc(x_97);
lean_dec(x_17);
x_98 = 0;
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
lean_ctor_set(x_16, 2, x_99);
x_100 = lean_st_ref_set(x_6, x_16, x_18);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_122 = l_Lean_Meta_commitWhen___at_Lean_Meta_isDefEqNoConstantApprox___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_101);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_123);
x_125 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_125, 0, x_1);
lean_closure_set(x_125, 1, x_2);
lean_closure_set(x_125, 2, x_123);
x_126 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_127 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_126, x_125, x_3, x_4, x_5, x_6, x_124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_st_ref_get(x_6, x_128);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_st_ref_take(x_6, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 x_137 = x_132;
} else {
 lean_dec_ref(x_132);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_133, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_139 = x_133;
} else {
 lean_dec_ref(x_133);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 1, 1);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_14);
if (lean_is_scalar(x_137)) {
 x_141 = lean_alloc_ctor(0, 3, 0);
} else {
 x_141 = x_137;
}
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_136);
lean_ctor_set(x_141, 2, x_140);
x_142 = lean_st_ref_set(x_6, x_141, x_134);
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
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_123);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = lean_ctor_get(x_122, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_122, 1);
lean_inc(x_147);
lean_dec(x_122);
x_102 = x_146;
x_103 = x_147;
goto block_121;
}
block_121:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_104 = lean_st_ref_get(x_6, x_103);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_st_ref_take(x_6, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 x_112 = x_107;
} else {
 lean_dec_ref(x_107);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_114 = x_108;
} else {
 lean_dec_ref(x_108);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 1, 1);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_14);
if (lean_is_scalar(x_112)) {
 x_116 = lean_alloc_ctor(0, 3, 0);
} else {
 x_116 = x_112;
}
lean_ctor_set(x_116, 0, x_110);
lean_ctor_set(x_116, 1, x_111);
lean_ctor_set(x_116, 2, x_115);
x_117 = lean_st_ref_set(x_6, x_116, x_109);
lean_dec(x_6);
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
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
 lean_ctor_set_tag(x_120, 1);
}
lean_ctor_set(x_120, 0, x_102);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_177; 
x_148 = lean_ctor_get(x_16, 0);
x_149 = lean_ctor_get(x_16, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_16);
x_150 = lean_ctor_get(x_17, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_151 = x_17;
} else {
 lean_dec_ref(x_17);
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
x_154 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_149);
lean_ctor_set(x_154, 2, x_153);
x_155 = lean_st_ref_set(x_6, x_154, x_18);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_177 = l_Lean_Meta_commitWhen___at_Lean_Meta_isDefEqNoConstantApprox___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_156);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
lean_inc(x_178);
x_180 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_180, 0, x_1);
lean_closure_set(x_180, 1, x_2);
lean_closure_set(x_180, 2, x_178);
x_181 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_182 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_181, x_180, x_3, x_4, x_5, x_6, x_179);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_st_ref_get(x_6, x_183);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_st_ref_take(x_6, x_185);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_187, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 x_192 = x_187;
} else {
 lean_dec_ref(x_187);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_188, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_194 = x_188;
} else {
 lean_dec_ref(x_188);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(0, 1, 1);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*1, x_14);
if (lean_is_scalar(x_192)) {
 x_196 = lean_alloc_ctor(0, 3, 0);
} else {
 x_196 = x_192;
}
lean_ctor_set(x_196, 0, x_190);
lean_ctor_set(x_196, 1, x_191);
lean_ctor_set(x_196, 2, x_195);
x_197 = lean_st_ref_set(x_6, x_196, x_189);
lean_dec(x_6);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_178);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_201 = lean_ctor_get(x_177, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_177, 1);
lean_inc(x_202);
lean_dec(x_177);
x_157 = x_201;
x_158 = x_202;
goto block_176;
}
block_176:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_159 = lean_st_ref_get(x_6, x_158);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_161 = lean_st_ref_take(x_6, x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_162, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_162, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 x_167 = x_162;
} else {
 lean_dec_ref(x_162);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_163, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_169 = x_163;
} else {
 lean_dec_ref(x_163);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(0, 1, 1);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set_uint8(x_170, sizeof(void*)*1, x_14);
if (lean_is_scalar(x_167)) {
 x_171 = lean_alloc_ctor(0, 3, 0);
} else {
 x_171 = x_167;
}
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_166);
lean_ctor_set(x_171, 2, x_170);
x_172 = lean_st_ref_set(x_6, x_171, x_164);
lean_dec(x_6);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
 lean_ctor_set_tag(x_175, 1);
}
lean_ctor_set(x_175, 0, x_157);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = l___private_Lean_Util_Trace_5__getResetTraces___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__6___rarg(x_6, x_9);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_206 = l_Lean_Meta_commitWhen___at_Lean_Meta_isDefEqNoConstantApprox___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
lean_inc(x_207);
x_209 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_209, 0, x_1);
lean_closure_set(x_209, 1, x_2);
lean_closure_set(x_209, 2, x_207);
x_210 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_211 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_210, x_209, x_3, x_4, x_5, x_6, x_208);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_204, x_210, x_3, x_4, x_5, x_6, x_212);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_213, 0);
lean_dec(x_215);
lean_ctor_set(x_213, 0, x_207);
return x_213;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_213, 1);
lean_inc(x_216);
lean_dec(x_213);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_207);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_2);
lean_dec(x_1);
x_218 = lean_ctor_get(x_206, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_206, 1);
lean_inc(x_219);
lean_dec(x_206);
x_220 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_221 = l___private_Lean_Util_Trace_4__addNode___at___private_Lean_Meta_LevelDefEq_11__processPostponedStep___spec__7(x_204, x_220, x_3, x_4, x_5, x_6, x_219);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_221, 0);
lean_dec(x_223);
lean_ctor_set_tag(x_221, 1);
lean_ctor_set(x_221, 0, x_218);
return x_221;
}
else
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_218);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
}
}
lean_object* l_Lean_Meta_isDefEqNoConstantApprox___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_12 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get_uint8(x_9, 3);
x_22 = lean_ctor_get_uint8(x_9, 4);
x_23 = lean_ctor_get_uint8(x_9, 5);
x_24 = lean_ctor_get_uint8(x_9, 6);
x_25 = lean_ctor_get_uint8(x_9, 7);
lean_dec(x_9);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, 2, x_26);
lean_ctor_set_uint8(x_27, 3, x_21);
lean_ctor_set_uint8(x_27, 4, x_22);
lean_ctor_set_uint8(x_27, 5, x_23);
lean_ctor_set_uint8(x_27, 6, x_24);
lean_ctor_set_uint8(x_27, 7, x_25);
lean_ctor_set(x_3, 0, x_27);
x_28 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_3, 1);
x_39 = lean_ctor_get(x_3, 2);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_3);
x_40 = lean_ctor_get_uint8(x_37, 3);
x_41 = lean_ctor_get_uint8(x_37, 4);
x_42 = lean_ctor_get_uint8(x_37, 5);
x_43 = lean_ctor_get_uint8(x_37, 6);
x_44 = lean_ctor_get_uint8(x_37, 7);
if (lean_is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
x_46 = 1;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 0, 8);
} else {
 x_47 = x_45;
}
lean_ctor_set_uint8(x_47, 0, x_46);
lean_ctor_set_uint8(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, 2, x_46);
lean_ctor_set_uint8(x_47, 3, x_40);
lean_ctor_set_uint8(x_47, 4, x_41);
lean_ctor_set_uint8(x_47, 5, x_42);
lean_ctor_set_uint8(x_47, 6, x_43);
lean_ctor_set_uint8(x_47, 7, x_44);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_38);
lean_ctor_set(x_48, 2, x_39);
x_49 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_1, x_2, x_48, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
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
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_56 = x_49;
} else {
 lean_dec_ref(x_49);
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
lean_object* l_Lean_Meta_isDefEqNoConstantApprox___rarg___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_isDefEqNoConstantApprox___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqNoConstantApprox___rarg___lambda__2___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_isDefEqNoConstantApprox___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqNoConstantApprox___rarg___lambda__1), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Lean_Meta_isDefEqNoConstantApprox___rarg___closed__1;
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_isDefEqNoConstantApprox(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqNoConstantApprox___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isDefEqNoConstantApprox___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_Meta_isDefEqNoConstantApprox___rarg___lambda__2(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* initialize_Init(lean_object*);
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
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_decLevel___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_decLevel___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_decLevel___rarg___lambda__1___closed__1);
l_Lean_Meta_decLevel___rarg___lambda__1___closed__2 = _init_l_Lean_Meta_decLevel___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_decLevel___rarg___lambda__1___closed__2);
l_Lean_Meta_decLevel___rarg___lambda__1___closed__3 = _init_l_Lean_Meta_decLevel___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_decLevel___rarg___lambda__1___closed__3);
l_Lean_Meta_decLevel___rarg___lambda__1___closed__4 = _init_l_Lean_Meta_decLevel___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_decLevel___rarg___lambda__1___closed__4);
l_Lean_Meta_decLevel___rarg___lambda__1___closed__5 = _init_l_Lean_Meta_decLevel___rarg___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_decLevel___rarg___lambda__1___closed__5);
l_Lean_Meta_decLevel___rarg___lambda__1___closed__6 = _init_l_Lean_Meta_decLevel___rarg___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_decLevel___rarg___lambda__1___closed__6);
l_Lean_Meta_getDecLevel___rarg___closed__1 = _init_l_Lean_Meta_getDecLevel___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_getDecLevel___rarg___closed__1);
l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__1 = _init_l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__1);
l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__2 = _init_l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__2);
l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3 = _init_l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3);
l_Lean_Meta_isLevelDefEqAux___main___closed__1 = _init_l_Lean_Meta_isLevelDefEqAux___main___closed__1();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAux___main___closed__1);
l_Lean_Meta_isLevelDefEqAux___main___closed__2 = _init_l_Lean_Meta_isLevelDefEqAux___main___closed__2();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAux___main___closed__2);
l_Lean_Meta_isLevelDefEqAux___main___closed__3 = _init_l_Lean_Meta_isLevelDefEqAux___main___closed__3();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAux___main___closed__3);
l_Lean_Meta_isLevelDefEqAux___main___closed__4 = _init_l_Lean_Meta_isLevelDefEqAux___main___closed__4();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAux___main___closed__4);
l_Lean_Meta_isLevelDefEqAux___main___closed__5 = _init_l_Lean_Meta_isLevelDefEqAux___main___closed__5();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAux___main___closed__5);
l_Lean_Meta_isLevelDefEqAux___main___closed__6 = _init_l_Lean_Meta_isLevelDefEqAux___main___closed__6();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAux___main___closed__6);
l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__1);
l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2 = _init_l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__2);
l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__3 = _init_l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__3();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_11__processPostponedStep___closed__3);
l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__1);
l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__2 = _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__2);
l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__3 = _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__3);
l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__4 = _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__4);
l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__5 = _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__5);
l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__6 = _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__1___closed__6);
l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__1);
l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__2 = _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__2);
l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__3 = _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___lambda__2___closed__3);
l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_12__processPostponedAux___main___rarg___closed__1);
l_Lean_Meta_commitWhen___lambda__1___closed__1 = _init_l_Lean_Meta_commitWhen___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_commitWhen___lambda__1___closed__1);
l_Lean_Meta_commitWhen___closed__1 = _init_l_Lean_Meta_commitWhen___closed__1();
lean_mark_persistent(l_Lean_Meta_commitWhen___closed__1);
res = l___private_Lean_Meta_LevelDefEq_14__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__1 = _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__1);
l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2 = _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2);
l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__3 = _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__3);
l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4 = _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4);
l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__5 = _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__5);
l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6 = _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6);
l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__7 = _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__7);
l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__8 = _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__8);
l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__9 = _init_l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__9);
l_Lean_Meta_isLevelDefEq___rarg___closed__1 = _init_l_Lean_Meta_isLevelDefEq___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___closed__1);
l_Lean_Meta_isLevelDefEq___rarg___closed__2 = _init_l_Lean_Meta_isLevelDefEq___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___closed__2);
l_Lean_Meta_isLevelDefEq___rarg___closed__3 = _init_l_Lean_Meta_isLevelDefEq___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___closed__3);
l_Lean_Meta_isLevelDefEq___rarg___closed__4 = _init_l_Lean_Meta_isLevelDefEq___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_isLevelDefEq___rarg___closed__4);
l_Lean_Meta_isExprDefEq___rarg___closed__1 = _init_l_Lean_Meta_isExprDefEq___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_isExprDefEq___rarg___closed__1);
l_Lean_Meta_isExprDefEq___rarg___closed__2 = _init_l_Lean_Meta_isExprDefEq___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_isExprDefEq___rarg___closed__2);
l_Lean_Meta_isExprDefEq___rarg___closed__3 = _init_l_Lean_Meta_isExprDefEq___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_isExprDefEq___rarg___closed__3);
l_Lean_Meta_isExprDefEq___rarg___closed__4 = _init_l_Lean_Meta_isExprDefEq___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_isExprDefEq___rarg___closed__4);
l_Lean_Meta_isDefEqNoConstantApprox___rarg___closed__1 = _init_l_Lean_Meta_isDefEqNoConstantApprox___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_isDefEqNoConstantApprox___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Init.Lean.Meta.ExprDefEq
// Imports: Init.Lean.Meta.WHNF Init.Lean.Meta.InferType Init.Lean.Meta.FunInfo Init.Lean.Meta.LevelDefEq Init.Lean.Meta.Check Init.Lean.Meta.Offset
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
uint8_t l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__9;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__4;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Meta_CheckAssignment_findCached___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__6;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
lean_object* l_ReaderT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_checkFVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqBindingDomain___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_18__sameHeadSymbol___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_7__visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__21;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__processAssignmentFOApproxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___closed__1;
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache;
uint8_t l_Lean_LocalContext_containsFVar(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__19;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFVar(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_Meta_CheckAssignment_cache___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__8;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_MessageData_coeOfArrayExpr___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__2;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__simpAssignmentArgAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isReducible(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1;
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__simpAssignmentArgAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__12;
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3;
extern lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_check(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_cache(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_findCached(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqBindingDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isListLevelDefEq___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___closed__1;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Meta_ExprDefEq_18__sameHeadSymbol(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_16__unfold___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
extern lean_object* l_Lean_formatEntry___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticExprMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Meta_isTypeCorrectAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
extern lean_object* l_Lean_Meta_tracer___closed__3;
extern lean_object* l_Lean_Meta_tracer;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__11;
lean_object* l_Lean_Meta_CheckAssignment_findCached___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_checkMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_mkAuxMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isEtaUnassignedMVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_assign_expr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_isWellFormed___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__16;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_try(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateApp_x21___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_isEtaUnassignedMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l___private_Init_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqBindingDomain___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_ConstantInfo_hints(lean_object*);
extern lean_object* l_Id_Monad;
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_Meta_CheckAssignment_cache___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_16__unfold(lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Meta_CheckAssignment_cache___spec__6(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateProj_x21___closed__2;
lean_object* l_Lean_Meta_isDefEqBindingDomain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__7;
uint8_t l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__2(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__7___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
lean_object* l_Lean_Meta_CheckAssignment_getMCtx(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_ParamInfo_inhabited;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_usingDefault(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__isDeltaCandidate___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Meta_CheckAssignment_cache___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferTypeAuxAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_mk_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_getConstAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
lean_object* l_AssocList_find___main___at_Lean_Meta_CheckAssignment_findCached___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__20;
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_check___main(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Meta_CheckAssignment_findCached___spec__2(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLet_x21___closed__1;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_simpleMonadTracerAdapter___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__17;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_Meta_CheckAssignment_cache___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_object* l_Lean_Meta_checkAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkAssignment___closed__1;
lean_object* l_Lean_Meta_inferTypeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_mkAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3;
lean_object* l_mkHashMap___at_Lean_Meta_checkAssignment___spec__2(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_15__processAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_getMCtx___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__6;
lean_object* l___private_Init_Lean_Expr_9__etaExpandedAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__2;
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_check___main___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15;
lean_object* l___private_Init_Lean_Trace_3__addTrace___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__18;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_CheckAssignment_cache___spec__5(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__3;
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__13;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4;
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Meta_CheckAssignment_findCached___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__isDeltaCandidate(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__processAssignmentFOApproxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoAuxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_getMCtx___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__22;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__4;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_13__simpAssignmentArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ReducibilityHints_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__14;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_CheckAssignment_cache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__5;
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkBVar(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isLambda(x_3);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isLambda(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_usingDefault), 4, 1);
lean_closure_set(x_12, 0, x_1);
lean_inc(x_5);
x_13 = l_Lean_Meta_inferTypeAuxAux___main(x_12, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 2);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 1;
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 4, x_20);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
x_22 = lean_apply_3(x_1, x_15, x_21, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 7)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_23, sizeof(void*)*3);
lean_dec(x_23);
x_29 = (uint8_t)((x_28 << 24) >> 61);
x_30 = l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1;
x_31 = l_Lean_mkApp(x_27, x_30);
x_32 = l_Lean_mkLambda(x_25, x_29, x_26, x_31);
x_33 = lean_apply_2(x_2, x_3, x_32);
x_34 = l_Lean_Meta_try(x_33, x_5, x_24);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
lean_dec(x_36);
x_37 = 0;
x_38 = lean_box(x_37);
lean_ctor_set(x_22, 0, x_38);
return x_22;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
lean_dec(x_22);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_22);
if (x_43 == 0)
{
return x_22;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_22, 0);
x_45 = lean_ctor_get(x_22, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_22);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_49 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 1);
x_50 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 2);
x_51 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 3);
lean_inc(x_47);
lean_dec(x_14);
x_52 = 1;
x_53 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_48);
lean_ctor_set_uint8(x_53, sizeof(void*)*1 + 1, x_49);
lean_ctor_set_uint8(x_53, sizeof(void*)*1 + 2, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*1 + 3, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1 + 4, x_52);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_17);
lean_ctor_set(x_54, 2, x_18);
x_55 = lean_apply_3(x_1, x_15, x_54, x_16);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 7)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 2);
lean_inc(x_60);
x_61 = lean_ctor_get_uint64(x_56, sizeof(void*)*3);
lean_dec(x_56);
x_62 = (uint8_t)((x_61 << 24) >> 61);
x_63 = l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1;
x_64 = l_Lean_mkApp(x_60, x_63);
x_65 = l_Lean_mkLambda(x_58, x_62, x_59, x_64);
x_66 = lean_apply_2(x_2, x_3, x_65);
x_67 = l_Lean_Meta_try(x_66, x_5, x_57);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_56);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_ctor_get(x_55, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_69 = x_55;
} else {
 lean_dec_ref(x_55);
 x_69 = lean_box(0);
}
x_70 = 0;
x_71 = lean_box(x_70);
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
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_ctor_get(x_55, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_55, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_75 = x_55;
} else {
 lean_dec_ref(x_55);
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
else
{
uint8_t x_77; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_13);
if (x_77 == 0)
{
return x_13;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_13, 0);
x_79 = lean_ctor_get(x_13, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_13);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = 0;
x_82 = lean_box(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_6);
return x_83;
}
}
}
}
lean_object* l_Lean_Meta_isEtaUnassignedMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_Lean_Expr_9__etaExpandedAux___main(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_10);
x_11 = l_Lean_Meta_isReadOnlyOrSyntheticExprMVar(x_10, x_2, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_metavar_ctx_is_expr_assigned(x_17, x_10);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; 
lean_dec(x_12);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
return x_11;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_metavar_ctx_is_expr_assigned(x_22, x_10);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_11, 0, x_31);
return x_11;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_dec(x_11);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
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
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_9);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_3);
return x_42;
}
}
}
}
lean_object* l_Lean_Meta_isEtaUnassignedMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isEtaUnassignedMVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_41; 
x_13 = lean_array_fget(x_2, x_5);
x_14 = l_Lean_Expr_Inhabited;
x_15 = lean_array_get(x_14, x_3, x_5);
x_16 = lean_array_get(x_14, x_4, x_5);
x_41 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 1);
lean_dec(x_13);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc(x_1);
lean_inc(x_7);
x_43 = lean_apply_4(x_1, x_15, x_16, x_7, x_8);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
uint8_t x_46; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_5, x_53);
lean_dec(x_5);
x_5 = x_54;
x_8 = x_52;
goto _start;
}
}
else
{
uint8_t x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_43);
if (x_56 == 0)
{
return x_43;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_43, 0);
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_43);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; 
lean_inc(x_15);
x_60 = l_Lean_Meta_isEtaUnassignedMVar(x_15, x_7, x_8);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_61);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
lean_inc(x_16);
x_64 = l_Lean_Meta_isEtaUnassignedMVar(x_16, x_7, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_17 = x_67;
x_18 = x_66;
goto block_40;
}
else
{
uint8_t x_68; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_64);
if (x_68 == 0)
{
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_64);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_60, 1);
lean_inc(x_72);
lean_dec(x_60);
x_73 = lean_unbox(x_61);
lean_dec(x_61);
x_17 = x_73;
x_18 = x_72;
goto block_40;
}
}
else
{
uint8_t x_74; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_60);
if (x_74 == 0)
{
return x_60;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_60, 0);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_60);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_13);
lean_inc(x_15);
x_78 = l_Lean_Meta_isEtaUnassignedMVar(x_15, x_7, x_8);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
lean_inc(x_16);
x_82 = l_Lean_Meta_isEtaUnassignedMVar(x_16, x_7, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_unbox(x_83);
lean_dec(x_83);
x_17 = x_85;
x_18 = x_84;
goto block_40;
}
else
{
uint8_t x_86; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
return x_82;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_82, 0);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_82);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_78, 1);
lean_inc(x_90);
lean_dec(x_78);
x_91 = lean_unbox(x_79);
lean_dec(x_79);
x_17 = x_91;
x_18 = x_90;
goto block_40;
}
}
else
{
uint8_t x_92; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_78);
if (x_92 == 0)
{
return x_78;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_78, 0);
x_94 = lean_ctor_get(x_78, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_78);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
block_40:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_15);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
x_21 = lean_array_push(x_6, x_5);
x_5 = x_20;
x_6 = x_21;
x_8 = x_18;
goto _start;
}
else
{
lean_object* x_23; 
lean_inc(x_1);
lean_inc(x_7);
x_23 = lean_apply_4(x_1, x_15, x_16, x_7, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_5, x_33);
lean_dec(x_5);
x_5 = x_34;
x_8 = x_32;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_fget(x_2, x_5);
x_14 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_6);
x_15 = lean_apply_4(x_1, x_13, x_14, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_16);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_5, x_23);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_24;
x_7 = x_22;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main(x_1, x_2, x_3, lean_box(0), x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_9 = l_Lean_Expr_Inhabited;
x_10 = lean_array_get(x_9, x_1, x_6);
x_11 = lean_array_get(x_9, x_2, x_6);
x_100 = l_Lean_Meta_ParamInfo_inhabited;
x_101 = lean_array_get(x_100, x_4, x_6);
x_102 = lean_ctor_get_uint8(x_101, sizeof(void*)*1 + 1);
lean_dec(x_101);
if (x_102 == 0)
{
lean_dec(x_5);
x_12 = x_8;
goto block_99;
}
else
{
lean_object* x_103; 
lean_inc(x_5);
lean_inc(x_7);
lean_inc(x_10);
x_103 = lean_apply_3(x_5, x_10, x_7, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
lean_inc(x_7);
lean_inc(x_11);
x_105 = lean_apply_3(x_5, x_11, x_7, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_12 = x_106;
goto block_99;
}
else
{
uint8_t x_107; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
return x_105;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_105, 0);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_105);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_111 = !lean_is_exclusive(x_103);
if (x_111 == 0)
{
return x_103;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_103, 0);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_103);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
block_99:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 4);
x_17 = 1;
x_18 = l_Lean_Meta_TransparencyMode_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_apply_4(x_3, x_10, x_11, x_7, x_12);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
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
lean_object* x_28; 
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 4, x_17);
x_28 = lean_apply_4(x_3, x_10, x_11, x_7, x_12);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_39 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 1);
x_40 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 2);
x_41 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 3);
x_42 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 4);
lean_inc(x_37);
lean_dec(x_14);
x_43 = 1;
x_44 = l_Lean_Meta_TransparencyMode_lt(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_38);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 1, x_39);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 2, x_40);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 3, x_41);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 4, x_42);
lean_ctor_set(x_7, 0, x_45);
x_46 = lean_apply_4(x_3, x_10, x_11, x_7, x_12);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
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
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_53 = x_46;
} else {
 lean_dec_ref(x_46);
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
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_55, 0, x_37);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_38);
lean_ctor_set_uint8(x_55, sizeof(void*)*1 + 1, x_39);
lean_ctor_set_uint8(x_55, sizeof(void*)*1 + 2, x_40);
lean_ctor_set_uint8(x_55, sizeof(void*)*1 + 3, x_41);
lean_ctor_set_uint8(x_55, sizeof(void*)*1 + 4, x_43);
lean_ctor_set(x_7, 0, x_55);
x_56 = lean_apply_4(x_3, x_10, x_11, x_7, x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_63 = x_56;
} else {
 lean_dec_ref(x_56);
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
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; 
x_65 = lean_ctor_get(x_7, 0);
x_66 = lean_ctor_get(x_7, 1);
x_67 = lean_ctor_get(x_7, 2);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_7);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_65, sizeof(void*)*1);
x_70 = lean_ctor_get_uint8(x_65, sizeof(void*)*1 + 1);
x_71 = lean_ctor_get_uint8(x_65, sizeof(void*)*1 + 2);
x_72 = lean_ctor_get_uint8(x_65, sizeof(void*)*1 + 3);
x_73 = lean_ctor_get_uint8(x_65, sizeof(void*)*1 + 4);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_74 = x_65;
} else {
 lean_dec_ref(x_65);
 x_74 = lean_box(0);
}
x_75 = 1;
x_76 = l_Lean_Meta_TransparencyMode_lt(x_73, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 1, 5);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_69);
lean_ctor_set_uint8(x_77, sizeof(void*)*1 + 1, x_70);
lean_ctor_set_uint8(x_77, sizeof(void*)*1 + 2, x_71);
lean_ctor_set_uint8(x_77, sizeof(void*)*1 + 3, x_72);
lean_ctor_set_uint8(x_77, sizeof(void*)*1 + 4, x_73);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_66);
lean_ctor_set(x_78, 2, x_67);
x_79 = lean_apply_4(x_3, x_10, x_11, x_78, x_12);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
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
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_86 = x_79;
} else {
 lean_dec_ref(x_79);
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
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
if (lean_is_scalar(x_74)) {
 x_88 = lean_alloc_ctor(0, 1, 5);
} else {
 x_88 = x_74;
}
lean_ctor_set(x_88, 0, x_68);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_69);
lean_ctor_set_uint8(x_88, sizeof(void*)*1 + 1, x_70);
lean_ctor_set_uint8(x_88, sizeof(void*)*1 + 2, x_71);
lean_ctor_set_uint8(x_88, sizeof(void*)*1 + 3, x_72);
lean_ctor_set_uint8(x_88, sizeof(void*)*1 + 4, x_75);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_66);
lean_ctor_set(x_89, 2, x_67);
x_90 = lean_apply_4(x_3, x_10, x_11, x_89, x_12);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
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
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_array_get_size(x_6);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_9);
lean_inc(x_7);
x_16 = l_Lean_Meta_getFunInfoAuxAux(x_1, x_4, x_15, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_19);
lean_inc(x_7);
lean_inc(x_2);
x_21 = l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main(x_2, x_5, x_6, lean_box(0), x_20, x_7, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_empty___closed__1;
lean_inc(x_7);
lean_inc(x_2);
x_25 = l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main(x_2, x_19, x_5, x_6, x_23, x_24, x_7, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = 0;
x_30 = lean_box(x_29);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___lambda__1___boxed), 8, 5);
lean_closure_set(x_37, 0, x_5);
lean_closure_set(x_37, 1, x_6);
lean_closure_set(x_37, 2, x_2);
lean_closure_set(x_37, 3, x_19);
lean_closure_set(x_37, 4, x_3);
x_38 = lean_array_get_size(x_36);
x_39 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_40 = l_Array_anyRangeMAux___main___rarg(x_39, x_36, x_38, lean_box(0), x_37, x_23);
x_41 = lean_apply_2(x_40, x_7, x_35);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
x_46 = 1;
x_47 = lean_box(x_46);
lean_ctor_set(x_41, 0, x_47);
return x_41;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = 1;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_41, 0);
lean_dec(x_53);
x_54 = 0;
x_55 = lean_box(x_54);
lean_ctor_set(x_41, 0, x_55);
return x_41;
}
else
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_dec(x_41);
x_57 = 0;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_41);
if (x_60 == 0)
{
return x_41;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_41, 0);
x_62 = lean_ctor_get(x_41, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_41);
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
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_25);
if (x_64 == 0)
{
return x_25;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_25, 0);
x_66 = lean_ctor_get(x_25, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_25);
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
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_21);
if (x_68 == 0)
{
return x_21;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_21, 0);
x_70 = lean_ctor_get(x_21, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_21);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_16);
if (x_72 == 0)
{
return x_16;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_16, 0);
x_74 = lean_ctor_get(x_16, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_16);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_isDefEqBindingDomain___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_apply_2(x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_3, x_5);
lean_inc(x_7);
x_13 = l_Lean_Meta_getFVarLocalDecl(x_12, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_LocalDecl_type(x_14);
lean_dec(x_14);
x_17 = l_Lean_Expr_Inhabited;
x_18 = lean_array_get(x_17, x_4, x_5);
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_16);
x_19 = lean_apply_4(x_2, x_16, x_18, x_7, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_1);
x_27 = l_Lean_Meta_isClass(x_1, x_16, x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_5, x_30);
lean_dec(x_5);
x_5 = x_31;
x_8 = x_29;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_5, x_35);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_7, 2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_12);
x_40 = lean_array_push(x_38, x_39);
lean_ctor_set(x_7, 2, x_40);
x_5 = x_36;
x_8 = x_33;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
x_44 = lean_ctor_get(x_7, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_7);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_12);
x_46 = lean_array_push(x_44, x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_46);
x_5 = x_36;
x_7 = x_47;
x_8 = x_33;
goto _start;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_27);
if (x_49 == 0)
{
return x_27;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_27, 0);
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_27);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_19);
if (x_53 == 0)
{
return x_19;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_19, 0);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_19);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_13);
if (x_57 == 0)
{
return x_13;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_13, 0);
x_59 = lean_ctor_get(x_13, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_13);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
lean_object* l_Lean_Meta_isDefEqBindingDomain___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isDefEqBindingDomain___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_isDefEqBindingDomain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isDefEqBindingDomain___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_isDefEqBindingDomain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isDefEqBindingDomain(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
switch (lean_obj_tag(x_5)) {
case 6:
{
if (lean_obj_tag(x_6) == 6)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 2);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_6, 2);
x_29 = lean_expr_instantiate_rev(x_25, x_4);
lean_dec(x_25);
x_30 = lean_expr_instantiate_rev(x_27, x_4);
x_31 = l_Lean_Meta_mkFreshId___rarg(x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 0;
lean_inc(x_32);
x_35 = lean_local_ctx_mk_local_decl(x_3, x_32, x_24, x_29, x_34);
x_36 = l_Lean_mkFVar(x_32);
x_37 = lean_array_push(x_4, x_36);
x_38 = lean_array_push(x_7, x_30);
x_3 = x_35;
x_4 = x_37;
x_5 = x_26;
x_6 = x_28;
x_7 = x_38;
x_9 = x_33;
goto _start;
}
else
{
lean_object* x_40; 
x_40 = lean_box(0);
x_10 = x_40;
goto block_23;
}
}
case 7:
{
if (lean_obj_tag(x_6) == 7)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get(x_5, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_5, 2);
lean_inc(x_43);
lean_dec(x_5);
x_44 = lean_ctor_get(x_6, 1);
x_45 = lean_ctor_get(x_6, 2);
x_46 = lean_expr_instantiate_rev(x_42, x_4);
lean_dec(x_42);
x_47 = lean_expr_instantiate_rev(x_44, x_4);
x_48 = l_Lean_Meta_mkFreshId___rarg(x_9);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = 0;
lean_inc(x_49);
x_52 = lean_local_ctx_mk_local_decl(x_3, x_49, x_41, x_46, x_51);
x_53 = l_Lean_mkFVar(x_49);
x_54 = lean_array_push(x_4, x_53);
x_55 = lean_array_push(x_7, x_47);
x_3 = x_52;
x_4 = x_54;
x_5 = x_43;
x_6 = x_45;
x_7 = x_55;
x_9 = x_50;
goto _start;
}
else
{
lean_object* x_57; 
x_57 = lean_box(0);
x_10 = x_57;
goto block_23;
}
}
default: 
{
lean_object* x_58; 
x_58 = lean_box(0);
x_10 = x_58;
goto block_23;
}
}
block_23:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_10);
x_11 = lean_expr_instantiate_rev(x_5, x_4);
lean_dec(x_5);
x_12 = lean_expr_instantiate_rev(x_6, x_4);
lean_inc(x_2);
x_13 = lean_apply_2(x_2, x_11, x_12);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 1);
lean_dec(x_15);
lean_ctor_set(x_8, 1, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Meta_isDefEqBindingDomain___main(x_1, x_2, x_4, x_7, x_16, x_13, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Meta_isDefEqBindingDomain___main(x_1, x_2, x_4, x_7, x_21, x_13, x_20, x_9);
lean_dec(x_7);
lean_dec(x_4);
return x_22;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l_Array_empty___closed__1;
x_9 = l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(x_1, x_2, x_7, x_8, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_AssocList_find___main___at_Lean_Meta_CheckAssignment_findCached___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_expr_equal(x_4, x_1);
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
lean_object* l_HashMapImp_find___at_Lean_Meta_CheckAssignment_findCached___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Meta_CheckAssignment_findCached___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_CheckAssignment_findCached(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = l_HashMapImp_find___at_Lean_Meta_CheckAssignment_findCached___spec__1(x_4, x_1);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_AssocList_find___main___at_Lean_Meta_CheckAssignment_findCached___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Meta_CheckAssignment_findCached___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_Meta_CheckAssignment_findCached___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Meta_CheckAssignment_findCached___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_CheckAssignment_findCached___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_CheckAssignment_findCached(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Meta_CheckAssignment_cache___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_expr_equal(x_4, x_1);
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
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_CheckAssignment_cache___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_CheckAssignment_cache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_Meta_CheckAssignment_cache___spec__5(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_Meta_CheckAssignment_cache___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Meta_CheckAssignment_cache___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Meta_CheckAssignment_cache___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_expr_equal(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_Meta_CheckAssignment_cache___spec__6(x_1, x_2, x_7);
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
x_13 = lean_expr_equal(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_Meta_CheckAssignment_cache___spec__6(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_Meta_CheckAssignment_cache___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_AssocList_contains___main___at_Lean_Meta_CheckAssignment_cache___spec__2(x_2, x_10);
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
x_17 = l_HashMapImp_expand___at_Lean_Meta_CheckAssignment_cache___spec__3(x_13, x_15);
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
x_18 = l_AssocList_replace___main___at_Lean_Meta_CheckAssignment_cache___spec__6(x_2, x_3, x_10);
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
x_26 = l_AssocList_contains___main___at_Lean_Meta_CheckAssignment_cache___spec__2(x_2, x_25);
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
x_32 = l_HashMapImp_expand___at_Lean_Meta_CheckAssignment_cache___spec__3(x_28, x_30);
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
x_34 = l_AssocList_replace___main___at_Lean_Meta_CheckAssignment_cache___spec__6(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Meta_CheckAssignment_cache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 2);
x_7 = l_HashMapImp_insert___at_Lean_Meta_CheckAssignment_cache___spec__1(x_6, x_1, x_2);
lean_ctor_set(x_4, 2, x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_13 = l_HashMapImp_insert___at_Lean_Meta_CheckAssignment_cache___spec__1(x_12, x_1, x_2);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_Meta_CheckAssignment_cache___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Meta_CheckAssignment_cache___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_CheckAssignment_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_CheckAssignment_cache(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_CheckAssignment_findCached___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_CheckAssignment_cache___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1;
x_2 = l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3;
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_7__visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_28; 
x_28 = l_Lean_Expr_hasExprMVar(x_2);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Expr_hasFVar(x_2);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_box(0);
x_5 = x_31;
goto block_27;
}
}
else
{
lean_object* x_32; 
x_32 = lean_box(0);
x_5 = x_32;
goto block_27;
}
block_27:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = l_Lean_Meta_CheckAssignment_findCached(x_2, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_9 = lean_apply_3(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Meta_CheckAssignment_cache(x_2, x_10, x_3, x_11);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_6, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_expr_eqv(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_CheckAssignment_checkFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_LocalContext_containsFVar(x_6, x_2);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_LocalContext_findFVar(x_8, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(x_10, x_2);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_fvarId_x21(x_2);
lean_dec(x_2);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_3, 3);
lean_inc(x_17);
lean_dec(x_3);
x_18 = l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(x_17, x_2);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_Expr_fvarId_x21(x_2);
lean_dec(x_2);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_4);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_47; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_16, 4);
lean_inc(x_23);
lean_dec(x_16);
x_47 = l_Lean_Expr_hasExprMVar(x_23);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Expr_hasFVar(x_23);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_23);
lean_ctor_set(x_49, 1, x_4);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_box(0);
x_24 = x_50;
goto block_46;
}
}
else
{
lean_object* x_51; 
x_51 = lean_box(0);
x_24 = x_51;
goto block_46;
}
block_46:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_24);
x_25 = l_Lean_Meta_CheckAssignment_findCached(x_23, x_3, x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_3);
lean_inc(x_23);
x_28 = lean_apply_3(x_1, x_23, x_3, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_29);
x_31 = l_Lean_Meta_CheckAssignment_cache(x_23, x_29, x_3, x_30);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_23);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
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
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_25, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_26, 0);
lean_inc(x_42);
lean_dec(x_26);
lean_ctor_set(x_25, 0, x_42);
return x_25;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_dec(x_25);
x_44 = lean_ctor_get(x_26, 0);
lean_inc(x_44);
lean_dec(x_26);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_4);
return x_52;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_CheckAssignment_getMCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_CheckAssignment_getMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_CheckAssignment_getMCtx___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_CheckAssignment_getMCtx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_CheckAssignment_getMCtx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_CheckAssignment_mkAuxMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_9);
x_11 = lean_name_mk_numeral(x_9, x_10);
x_12 = lean_box(0);
x_13 = 0;
lean_inc(x_11);
x_14 = lean_metavar_ctx_mk_decl(x_8, x_11, x_12, x_1, x_2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_10, x_15);
lean_dec(x_10);
lean_ctor_set(x_6, 1, x_16);
lean_ctor_set(x_4, 0, x_14);
x_17 = l_Lean_mkMVar(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
lean_inc(x_21);
lean_inc(x_20);
x_22 = lean_name_mk_numeral(x_20, x_21);
x_23 = lean_box(0);
x_24 = 0;
lean_inc(x_22);
x_25 = lean_metavar_ctx_mk_decl(x_19, x_22, x_23, x_1, x_2, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_21, x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_4, 1, x_28);
lean_ctor_set(x_4, 0, x_25);
x_29 = l_Lean_mkMVar(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_31 = lean_ctor_get(x_4, 1);
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 2);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_32);
lean_dec(x_4);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_36 = x_31;
} else {
 lean_dec_ref(x_31);
 x_36 = lean_box(0);
}
lean_inc(x_35);
lean_inc(x_34);
x_37 = lean_name_mk_numeral(x_34, x_35);
x_38 = lean_box(0);
x_39 = 0;
lean_inc(x_37);
x_40 = lean_metavar_ctx_mk_decl(x_32, x_37, x_38, x_1, x_2, x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_35, x_41);
lean_dec(x_35);
if (lean_is_scalar(x_36)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_36;
}
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_33);
x_45 = l_Lean_mkMVar(x_37);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
lean_object* l_Lean_Meta_CheckAssignment_mkAuxMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_CheckAssignment_mkAuxMVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_CheckAssignment_checkMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Expr_mvarId_x21(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_6);
x_7 = lean_metavar_ctx_get_expr_assignment(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_name_eq(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_5);
lean_inc(x_6);
x_10 = lean_metavar_ctx_find_decl(x_6, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_17);
lean_inc(x_15);
x_18 = l_Lean_LocalContext_isSubPrefixOf(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_14, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_5);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_14, sizeof(void*)*4);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
else
{
uint8_t x_27; 
lean_inc(x_17);
x_27 = l_Lean_LocalContext_isSubPrefixOf(x_17, x_15);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_2);
x_29 = lean_ctor_get(x_14, 2);
lean_inc(x_29);
lean_dec(x_14);
lean_inc(x_29);
lean_inc(x_17);
x_30 = l_Lean_MetavarContext_isWellFormed___main(x_6, x_17, x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_3);
x_32 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_32, 0, x_5);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Meta_CheckAssignment_mkAuxMVar(x_17, x_29, x_3, x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_40 = lean_metavar_ctx_assign_expr(x_39, x_5, x_38);
lean_ctor_set(x_36, 0, x_40);
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
x_44 = lean_ctor_get(x_36, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
lean_inc(x_41);
x_45 = lean_metavar_ctx_assign_expr(x_42, x_5, x_41);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_44);
lean_ctor_set(x_34, 1, x_46);
return x_34;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_34, 1);
x_48 = lean_ctor_get(x_34, 0);
lean_inc(x_47);
lean_inc(x_48);
lean_dec(x_34);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 2);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
lean_inc(x_48);
x_53 = lean_metavar_ctx_assign_expr(x_49, x_5, x_48);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 3, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_5);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_4);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_4);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(1);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_4);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_4);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_87; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_63 = lean_ctor_get(x_7, 0);
lean_inc(x_63);
lean_dec(x_7);
x_87 = l_Lean_Expr_hasExprMVar(x_63);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Expr_hasFVar(x_63);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_3);
lean_dec(x_1);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_63);
lean_ctor_set(x_89, 1, x_4);
return x_89;
}
else
{
lean_object* x_90; 
x_90 = lean_box(0);
x_64 = x_90;
goto block_86;
}
}
else
{
lean_object* x_91; 
x_91 = lean_box(0);
x_64 = x_91;
goto block_86;
}
block_86:
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_64);
x_65 = l_Lean_Meta_CheckAssignment_findCached(x_63, x_3, x_4);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_3);
lean_inc(x_63);
x_68 = lean_apply_3(x_1, x_63, x_3, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_69);
x_71 = l_Lean_Meta_CheckAssignment_cache(x_63, x_69, x_3, x_70);
lean_dec(x_3);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_63);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_68);
if (x_76 == 0)
{
return x_68;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_68, 0);
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_68);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_63);
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_65);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_65, 0);
lean_dec(x_81);
x_82 = lean_ctor_get(x_66, 0);
lean_inc(x_82);
lean_dec(x_66);
lean_ctor_set(x_65, 0, x_82);
return x_65;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_65, 1);
lean_inc(x_83);
lean_dec(x_65);
x_84 = lean_ctor_get(x_66, 0);
lean_inc(x_84);
lean_dec(x_66);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
}
}
lean_object* _init_l_Lean_Meta_CheckAssignment_check___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_2 = l_Lean_Expr_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_CheckAssignment_check___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_12; lean_object* x_13; lean_object* x_21; lean_object* x_22; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_30; uint8_t x_116; 
x_116 = l_Lean_Expr_hasExprMVar(x_1);
if (x_116 == 0)
{
uint8_t x_117; 
x_117 = l_Lean_Expr_hasFVar(x_1);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_2);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set(x_118, 1, x_3);
return x_118;
}
else
{
lean_object* x_119; 
x_119 = lean_box(0);
x_30 = x_119;
goto block_115;
}
}
else
{
lean_object* x_120; 
x_120 = lean_box(0);
x_30 = x_120;
goto block_115;
}
block_115:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_30);
x_31 = l_Lean_Meta_CheckAssignment_findCached(x_1, x_2, x_3);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_2, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_LocalContext_containsFVar(x_37, x_1);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
x_40 = l_Lean_LocalContext_findFVar(x_39, x_1);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_2, 3);
lean_inc(x_41);
x_42 = l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(x_41, x_1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
x_43 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_44);
return x_31;
}
else
{
lean_free_object(x_31);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_34;
goto block_11;
}
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec(x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_45);
x_46 = lean_ctor_get(x_2, 3);
lean_inc(x_46);
x_47 = l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(x_46, x_1);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_48 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_49);
return x_31;
}
else
{
lean_free_object(x_31);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_34;
goto block_11;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_67; 
lean_free_object(x_31);
x_50 = lean_ctor_get(x_45, 4);
lean_inc(x_50);
lean_dec(x_45);
x_67 = l_Lean_Expr_hasExprMVar(x_50);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = l_Lean_Expr_hasFVar(x_50);
if (x_68 == 0)
{
x_4 = x_50;
x_5 = x_34;
goto block_11;
}
else
{
lean_object* x_69; 
x_69 = lean_box(0);
x_51 = x_69;
goto block_66;
}
}
else
{
lean_object* x_70; 
x_70 = lean_box(0);
x_51 = x_70;
goto block_66;
}
block_66:
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_51);
x_52 = l_Lean_Meta_CheckAssignment_findCached(x_50, x_2, x_34);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_2);
lean_inc(x_50);
x_55 = l_Lean_Meta_CheckAssignment_check___main(x_50, x_2, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_56);
x_58 = l_Lean_Meta_CheckAssignment_cache(x_50, x_56, x_2, x_57);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_4 = x_56;
x_5 = x_59;
goto block_11;
}
else
{
uint8_t x_60; 
lean_dec(x_50);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_64; lean_object* x_65; 
lean_dec(x_50);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_dec(x_52);
x_65 = lean_ctor_get(x_53, 0);
lean_inc(x_65);
lean_dec(x_53);
x_4 = x_65;
x_5 = x_64;
goto block_11;
}
}
}
}
}
else
{
lean_free_object(x_31);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_34;
goto block_11;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_31, 1);
lean_inc(x_71);
lean_dec(x_31);
x_72 = lean_ctor_get(x_2, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_LocalContext_containsFVar(x_73, x_1);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_2, 0);
lean_inc(x_75);
x_76 = l_Lean_LocalContext_findFVar(x_75, x_1);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_2, 3);
lean_inc(x_77);
x_78 = l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(x_77, x_1);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_2);
x_79 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_71);
return x_81;
}
else
{
lean_inc(x_1);
x_4 = x_1;
x_5 = x_71;
goto block_11;
}
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_inc(x_82);
lean_dec(x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_82);
x_83 = lean_ctor_get(x_2, 3);
lean_inc(x_83);
x_84 = l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(x_83, x_1);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_2);
x_85 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
x_86 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_71);
return x_87;
}
else
{
lean_inc(x_1);
x_4 = x_1;
x_5 = x_71;
goto block_11;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_105; 
x_88 = lean_ctor_get(x_82, 4);
lean_inc(x_88);
lean_dec(x_82);
x_105 = l_Lean_Expr_hasExprMVar(x_88);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = l_Lean_Expr_hasFVar(x_88);
if (x_106 == 0)
{
x_4 = x_88;
x_5 = x_71;
goto block_11;
}
else
{
lean_object* x_107; 
x_107 = lean_box(0);
x_89 = x_107;
goto block_104;
}
}
else
{
lean_object* x_108; 
x_108 = lean_box(0);
x_89 = x_108;
goto block_104;
}
block_104:
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_89);
x_90 = l_Lean_Meta_CheckAssignment_findCached(x_88, x_2, x_71);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_2);
lean_inc(x_88);
x_93 = l_Lean_Meta_CheckAssignment_check___main(x_88, x_2, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_94);
x_96 = l_Lean_Meta_CheckAssignment_cache(x_88, x_94, x_2, x_95);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_4 = x_94;
x_5 = x_97;
goto block_11;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_88);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_100 = x_93;
} else {
 lean_dec_ref(x_93);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_88);
x_102 = lean_ctor_get(x_90, 1);
lean_inc(x_102);
lean_dec(x_90);
x_103 = lean_ctor_get(x_91, 0);
lean_inc(x_103);
lean_dec(x_91);
x_4 = x_103;
x_5 = x_102;
goto block_11;
}
}
}
}
}
else
{
lean_inc(x_1);
x_4 = x_1;
x_5 = x_71;
goto block_11;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_31);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_31, 0);
lean_dec(x_110);
x_111 = lean_ctor_get(x_32, 0);
lean_inc(x_111);
lean_dec(x_32);
lean_ctor_set(x_31, 0, x_111);
return x_31;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_31, 1);
lean_inc(x_112);
lean_dec(x_31);
x_113 = lean_ctor_get(x_32, 0);
lean_inc(x_113);
lean_dec(x_32);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
}
case 2:
{
lean_object* x_121; uint8_t x_257; 
x_257 = l_Lean_Expr_hasExprMVar(x_1);
if (x_257 == 0)
{
uint8_t x_258; 
x_258 = l_Lean_Expr_hasFVar(x_1);
if (x_258 == 0)
{
lean_object* x_259; 
lean_dec(x_2);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_1);
lean_ctor_set(x_259, 1, x_3);
return x_259;
}
else
{
lean_object* x_260; 
x_260 = lean_box(0);
x_121 = x_260;
goto block_256;
}
}
else
{
lean_object* x_261; 
x_261 = lean_box(0);
x_121 = x_261;
goto block_256;
}
block_256:
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_121);
x_122 = l_Lean_Meta_CheckAssignment_findCached(x_1, x_2, x_3);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_122, 1);
x_126 = lean_ctor_get(x_122, 0);
lean_dec(x_126);
x_127 = l_Lean_Expr_mvarId_x21(x_1);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_128);
x_129 = lean_metavar_ctx_get_expr_assignment(x_128, x_127);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_2, 1);
lean_inc(x_130);
x_131 = lean_name_eq(x_127, x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; 
lean_inc(x_127);
lean_inc(x_128);
x_132 = lean_metavar_ctx_find_decl(x_128, x_127);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
lean_dec(x_128);
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set_tag(x_122, 1);
lean_ctor_set(x_122, 0, x_133);
return x_122;
}
else
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 1);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
lean_dec(x_132);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_2, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
lean_inc(x_138);
lean_inc(x_136);
x_139 = l_Lean_LocalContext_isSubPrefixOf(x_136, x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = lean_ctor_get(x_135, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_128, 0);
lean_inc(x_141);
x_142 = lean_nat_dec_eq(x_140, x_141);
lean_dec(x_141);
lean_dec(x_140);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_128);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_143, 0, x_127);
lean_ctor_set_tag(x_122, 1);
lean_ctor_set(x_122, 0, x_143);
return x_122;
}
else
{
uint8_t x_144; 
x_144 = lean_ctor_get_uint8(x_135, sizeof(void*)*4);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_145 == 0)
{
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_128);
lean_dec(x_127);
lean_free_object(x_122);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_125;
goto block_11;
}
else
{
uint8_t x_146; 
lean_inc(x_138);
x_146 = l_Lean_LocalContext_isSubPrefixOf(x_138, x_136);
if (x_146 == 0)
{
lean_dec(x_138);
lean_dec(x_135);
lean_dec(x_128);
lean_dec(x_127);
lean_free_object(x_122);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_125;
goto block_11;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_135, 2);
lean_inc(x_147);
lean_dec(x_135);
lean_inc(x_147);
lean_inc(x_138);
x_148 = l_Lean_MetavarContext_isWellFormed___main(x_128, x_138, x_147);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_147);
lean_dec(x_138);
lean_dec(x_2);
lean_dec(x_1);
x_150 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_150, 0, x_127);
lean_ctor_set_tag(x_122, 1);
lean_ctor_set(x_122, 0, x_150);
return x_122;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_free_object(x_122);
x_151 = l_Lean_Meta_CheckAssignment_mkAuxMVar(x_138, x_147, x_2, x_125);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
lean_dec(x_151);
x_154 = !lean_is_exclusive(x_152);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_156 = lean_metavar_ctx_assign_expr(x_155, x_127, x_153);
lean_ctor_set(x_152, 0, x_156);
x_4 = x_153;
x_5 = x_152;
goto block_11;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_152, 0);
x_158 = lean_ctor_get(x_152, 1);
x_159 = lean_ctor_get(x_152, 2);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_152);
lean_inc(x_153);
x_160 = lean_metavar_ctx_assign_expr(x_157, x_127, x_153);
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
lean_ctor_set(x_161, 2, x_159);
x_4 = x_153;
x_5 = x_161;
goto block_11;
}
}
}
}
}
else
{
lean_object* x_162; 
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_128);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_162, 0, x_127);
lean_ctor_set_tag(x_122, 1);
lean_ctor_set(x_122, 0, x_162);
return x_122;
}
}
}
else
{
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_128);
lean_dec(x_127);
lean_free_object(x_122);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_125;
goto block_11;
}
}
else
{
lean_object* x_163; 
lean_dec(x_132);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_2);
lean_dec(x_1);
x_163 = lean_box(1);
lean_ctor_set_tag(x_122, 1);
lean_ctor_set(x_122, 0, x_163);
return x_122;
}
}
}
else
{
lean_object* x_164; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_box(0);
lean_ctor_set_tag(x_122, 1);
lean_ctor_set(x_122, 0, x_164);
return x_122;
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_182; 
lean_dec(x_128);
lean_dec(x_127);
lean_free_object(x_122);
x_165 = lean_ctor_get(x_129, 0);
lean_inc(x_165);
lean_dec(x_129);
x_182 = l_Lean_Expr_hasExprMVar(x_165);
if (x_182 == 0)
{
uint8_t x_183; 
x_183 = l_Lean_Expr_hasFVar(x_165);
if (x_183 == 0)
{
x_4 = x_165;
x_5 = x_125;
goto block_11;
}
else
{
lean_object* x_184; 
x_184 = lean_box(0);
x_166 = x_184;
goto block_181;
}
}
else
{
lean_object* x_185; 
x_185 = lean_box(0);
x_166 = x_185;
goto block_181;
}
block_181:
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_166);
x_167 = l_Lean_Meta_CheckAssignment_findCached(x_165, x_2, x_125);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
lean_inc(x_2);
lean_inc(x_165);
x_170 = l_Lean_Meta_CheckAssignment_check___main(x_165, x_2, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
lean_inc(x_171);
x_173 = l_Lean_Meta_CheckAssignment_cache(x_165, x_171, x_2, x_172);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_4 = x_171;
x_5 = x_174;
goto block_11;
}
else
{
uint8_t x_175; 
lean_dec(x_165);
lean_dec(x_2);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_170);
if (x_175 == 0)
{
return x_170;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_170, 0);
x_177 = lean_ctor_get(x_170, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_170);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_165);
x_179 = lean_ctor_get(x_167, 1);
lean_inc(x_179);
lean_dec(x_167);
x_180 = lean_ctor_get(x_168, 0);
lean_inc(x_180);
lean_dec(x_168);
x_4 = x_180;
x_5 = x_179;
goto block_11;
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_122, 1);
lean_inc(x_186);
lean_dec(x_122);
x_187 = l_Lean_Expr_mvarId_x21(x_1);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_188);
x_189 = lean_metavar_ctx_get_expr_assignment(x_188, x_187);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_2, 1);
lean_inc(x_190);
x_191 = lean_name_eq(x_187, x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; 
lean_inc(x_187);
lean_inc(x_188);
x_192 = lean_metavar_ctx_find_decl(x_188, x_187);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_188);
lean_dec(x_2);
lean_dec(x_1);
x_193 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_193, 0, x_187);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_186);
return x_194;
}
else
{
uint8_t x_195; 
x_195 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 1);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_196 = lean_ctor_get(x_192, 0);
lean_inc(x_196);
lean_dec(x_192);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_2, 2);
lean_inc(x_198);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
lean_inc(x_199);
lean_inc(x_197);
x_200 = l_Lean_LocalContext_isSubPrefixOf(x_197, x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_201 = lean_ctor_get(x_196, 3);
lean_inc(x_201);
x_202 = lean_ctor_get(x_188, 0);
lean_inc(x_202);
x_203 = lean_nat_dec_eq(x_201, x_202);
lean_dec(x_202);
lean_dec(x_201);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_188);
lean_dec(x_2);
lean_dec(x_1);
x_204 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_204, 0, x_187);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_186);
return x_205;
}
else
{
uint8_t x_206; 
x_206 = lean_ctor_get_uint8(x_196, sizeof(void*)*4);
if (x_206 == 0)
{
uint8_t x_207; 
x_207 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_207 == 0)
{
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_188);
lean_dec(x_187);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_186;
goto block_11;
}
else
{
uint8_t x_208; 
lean_inc(x_199);
x_208 = l_Lean_LocalContext_isSubPrefixOf(x_199, x_197);
if (x_208 == 0)
{
lean_dec(x_199);
lean_dec(x_196);
lean_dec(x_188);
lean_dec(x_187);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_186;
goto block_11;
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_209 = lean_ctor_get(x_196, 2);
lean_inc(x_209);
lean_dec(x_196);
lean_inc(x_209);
lean_inc(x_199);
x_210 = l_Lean_MetavarContext_isWellFormed___main(x_188, x_199, x_209);
x_211 = lean_unbox(x_210);
lean_dec(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_209);
lean_dec(x_199);
lean_dec(x_2);
lean_dec(x_1);
x_212 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_212, 0, x_187);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_186);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_214 = l_Lean_Meta_CheckAssignment_mkAuxMVar(x_199, x_209, x_2, x_186);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_215, 2);
lean_inc(x_219);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 lean_ctor_release(x_215, 2);
 x_220 = x_215;
} else {
 lean_dec_ref(x_215);
 x_220 = lean_box(0);
}
lean_inc(x_216);
x_221 = lean_metavar_ctx_assign_expr(x_217, x_187, x_216);
if (lean_is_scalar(x_220)) {
 x_222 = lean_alloc_ctor(0, 3, 0);
} else {
 x_222 = x_220;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_218);
lean_ctor_set(x_222, 2, x_219);
x_4 = x_216;
x_5 = x_222;
goto block_11;
}
}
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_188);
lean_dec(x_2);
lean_dec(x_1);
x_223 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_223, 0, x_187);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_186);
return x_224;
}
}
}
else
{
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_188);
lean_dec(x_187);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_186;
goto block_11;
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_192);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_2);
lean_dec(x_1);
x_225 = lean_box(1);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_186);
return x_226;
}
}
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_2);
lean_dec(x_1);
x_227 = lean_box(0);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_186);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_246; 
lean_dec(x_188);
lean_dec(x_187);
x_229 = lean_ctor_get(x_189, 0);
lean_inc(x_229);
lean_dec(x_189);
x_246 = l_Lean_Expr_hasExprMVar(x_229);
if (x_246 == 0)
{
uint8_t x_247; 
x_247 = l_Lean_Expr_hasFVar(x_229);
if (x_247 == 0)
{
x_4 = x_229;
x_5 = x_186;
goto block_11;
}
else
{
lean_object* x_248; 
x_248 = lean_box(0);
x_230 = x_248;
goto block_245;
}
}
else
{
lean_object* x_249; 
x_249 = lean_box(0);
x_230 = x_249;
goto block_245;
}
block_245:
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_230);
x_231 = l_Lean_Meta_CheckAssignment_findCached(x_229, x_2, x_186);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
lean_inc(x_2);
lean_inc(x_229);
x_234 = l_Lean_Meta_CheckAssignment_check___main(x_229, x_2, x_233);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
lean_inc(x_235);
x_237 = l_Lean_Meta_CheckAssignment_cache(x_229, x_235, x_2, x_236);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_4 = x_235;
x_5 = x_238;
goto block_11;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_229);
lean_dec(x_2);
lean_dec(x_1);
x_239 = lean_ctor_get(x_234, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_234, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_241 = x_234;
} else {
 lean_dec_ref(x_234);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_229);
x_243 = lean_ctor_get(x_231, 1);
lean_inc(x_243);
lean_dec(x_231);
x_244 = lean_ctor_get(x_232, 0);
lean_inc(x_244);
lean_dec(x_232);
x_4 = x_244;
x_5 = x_243;
goto block_11;
}
}
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_2);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_122);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_122, 0);
lean_dec(x_251);
x_252 = lean_ctor_get(x_123, 0);
lean_inc(x_252);
lean_dec(x_123);
lean_ctor_set(x_122, 0, x_252);
return x_122;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_122, 1);
lean_inc(x_253);
lean_dec(x_122);
x_254 = lean_ctor_get(x_123, 0);
lean_inc(x_254);
lean_dec(x_123);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
}
}
case 5:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_296; uint8_t x_312; 
x_262 = lean_ctor_get(x_1, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_1, 1);
lean_inc(x_263);
x_312 = l_Lean_Expr_hasExprMVar(x_262);
if (x_312 == 0)
{
uint8_t x_313; 
x_313 = l_Lean_Expr_hasFVar(x_262);
if (x_313 == 0)
{
x_264 = x_262;
x_265 = x_3;
goto block_295;
}
else
{
lean_object* x_314; 
x_314 = lean_box(0);
x_296 = x_314;
goto block_311;
}
}
else
{
lean_object* x_315; 
x_315 = lean_box(0);
x_296 = x_315;
goto block_311;
}
block_295:
{
lean_object* x_266; lean_object* x_267; lean_object* x_275; uint8_t x_291; 
x_291 = l_Lean_Expr_hasExprMVar(x_263);
if (x_291 == 0)
{
uint8_t x_292; 
x_292 = l_Lean_Expr_hasFVar(x_263);
if (x_292 == 0)
{
lean_dec(x_2);
x_266 = x_263;
x_267 = x_265;
goto block_274;
}
else
{
lean_object* x_293; 
x_293 = lean_box(0);
x_275 = x_293;
goto block_290;
}
}
else
{
lean_object* x_294; 
x_294 = lean_box(0);
x_275 = x_294;
goto block_290;
}
block_274:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_expr_update_app(x_1, x_264, x_266);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_266);
lean_dec(x_264);
lean_dec(x_1);
x_270 = l_Lean_Expr_Inhabited;
x_271 = l_Lean_Expr_updateApp_x21___closed__1;
x_272 = lean_panic_fn(x_271);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_267);
return x_273;
}
}
block_290:
{
lean_object* x_276; lean_object* x_277; 
lean_dec(x_275);
x_276 = l_Lean_Meta_CheckAssignment_findCached(x_263, x_2, x_265);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
lean_inc(x_2);
lean_inc(x_263);
x_279 = l_Lean_Meta_CheckAssignment_check___main(x_263, x_2, x_278);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
lean_inc(x_280);
x_282 = l_Lean_Meta_CheckAssignment_cache(x_263, x_280, x_2, x_281);
lean_dec(x_2);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_266 = x_280;
x_267 = x_283;
goto block_274;
}
else
{
uint8_t x_284; 
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_2);
lean_dec(x_1);
x_284 = !lean_is_exclusive(x_279);
if (x_284 == 0)
{
return x_279;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_279, 0);
x_286 = lean_ctor_get(x_279, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_279);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_263);
lean_dec(x_2);
x_288 = lean_ctor_get(x_276, 1);
lean_inc(x_288);
lean_dec(x_276);
x_289 = lean_ctor_get(x_277, 0);
lean_inc(x_289);
lean_dec(x_277);
x_266 = x_289;
x_267 = x_288;
goto block_274;
}
}
}
block_311:
{
lean_object* x_297; lean_object* x_298; 
lean_dec(x_296);
x_297 = l_Lean_Meta_CheckAssignment_findCached(x_262, x_2, x_3);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
lean_inc(x_2);
lean_inc(x_262);
x_300 = l_Lean_Meta_CheckAssignment_check___main(x_262, x_2, x_299);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
lean_inc(x_301);
x_303 = l_Lean_Meta_CheckAssignment_cache(x_262, x_301, x_2, x_302);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
lean_dec(x_303);
x_264 = x_301;
x_265 = x_304;
goto block_295;
}
else
{
uint8_t x_305; 
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_2);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_300);
if (x_305 == 0)
{
return x_300;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_300, 0);
x_307 = lean_ctor_get(x_300, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_300);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; 
lean_dec(x_262);
x_309 = lean_ctor_get(x_297, 1);
lean_inc(x_309);
lean_dec(x_297);
x_310 = lean_ctor_get(x_298, 0);
lean_inc(x_310);
lean_dec(x_298);
x_264 = x_310;
x_265 = x_309;
goto block_295;
}
}
}
case 6:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_352; uint8_t x_368; 
x_316 = lean_ctor_get(x_1, 1);
lean_inc(x_316);
x_317 = lean_ctor_get(x_1, 2);
lean_inc(x_317);
x_368 = l_Lean_Expr_hasExprMVar(x_316);
if (x_368 == 0)
{
uint8_t x_369; 
x_369 = l_Lean_Expr_hasFVar(x_316);
if (x_369 == 0)
{
x_318 = x_316;
x_319 = x_3;
goto block_351;
}
else
{
lean_object* x_370; 
x_370 = lean_box(0);
x_352 = x_370;
goto block_367;
}
}
else
{
lean_object* x_371; 
x_371 = lean_box(0);
x_352 = x_371;
goto block_367;
}
block_351:
{
lean_object* x_320; lean_object* x_321; lean_object* x_331; uint8_t x_347; 
x_347 = l_Lean_Expr_hasExprMVar(x_317);
if (x_347 == 0)
{
uint8_t x_348; 
x_348 = l_Lean_Expr_hasFVar(x_317);
if (x_348 == 0)
{
lean_dec(x_2);
x_320 = x_317;
x_321 = x_319;
goto block_330;
}
else
{
lean_object* x_349; 
x_349 = lean_box(0);
x_331 = x_349;
goto block_346;
}
}
else
{
lean_object* x_350; 
x_350 = lean_box(0);
x_331 = x_350;
goto block_346;
}
block_330:
{
if (lean_obj_tag(x_1) == 6)
{
uint64_t x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_323 = (uint8_t)((x_322 << 24) >> 61);
x_324 = lean_expr_update_lambda(x_1, x_323, x_318, x_320);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_321);
return x_325;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_320);
lean_dec(x_318);
lean_dec(x_1);
x_326 = l_Lean_Expr_Inhabited;
x_327 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_328 = lean_panic_fn(x_327);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_321);
return x_329;
}
}
block_346:
{
lean_object* x_332; lean_object* x_333; 
lean_dec(x_331);
x_332 = l_Lean_Meta_CheckAssignment_findCached(x_317, x_2, x_319);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
lean_inc(x_2);
lean_inc(x_317);
x_335 = l_Lean_Meta_CheckAssignment_check___main(x_317, x_2, x_334);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
lean_inc(x_336);
x_338 = l_Lean_Meta_CheckAssignment_cache(x_317, x_336, x_2, x_337);
lean_dec(x_2);
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
lean_dec(x_338);
x_320 = x_336;
x_321 = x_339;
goto block_330;
}
else
{
uint8_t x_340; 
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_2);
lean_dec(x_1);
x_340 = !lean_is_exclusive(x_335);
if (x_340 == 0)
{
return x_335;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_335, 0);
x_342 = lean_ctor_get(x_335, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_335);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_317);
lean_dec(x_2);
x_344 = lean_ctor_get(x_332, 1);
lean_inc(x_344);
lean_dec(x_332);
x_345 = lean_ctor_get(x_333, 0);
lean_inc(x_345);
lean_dec(x_333);
x_320 = x_345;
x_321 = x_344;
goto block_330;
}
}
}
block_367:
{
lean_object* x_353; lean_object* x_354; 
lean_dec(x_352);
x_353 = l_Lean_Meta_CheckAssignment_findCached(x_316, x_2, x_3);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
lean_inc(x_2);
lean_inc(x_316);
x_356 = l_Lean_Meta_CheckAssignment_check___main(x_316, x_2, x_355);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
lean_inc(x_357);
x_359 = l_Lean_Meta_CheckAssignment_cache(x_316, x_357, x_2, x_358);
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
lean_dec(x_359);
x_318 = x_357;
x_319 = x_360;
goto block_351;
}
else
{
uint8_t x_361; 
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_2);
lean_dec(x_1);
x_361 = !lean_is_exclusive(x_356);
if (x_361 == 0)
{
return x_356;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_356, 0);
x_363 = lean_ctor_get(x_356, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_356);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
else
{
lean_object* x_365; lean_object* x_366; 
lean_dec(x_316);
x_365 = lean_ctor_get(x_353, 1);
lean_inc(x_365);
lean_dec(x_353);
x_366 = lean_ctor_get(x_354, 0);
lean_inc(x_366);
lean_dec(x_354);
x_318 = x_366;
x_319 = x_365;
goto block_351;
}
}
}
case 7:
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_408; uint8_t x_424; 
x_372 = lean_ctor_get(x_1, 1);
lean_inc(x_372);
x_373 = lean_ctor_get(x_1, 2);
lean_inc(x_373);
x_424 = l_Lean_Expr_hasExprMVar(x_372);
if (x_424 == 0)
{
uint8_t x_425; 
x_425 = l_Lean_Expr_hasFVar(x_372);
if (x_425 == 0)
{
x_374 = x_372;
x_375 = x_3;
goto block_407;
}
else
{
lean_object* x_426; 
x_426 = lean_box(0);
x_408 = x_426;
goto block_423;
}
}
else
{
lean_object* x_427; 
x_427 = lean_box(0);
x_408 = x_427;
goto block_423;
}
block_407:
{
lean_object* x_376; lean_object* x_377; lean_object* x_387; uint8_t x_403; 
x_403 = l_Lean_Expr_hasExprMVar(x_373);
if (x_403 == 0)
{
uint8_t x_404; 
x_404 = l_Lean_Expr_hasFVar(x_373);
if (x_404 == 0)
{
lean_dec(x_2);
x_376 = x_373;
x_377 = x_375;
goto block_386;
}
else
{
lean_object* x_405; 
x_405 = lean_box(0);
x_387 = x_405;
goto block_402;
}
}
else
{
lean_object* x_406; 
x_406 = lean_box(0);
x_387 = x_406;
goto block_402;
}
block_386:
{
if (lean_obj_tag(x_1) == 7)
{
uint64_t x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; 
x_378 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_379 = (uint8_t)((x_378 << 24) >> 61);
x_380 = lean_expr_update_forall(x_1, x_379, x_374, x_376);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_377);
return x_381;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_376);
lean_dec(x_374);
lean_dec(x_1);
x_382 = l_Lean_Expr_Inhabited;
x_383 = l_Lean_Expr_updateForallE_x21___closed__1;
x_384 = lean_panic_fn(x_383);
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_377);
return x_385;
}
}
block_402:
{
lean_object* x_388; lean_object* x_389; 
lean_dec(x_387);
x_388 = l_Lean_Meta_CheckAssignment_findCached(x_373, x_2, x_375);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
lean_inc(x_2);
lean_inc(x_373);
x_391 = l_Lean_Meta_CheckAssignment_check___main(x_373, x_2, x_390);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
lean_inc(x_392);
x_394 = l_Lean_Meta_CheckAssignment_cache(x_373, x_392, x_2, x_393);
lean_dec(x_2);
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec(x_394);
x_376 = x_392;
x_377 = x_395;
goto block_386;
}
else
{
uint8_t x_396; 
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_2);
lean_dec(x_1);
x_396 = !lean_is_exclusive(x_391);
if (x_396 == 0)
{
return x_391;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_391, 0);
x_398 = lean_ctor_get(x_391, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_391);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
return x_399;
}
}
}
else
{
lean_object* x_400; lean_object* x_401; 
lean_dec(x_373);
lean_dec(x_2);
x_400 = lean_ctor_get(x_388, 1);
lean_inc(x_400);
lean_dec(x_388);
x_401 = lean_ctor_get(x_389, 0);
lean_inc(x_401);
lean_dec(x_389);
x_376 = x_401;
x_377 = x_400;
goto block_386;
}
}
}
block_423:
{
lean_object* x_409; lean_object* x_410; 
lean_dec(x_408);
x_409 = l_Lean_Meta_CheckAssignment_findCached(x_372, x_2, x_3);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
lean_inc(x_2);
lean_inc(x_372);
x_412 = l_Lean_Meta_CheckAssignment_check___main(x_372, x_2, x_411);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
lean_inc(x_413);
x_415 = l_Lean_Meta_CheckAssignment_cache(x_372, x_413, x_2, x_414);
x_416 = lean_ctor_get(x_415, 1);
lean_inc(x_416);
lean_dec(x_415);
x_374 = x_413;
x_375 = x_416;
goto block_407;
}
else
{
uint8_t x_417; 
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_2);
lean_dec(x_1);
x_417 = !lean_is_exclusive(x_412);
if (x_417 == 0)
{
return x_412;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_412, 0);
x_419 = lean_ctor_get(x_412, 1);
lean_inc(x_419);
lean_inc(x_418);
lean_dec(x_412);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
}
else
{
lean_object* x_421; lean_object* x_422; 
lean_dec(x_372);
x_421 = lean_ctor_get(x_409, 1);
lean_inc(x_421);
lean_dec(x_409);
x_422 = lean_ctor_get(x_410, 0);
lean_inc(x_422);
lean_dec(x_410);
x_374 = x_422;
x_375 = x_421;
goto block_407;
}
}
}
case 8:
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_486; uint8_t x_502; 
x_428 = lean_ctor_get(x_1, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_1, 2);
lean_inc(x_429);
x_430 = lean_ctor_get(x_1, 3);
lean_inc(x_430);
x_502 = l_Lean_Expr_hasExprMVar(x_428);
if (x_502 == 0)
{
uint8_t x_503; 
x_503 = l_Lean_Expr_hasFVar(x_428);
if (x_503 == 0)
{
x_431 = x_428;
x_432 = x_3;
goto block_485;
}
else
{
lean_object* x_504; 
x_504 = lean_box(0);
x_486 = x_504;
goto block_501;
}
}
else
{
lean_object* x_505; 
x_505 = lean_box(0);
x_486 = x_505;
goto block_501;
}
block_485:
{
lean_object* x_433; lean_object* x_434; lean_object* x_465; uint8_t x_481; 
x_481 = l_Lean_Expr_hasExprMVar(x_429);
if (x_481 == 0)
{
uint8_t x_482; 
x_482 = l_Lean_Expr_hasFVar(x_429);
if (x_482 == 0)
{
x_433 = x_429;
x_434 = x_432;
goto block_464;
}
else
{
lean_object* x_483; 
x_483 = lean_box(0);
x_465 = x_483;
goto block_480;
}
}
else
{
lean_object* x_484; 
x_484 = lean_box(0);
x_465 = x_484;
goto block_480;
}
block_464:
{
lean_object* x_435; lean_object* x_436; lean_object* x_444; uint8_t x_460; 
x_460 = l_Lean_Expr_hasExprMVar(x_430);
if (x_460 == 0)
{
uint8_t x_461; 
x_461 = l_Lean_Expr_hasFVar(x_430);
if (x_461 == 0)
{
lean_dec(x_2);
x_435 = x_430;
x_436 = x_434;
goto block_443;
}
else
{
lean_object* x_462; 
x_462 = lean_box(0);
x_444 = x_462;
goto block_459;
}
}
else
{
lean_object* x_463; 
x_463 = lean_box(0);
x_444 = x_463;
goto block_459;
}
block_443:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_expr_update_let(x_1, x_431, x_433, x_435);
x_438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_436);
return x_438;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_435);
lean_dec(x_433);
lean_dec(x_431);
lean_dec(x_1);
x_439 = l_Lean_Expr_Inhabited;
x_440 = l_Lean_Expr_updateLet_x21___closed__1;
x_441 = lean_panic_fn(x_440);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_436);
return x_442;
}
}
block_459:
{
lean_object* x_445; lean_object* x_446; 
lean_dec(x_444);
x_445 = l_Lean_Meta_CheckAssignment_findCached(x_430, x_2, x_434);
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
lean_inc(x_2);
lean_inc(x_430);
x_448 = l_Lean_Meta_CheckAssignment_check___main(x_430, x_2, x_447);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
lean_inc(x_449);
x_451 = l_Lean_Meta_CheckAssignment_cache(x_430, x_449, x_2, x_450);
lean_dec(x_2);
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
lean_dec(x_451);
x_435 = x_449;
x_436 = x_452;
goto block_443;
}
else
{
uint8_t x_453; 
lean_dec(x_433);
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_2);
lean_dec(x_1);
x_453 = !lean_is_exclusive(x_448);
if (x_453 == 0)
{
return x_448;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_448, 0);
x_455 = lean_ctor_get(x_448, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_448);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
else
{
lean_object* x_457; lean_object* x_458; 
lean_dec(x_430);
lean_dec(x_2);
x_457 = lean_ctor_get(x_445, 1);
lean_inc(x_457);
lean_dec(x_445);
x_458 = lean_ctor_get(x_446, 0);
lean_inc(x_458);
lean_dec(x_446);
x_435 = x_458;
x_436 = x_457;
goto block_443;
}
}
}
block_480:
{
lean_object* x_466; lean_object* x_467; 
lean_dec(x_465);
x_466 = l_Lean_Meta_CheckAssignment_findCached(x_429, x_2, x_432);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; 
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec(x_466);
lean_inc(x_2);
lean_inc(x_429);
x_469 = l_Lean_Meta_CheckAssignment_check___main(x_429, x_2, x_468);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec(x_469);
lean_inc(x_470);
x_472 = l_Lean_Meta_CheckAssignment_cache(x_429, x_470, x_2, x_471);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
lean_dec(x_472);
x_433 = x_470;
x_434 = x_473;
goto block_464;
}
else
{
uint8_t x_474; 
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_2);
lean_dec(x_1);
x_474 = !lean_is_exclusive(x_469);
if (x_474 == 0)
{
return x_469;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_469, 0);
x_476 = lean_ctor_get(x_469, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_469);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
return x_477;
}
}
}
else
{
lean_object* x_478; lean_object* x_479; 
lean_dec(x_429);
x_478 = lean_ctor_get(x_466, 1);
lean_inc(x_478);
lean_dec(x_466);
x_479 = lean_ctor_get(x_467, 0);
lean_inc(x_479);
lean_dec(x_467);
x_433 = x_479;
x_434 = x_478;
goto block_464;
}
}
}
block_501:
{
lean_object* x_487; lean_object* x_488; 
lean_dec(x_486);
x_487 = l_Lean_Meta_CheckAssignment_findCached(x_428, x_2, x_3);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; 
x_489 = lean_ctor_get(x_487, 1);
lean_inc(x_489);
lean_dec(x_487);
lean_inc(x_2);
lean_inc(x_428);
x_490 = l_Lean_Meta_CheckAssignment_check___main(x_428, x_2, x_489);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec(x_490);
lean_inc(x_491);
x_493 = l_Lean_Meta_CheckAssignment_cache(x_428, x_491, x_2, x_492);
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
lean_dec(x_493);
x_431 = x_491;
x_432 = x_494;
goto block_485;
}
else
{
uint8_t x_495; 
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_2);
lean_dec(x_1);
x_495 = !lean_is_exclusive(x_490);
if (x_495 == 0)
{
return x_490;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_490, 0);
x_497 = lean_ctor_get(x_490, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_490);
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
return x_498;
}
}
}
else
{
lean_object* x_499; lean_object* x_500; 
lean_dec(x_428);
x_499 = lean_ctor_get(x_487, 1);
lean_inc(x_499);
lean_dec(x_487);
x_500 = lean_ctor_get(x_488, 0);
lean_inc(x_500);
lean_dec(x_488);
x_431 = x_500;
x_432 = x_499;
goto block_485;
}
}
}
case 10:
{
lean_object* x_506; lean_object* x_507; uint8_t x_523; 
x_506 = lean_ctor_get(x_1, 1);
lean_inc(x_506);
x_523 = l_Lean_Expr_hasExprMVar(x_506);
if (x_523 == 0)
{
uint8_t x_524; 
x_524 = l_Lean_Expr_hasFVar(x_506);
if (x_524 == 0)
{
lean_dec(x_2);
x_12 = x_506;
x_13 = x_3;
goto block_20;
}
else
{
lean_object* x_525; 
x_525 = lean_box(0);
x_507 = x_525;
goto block_522;
}
}
else
{
lean_object* x_526; 
x_526 = lean_box(0);
x_507 = x_526;
goto block_522;
}
block_522:
{
lean_object* x_508; lean_object* x_509; 
lean_dec(x_507);
x_508 = l_Lean_Meta_CheckAssignment_findCached(x_506, x_2, x_3);
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; 
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
lean_inc(x_2);
lean_inc(x_506);
x_511 = l_Lean_Meta_CheckAssignment_check___main(x_506, x_2, x_510);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
lean_inc(x_512);
x_514 = l_Lean_Meta_CheckAssignment_cache(x_506, x_512, x_2, x_513);
lean_dec(x_2);
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
lean_dec(x_514);
x_12 = x_512;
x_13 = x_515;
goto block_20;
}
else
{
uint8_t x_516; 
lean_dec(x_506);
lean_dec(x_2);
lean_dec(x_1);
x_516 = !lean_is_exclusive(x_511);
if (x_516 == 0)
{
return x_511;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_511, 0);
x_518 = lean_ctor_get(x_511, 1);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_511);
x_519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_518);
return x_519;
}
}
}
else
{
lean_object* x_520; lean_object* x_521; 
lean_dec(x_506);
lean_dec(x_2);
x_520 = lean_ctor_get(x_508, 1);
lean_inc(x_520);
lean_dec(x_508);
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
lean_dec(x_509);
x_12 = x_521;
x_13 = x_520;
goto block_20;
}
}
}
case 11:
{
lean_object* x_527; lean_object* x_528; uint8_t x_544; 
x_527 = lean_ctor_get(x_1, 2);
lean_inc(x_527);
x_544 = l_Lean_Expr_hasExprMVar(x_527);
if (x_544 == 0)
{
uint8_t x_545; 
x_545 = l_Lean_Expr_hasFVar(x_527);
if (x_545 == 0)
{
lean_dec(x_2);
x_21 = x_527;
x_22 = x_3;
goto block_29;
}
else
{
lean_object* x_546; 
x_546 = lean_box(0);
x_528 = x_546;
goto block_543;
}
}
else
{
lean_object* x_547; 
x_547 = lean_box(0);
x_528 = x_547;
goto block_543;
}
block_543:
{
lean_object* x_529; lean_object* x_530; 
lean_dec(x_528);
x_529 = l_Lean_Meta_CheckAssignment_findCached(x_527, x_2, x_3);
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
lean_inc(x_2);
lean_inc(x_527);
x_532 = l_Lean_Meta_CheckAssignment_check___main(x_527, x_2, x_531);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
lean_dec(x_532);
lean_inc(x_533);
x_535 = l_Lean_Meta_CheckAssignment_cache(x_527, x_533, x_2, x_534);
lean_dec(x_2);
x_536 = lean_ctor_get(x_535, 1);
lean_inc(x_536);
lean_dec(x_535);
x_21 = x_533;
x_22 = x_536;
goto block_29;
}
else
{
uint8_t x_537; 
lean_dec(x_527);
lean_dec(x_2);
lean_dec(x_1);
x_537 = !lean_is_exclusive(x_532);
if (x_537 == 0)
{
return x_532;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_538 = lean_ctor_get(x_532, 0);
x_539 = lean_ctor_get(x_532, 1);
lean_inc(x_539);
lean_inc(x_538);
lean_dec(x_532);
x_540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_540, 0, x_538);
lean_ctor_set(x_540, 1, x_539);
return x_540;
}
}
}
else
{
lean_object* x_541; lean_object* x_542; 
lean_dec(x_527);
lean_dec(x_2);
x_541 = lean_ctor_get(x_529, 1);
lean_inc(x_541);
lean_dec(x_529);
x_542 = lean_ctor_get(x_530, 0);
lean_inc(x_542);
lean_dec(x_530);
x_21 = x_542;
x_22 = x_541;
goto block_29;
}
}
}
case 12:
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_1);
x_548 = l_Lean_Meta_CheckAssignment_check___main___closed__1;
x_549 = l_unreachable_x21___rarg(x_548);
x_550 = lean_apply_2(x_549, x_2, x_3);
return x_550;
}
default: 
{
lean_object* x_551; 
lean_dec(x_2);
x_551 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_551, 0, x_1);
lean_ctor_set(x_551, 1, x_3);
return x_551;
}
}
block_11:
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_4);
x_6 = l_Lean_Meta_CheckAssignment_cache(x_1, x_4, x_2, x_5);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
block_20:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_expr_update_mdata(x_1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_1);
x_16 = l_Lean_Expr_Inhabited;
x_17 = l_Lean_Expr_updateMData_x21___closed__2;
x_18 = lean_panic_fn(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
}
block_29:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_expr_update_proj(x_1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_1);
x_25 = l_Lean_Expr_Inhabited;
x_26 = l_Lean_Expr_updateProj_x21___closed__2;
x_27 = lean_panic_fn(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
}
}
lean_object* l_Lean_Meta_CheckAssignment_check(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_CheckAssignment_check___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isDefEq");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assignment");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__4;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("occursCheck");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__6;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__8;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_formatEntry___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("outOfScopeFVar");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__6;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" @ ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__12;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("readOnlyMVarWithBiggerLCtx");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__6;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__18;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mvarTypeNotWellFormedInSmallerLCtx");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__6;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__21;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__9;
x_12 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__1(x_11, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = l_Lean_mkMVar(x_1);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_umapMAux___main___at_Lean_MessageData_coeOfArrayExpr___spec__1(x_24, x_2);
x_26 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_29 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_3);
x_31 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__8;
x_33 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__2(x_32, x_31, x_5, x_21);
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
}
}
case 1:
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_6);
return x_41;
}
case 2:
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_71; uint8_t x_72; 
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
lean_dec(x_4);
x_71 = lean_ctor_get(x_6, 4);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_71, sizeof(void*)*1);
lean_dec(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = 0;
x_43 = x_73;
x_44 = x_6;
goto block_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__16;
x_75 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__1(x_74, x_5, x_6);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_unbox(x_76);
lean_dec(x_76);
x_43 = x_78;
x_44 = x_77;
goto block_70;
}
block_70:
{
if (x_43 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_47 = l_Lean_mkFVar(x_42);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15;
x_50 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_mkMVar(x_1);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Array_umapMAux___main___at_Lean_MessageData_coeOfArrayExpr___spec__1(x_54, x_2);
x_56 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_59 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_3);
x_61 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__12;
x_63 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__2(x_62, x_61, x_5, x_44);
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
}
case 3:
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_108; uint8_t x_109; 
x_79 = lean_ctor_get(x_4, 0);
lean_inc(x_79);
lean_dec(x_4);
x_108 = lean_ctor_get(x_6, 4);
lean_inc(x_108);
x_109 = lean_ctor_get_uint8(x_108, sizeof(void*)*1);
lean_dec(x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = 0;
x_80 = x_110;
x_81 = x_6;
goto block_107;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__19;
x_112 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__1(x_111, x_5, x_6);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_unbox(x_113);
lean_dec(x_113);
x_80 = x_115;
x_81 = x_114;
goto block_107;
}
block_107:
{
if (x_80 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_79);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_84 = l_Lean_mkMVar(x_79);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15;
x_87 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_mkMVar(x_1);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Array_umapMAux___main___at_Lean_MessageData_coeOfArrayExpr___spec__1(x_91, x_2);
x_93 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
x_95 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_96 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_3);
x_98 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__18;
x_100 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__2(x_99, x_98, x_5, x_81);
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
}
}
case 4:
{
lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_145; uint8_t x_146; 
x_116 = lean_ctor_get(x_4, 0);
lean_inc(x_116);
lean_dec(x_4);
x_145 = lean_ctor_get(x_6, 4);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_145, sizeof(void*)*1);
lean_dec(x_145);
if (x_146 == 0)
{
uint8_t x_147; 
x_147 = 0;
x_117 = x_147;
x_118 = x_6;
goto block_144;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__22;
x_149 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__1(x_148, x_5, x_6);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_unbox(x_150);
lean_dec(x_150);
x_117 = x_152;
x_118 = x_151;
goto block_144;
}
block_144:
{
if (x_117 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_116);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_121 = l_Lean_mkMVar(x_116);
x_122 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15;
x_124 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_mkMVar(x_1);
x_126 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Array_umapMAux___main___at_Lean_MessageData_coeOfArrayExpr___spec__1(x_128, x_2);
x_130 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_130);
x_132 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_133 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_134, 0, x_3);
x_135 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__21;
x_137 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__2(x_136, x_135, x_5, x_118);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_137, 0);
lean_dec(x_139);
x_140 = lean_box(0);
lean_ctor_set(x_137, 0, x_140);
return x_137;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_dec(x_137);
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
}
default: 
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = lean_ctor_get(x_4, 0);
lean_inc(x_153);
lean_dec(x_4);
x_154 = lean_ctor_get(x_6, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_6, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_5, 1);
lean_inc(x_156);
x_157 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
lean_ctor_set(x_157, 2, x_156);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_6);
return x_159;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_LocalContext_containsFVar(x_9, x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
lean_object* l_mkHashMap___at_Lean_Meta_checkAssignment___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_checkAssignment___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_checkAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_68; 
x_68 = l_Lean_Expr_hasExprMVar(x_3);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = l_Lean_Expr_hasFVar(x_3);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_3);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_5);
return x_71;
}
else
{
lean_object* x_72; 
x_72 = lean_box(0);
x_6 = x_72;
goto block_67;
}
}
else
{
lean_object* x_73; 
x_73 = lean_box(0);
x_6 = x_73;
goto block_67;
}
block_67:
{
uint8_t x_7; 
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 3);
x_10 = l_Lean_MetavarContext_getDecl(x_8, x_1);
x_11 = lean_array_get_size(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1(x_2, x_10, x_2, x_11, x_12);
lean_dec(x_11);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_17 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_10);
lean_ctor_set(x_17, 3, x_2);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*4 + 1, x_13);
x_18 = l_Lean_Meta_checkAssignment___closed__1;
lean_inc(x_8);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_18);
lean_inc(x_3);
x_20 = l_Lean_Meta_CheckAssignment_check___main(x_3, x_17, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_5, 3, x_26);
lean_ctor_set(x_5, 1, x_25);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_5, 3, x_31);
lean_ctor_set(x_5, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec(x_20);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_ctor_set(x_5, 3, x_35);
x_36 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure(x_1, x_2, x_3, x_33, x_4, x_5);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_37 = lean_ctor_get(x_5, 0);
x_38 = lean_ctor_get(x_5, 1);
x_39 = lean_ctor_get(x_5, 2);
x_40 = lean_ctor_get(x_5, 3);
x_41 = lean_ctor_get(x_5, 4);
x_42 = lean_ctor_get(x_5, 5);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_5);
x_43 = l_Lean_MetavarContext_getDecl(x_38, x_1);
x_44 = lean_array_get_size(x_2);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1(x_2, x_43, x_2, x_44, x_45);
lean_dec(x_44);
x_47 = lean_ctor_get(x_4, 1);
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1 + 1);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_47);
x_50 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_1);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_2);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*4 + 1, x_46);
x_51 = l_Lean_Meta_checkAssignment___closed__1;
lean_inc(x_38);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_40);
lean_ctor_set(x_52, 2, x_51);
lean_inc(x_3);
x_53 = l_Lean_Meta_CheckAssignment_check___main(x_3, x_50, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_38);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_54);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_37);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_39);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set(x_60, 4, x_41);
lean_ctor_set(x_60, 5, x_42);
if (lean_is_scalar(x_56)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_56;
}
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_53, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_dec(x_53);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_65, 0, x_37);
lean_ctor_set(x_65, 1, x_38);
lean_ctor_set(x_65, 2, x_39);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set(x_65, 4, x_41);
lean_ctor_set(x_65, 5, x_42);
x_66 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure(x_1, x_2, x_3, x_62, x_4, x_65);
return x_66;
}
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_checkAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_checkAssignment(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_5);
x_11 = lean_nat_dec_lt(x_7, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_apply_4(x_1, x_2, x_3, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Expr_Inhabited;
x_14 = lean_array_get(x_13, x_4, x_6);
x_15 = lean_array_fget(x_5, x_7);
lean_inc(x_1);
lean_inc(x_8);
x_16 = lean_apply_4(x_1, x_14, x_15, x_8, x_9);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_26 = lean_nat_add(x_7, x_24);
lean_dec(x_7);
x_6 = x_25;
x_7 = x_26;
x_9 = x_23;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__processAssignmentFOApproxAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Expr_getAppNumArgsAux___main(x_4, x_7);
x_9 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_8);
x_10 = lean_mk_array(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_8, x_11);
lean_dec(x_8);
lean_inc(x_4);
x_13 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_4, x_10, x_12);
x_14 = l_Array_isEmpty___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_get_size(x_13);
x_16 = lean_array_get_size(x_3);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_16, x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
x_19 = l_Lean_Expr_getAppFn___main(x_4);
lean_dec(x_4);
x_20 = l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main(x_1, x_2, x_19, x_3, x_13, x_7, x_7, x_5, x_6);
lean_dec(x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_Expr_getAppFn___main(x_4);
lean_dec(x_4);
x_22 = lean_nat_sub(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_23 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_22, x_13, x_7, x_21);
x_24 = l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main(x_1, x_2, x_23, x_3, x_13, x_7, x_22, x_5, x_6);
lean_dec(x_13);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_nat_sub(x_16, x_15);
lean_dec(x_15);
lean_dec(x_16);
x_26 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_25, x_3, x_7, x_2);
x_27 = l_Lean_Expr_getAppFn___main(x_4);
lean_dec(x_4);
x_28 = l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main(x_1, x_26, x_27, x_3, x_13, x_25, x_7, x_5, x_6);
lean_dec(x_13);
return x_28;
}
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__processAssignmentFOApproxAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_ExprDefEq_10__processAssignmentFOApproxAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_10__processAssignmentFOApproxAux___boxed), 6, 4);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_5);
lean_closure_set(x_9, 3, x_6);
lean_inc(x_7);
x_10 = l_Lean_Meta_try(x_9, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = l_EIO_Monad___closed__1;
x_16 = lean_alloc_closure((void*)(l_ReaderT_pure___rarg___boxed), 4, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, lean_box(0));
lean_closure_set(x_16, 2, x_11);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main), 8, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_5);
x_18 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_14, x_2, x_3, x_6, x_16, x_17, x_7, x_13);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__simpAssignmentArgAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_inc(x_2);
x_5 = l_Lean_Meta_getLocalDecl(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_LocalDecl_value_x3f(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_2);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_10; 
lean_free_object(x_5);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_1 = x_10;
x_3 = x_8;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = l_Lean_LocalDecl_value_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_1 = x_16;
x_3 = x_13;
goto _start;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
case 10:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_1 = x_22;
goto _start;
}
default: 
{
lean_object* x_24; 
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__simpAssignmentArgAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_ExprDefEq_12__simpAssignmentArgAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_13__simpAssignmentArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_getAppFn___main(x_1);
x_5 = l_Lean_Expr_hasExprMVar(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_ExprDefEq_12__simpAssignmentArgAux___main(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_instantiateMVars(x_1, x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Init_Lean_Meta_ExprDefEq_12__simpAssignmentArgAux___main(x_8, x_2, x_9);
return x_10;
}
}
}
uint8_t l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_LocalContext_containsFVar(x_3, x_2);
return x_4;
}
}
uint8_t l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_eqv(x_2, x_1);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_tracer;
x_2 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_3 = l_Lean_simpleMonadTracerAdapter___rarg(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeMismatch");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__6;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_8);
x_12 = lean_nat_dec_lt(x_7, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 2);
lean_inc(x_15);
x_16 = l_Lean_Meta_instantiateMVars(x_6, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
if (x_19 == 0)
{
lean_object* x_443; 
x_443 = lean_box(0);
x_20 = x_443;
goto block_442;
}
else
{
uint8_t x_444; 
x_444 = l_Array_isEmpty___rarg(x_8);
if (x_444 == 0)
{
lean_object* x_445; 
x_445 = lean_box(0);
x_20 = x_445;
goto block_442;
}
else
{
lean_object* x_446; uint8_t x_447; 
x_446 = l_Lean_Expr_getAppFn___main(x_17);
x_447 = lean_expr_eqv(x_446, x_4);
lean_dec(x_446);
if (x_447 == 0)
{
lean_object* x_448; 
x_448 = lean_box(0);
x_20 = x_448;
goto block_442;
}
else
{
lean_object* x_449; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
x_449 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_8, x_17, x_9, x_18);
return x_449;
}
}
}
block_442:
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_20);
x_21 = l_Lean_Expr_mvarId_x21(x_4);
lean_inc(x_17);
lean_inc(x_8);
lean_inc(x_21);
x_22 = l_Lean_Meta_checkAssignment(x_21, x_8, x_17, x_9, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
if (x_19 == 0)
{
uint8_t x_24; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = 0;
x_27 = lean_box(x_26);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
x_33 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_8, x_17, x_9, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
lean_inc(x_9);
lean_inc(x_8);
x_36 = l_Lean_Meta_mkLambda(x_8, x_35, x_9, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_39, 0, x_5);
x_40 = l_Id_Monad;
x_41 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
x_42 = l_Array_anyRangeMAux___main___rarg(x_40, x_8, x_11, lean_box(0), x_39, x_41);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_3);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_usingDefault), 4, 1);
lean_closure_set(x_44, 0, x_1);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_44);
x_45 = l_Lean_Meta_inferTypeAuxAux___main(x_44, x_4, x_9, x_38);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_9);
lean_inc(x_37);
x_48 = l_Lean_Meta_inferTypeAuxAux___main(x_44, x_37, x_9, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_52 = 1;
lean_ctor_set_uint8(x_13, sizeof(void*)*1 + 4, x_52);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_13);
lean_ctor_set(x_53, 1, x_14);
lean_ctor_set(x_53, 2, x_15);
lean_inc(x_49);
lean_inc(x_46);
x_54 = lean_apply_4(x_2, x_46, x_49, x_53, x_50);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
if (x_56 == 0)
{
uint8_t x_57; 
lean_dec(x_21);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_54, 1);
x_59 = lean_ctor_get(x_54, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_58, 4);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_60, sizeof(void*)*1);
lean_dec(x_60);
if (x_61 == 0)
{
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
return x_54;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_54);
x_62 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_63 = l_Lean_Meta_tracer;
x_64 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4;
x_65 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_62, x_63, x_64);
lean_inc(x_9);
x_66 = lean_apply_2(x_65, x_9, x_58);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
uint8_t x_69; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
lean_ctor_set(x_66, 0, x_55);
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_55);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_4);
x_75 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7;
x_76 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_46);
x_78 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_80 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_37);
x_82 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
x_84 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_84, 0, x_49);
x_85 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
x_87 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3;
x_88 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_86, x_87, x_85);
x_89 = lean_apply_2(x_88, x_9, x_73);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
lean_ctor_set(x_89, 0, x_55);
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_55);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_55);
x_94 = !lean_is_exclusive(x_89);
if (x_94 == 0)
{
return x_89;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_89, 0);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_89);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_55);
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_98 = !lean_is_exclusive(x_66);
if (x_98 == 0)
{
return x_66;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_66, 0);
x_100 = lean_ctor_get(x_66, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_66);
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
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_54, 1);
lean_inc(x_102);
lean_dec(x_54);
x_103 = lean_ctor_get(x_102, 4);
lean_inc(x_103);
x_104 = lean_ctor_get_uint8(x_103, sizeof(void*)*1);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_55);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_107 = l_Lean_Meta_tracer;
x_108 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4;
x_109 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_106, x_107, x_108);
lean_inc(x_9);
x_110 = lean_apply_2(x_109, x_9, x_102);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_114 = x_110;
} else {
 lean_dec_ref(x_110);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_55);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
lean_dec(x_110);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_4);
x_118 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7;
x_119 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_120, 0, x_46);
x_121 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_123 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_124, 0, x_37);
x_125 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_118);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_49);
x_128 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
x_130 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3;
x_131 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_129, x_130, x_128);
x_132 = lean_apply_2(x_131, x_9, x_116);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
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
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_55);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_55);
x_136 = lean_ctor_get(x_132, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_138 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_55);
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_140 = lean_ctor_get(x_110, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_110, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_142 = x_110;
} else {
 lean_dec_ref(x_110);
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
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_4);
x_144 = lean_ctor_get(x_54, 1);
lean_inc(x_144);
lean_dec(x_54);
x_145 = l_Lean_Meta_assignExprMVar(x_21, x_37, x_9, x_144);
lean_dec(x_9);
if (lean_obj_tag(x_145) == 0)
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_145);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_145, 0);
lean_dec(x_147);
lean_ctor_set(x_145, 0, x_55);
return x_145;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_55);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
else
{
uint8_t x_150; 
lean_dec(x_55);
x_150 = !lean_is_exclusive(x_145);
if (x_150 == 0)
{
return x_145;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_145, 0);
x_152 = lean_ctor_get(x_145, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_145);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_4);
x_154 = !lean_is_exclusive(x_54);
if (x_154 == 0)
{
return x_54;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_54, 0);
x_156 = lean_ctor_get(x_54, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_54);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_158 = lean_ctor_get(x_13, 0);
x_159 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 1);
x_160 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 2);
x_161 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 3);
lean_inc(x_158);
lean_dec(x_13);
x_162 = 1;
x_163 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_163, 0, x_158);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_19);
lean_ctor_set_uint8(x_163, sizeof(void*)*1 + 1, x_159);
lean_ctor_set_uint8(x_163, sizeof(void*)*1 + 2, x_160);
lean_ctor_set_uint8(x_163, sizeof(void*)*1 + 3, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*1 + 4, x_162);
x_164 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_14);
lean_ctor_set(x_164, 2, x_15);
lean_inc(x_49);
lean_inc(x_46);
x_165 = lean_apply_4(x_2, x_46, x_49, x_164, x_50);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_unbox(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
lean_dec(x_21);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_169 = x_165;
} else {
 lean_dec_ref(x_165);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_168, 4);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_170, sizeof(void*)*1);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_166);
lean_ctor_set(x_172, 1, x_168);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_169);
x_173 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_174 = l_Lean_Meta_tracer;
x_175 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4;
x_176 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_173, x_174, x_175);
lean_inc(x_9);
x_177 = lean_apply_2(x_176, x_9, x_168);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_unbox(x_178);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_181 = x_177;
} else {
 lean_dec_ref(x_177);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_166);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_183 = lean_ctor_get(x_177, 1);
lean_inc(x_183);
lean_dec(x_177);
x_184 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_184, 0, x_4);
x_185 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7;
x_186 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_187, 0, x_46);
x_188 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_190 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_191, 0, x_37);
x_192 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_185);
x_194 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_194, 0, x_49);
x_195 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
x_197 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3;
x_198 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_196, x_197, x_195);
x_199 = lean_apply_2(x_198, x_9, x_183);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_201 = x_199;
} else {
 lean_dec_ref(x_199);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_166);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_166);
x_203 = lean_ctor_get(x_199, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_199, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_205 = x_199;
} else {
 lean_dec_ref(x_199);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_166);
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_207 = lean_ctor_get(x_177, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_177, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_209 = x_177;
} else {
 lean_dec_ref(x_177);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_4);
x_211 = lean_ctor_get(x_165, 1);
lean_inc(x_211);
lean_dec(x_165);
x_212 = l_Lean_Meta_assignExprMVar(x_21, x_37, x_9, x_211);
lean_dec(x_9);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
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
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_166);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_166);
x_216 = lean_ctor_get(x_212, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_212, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_218 = x_212;
} else {
 lean_dec_ref(x_212);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_4);
x_220 = lean_ctor_get(x_165, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_165, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_222 = x_165;
} else {
 lean_dec_ref(x_165);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
}
else
{
uint8_t x_224; 
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_224 = !lean_is_exclusive(x_48);
if (x_224 == 0)
{
return x_48;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_48, 0);
x_226 = lean_ctor_get(x_48, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_48);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_228 = !lean_is_exclusive(x_45);
if (x_228 == 0)
{
return x_45;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_45, 0);
x_230 = lean_ctor_get(x_45, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_45);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; 
lean_inc(x_9);
lean_inc(x_37);
lean_inc(x_2);
lean_inc(x_1);
x_232 = l_Lean_Meta_isTypeCorrectAux(x_1, x_2, x_37, x_9, x_38);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_unbox(x_233);
lean_dec(x_233);
if (x_234 == 0)
{
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_19 == 0)
{
uint8_t x_235; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_235 = !lean_is_exclusive(x_232);
if (x_235 == 0)
{
lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_232, 0);
lean_dec(x_236);
x_237 = 0;
x_238 = lean_box(x_237);
lean_ctor_set(x_232, 0, x_238);
return x_232;
}
else
{
lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_232, 1);
lean_inc(x_239);
lean_dec(x_232);
x_240 = 0;
x_241 = lean_box(x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_239);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_232, 1);
lean_inc(x_243);
lean_dec(x_232);
x_244 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_8, x_17, x_9, x_243);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_3);
x_245 = lean_ctor_get(x_232, 1);
lean_inc(x_245);
lean_dec(x_232);
x_246 = lean_alloc_closure((void*)(l_Lean_Meta_usingDefault), 4, 1);
lean_closure_set(x_246, 0, x_1);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_246);
x_247 = l_Lean_Meta_inferTypeAuxAux___main(x_246, x_4, x_9, x_245);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
lean_inc(x_9);
lean_inc(x_37);
x_250 = l_Lean_Meta_inferTypeAuxAux___main(x_246, x_37, x_9, x_249);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = !lean_is_exclusive(x_13);
if (x_253 == 0)
{
uint8_t x_254; lean_object* x_255; lean_object* x_256; 
x_254 = 1;
lean_ctor_set_uint8(x_13, sizeof(void*)*1 + 4, x_254);
x_255 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_255, 0, x_13);
lean_ctor_set(x_255, 1, x_14);
lean_ctor_set(x_255, 2, x_15);
lean_inc(x_251);
lean_inc(x_248);
x_256 = lean_apply_4(x_2, x_248, x_251, x_255, x_252);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; uint8_t x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_unbox(x_257);
if (x_258 == 0)
{
uint8_t x_259; 
lean_dec(x_21);
x_259 = !lean_is_exclusive(x_256);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_260 = lean_ctor_get(x_256, 1);
x_261 = lean_ctor_get(x_256, 0);
lean_dec(x_261);
x_262 = lean_ctor_get(x_260, 4);
lean_inc(x_262);
x_263 = lean_ctor_get_uint8(x_262, sizeof(void*)*1);
lean_dec(x_262);
if (x_263 == 0)
{
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
return x_256;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_free_object(x_256);
x_264 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_265 = l_Lean_Meta_tracer;
x_266 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4;
x_267 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_264, x_265, x_266);
lean_inc(x_9);
x_268 = lean_apply_2(x_267, x_9, x_260);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; uint8_t x_270; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_unbox(x_269);
lean_dec(x_269);
if (x_270 == 0)
{
uint8_t x_271; 
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_271 = !lean_is_exclusive(x_268);
if (x_271 == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_268, 0);
lean_dec(x_272);
lean_ctor_set(x_268, 0, x_257);
return x_268;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_268, 1);
lean_inc(x_273);
lean_dec(x_268);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_257);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_275 = lean_ctor_get(x_268, 1);
lean_inc(x_275);
lean_dec(x_268);
x_276 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_276, 0, x_4);
x_277 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7;
x_278 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_279, 0, x_248);
x_280 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_282 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_283, 0, x_37);
x_284 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_277);
x_286 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_286, 0, x_251);
x_287 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_288 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
x_289 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3;
x_290 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_288, x_289, x_287);
x_291 = lean_apply_2(x_290, x_9, x_275);
if (lean_obj_tag(x_291) == 0)
{
uint8_t x_292; 
x_292 = !lean_is_exclusive(x_291);
if (x_292 == 0)
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_291, 0);
lean_dec(x_293);
lean_ctor_set(x_291, 0, x_257);
return x_291;
}
else
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
lean_dec(x_291);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_257);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
else
{
uint8_t x_296; 
lean_dec(x_257);
x_296 = !lean_is_exclusive(x_291);
if (x_296 == 0)
{
return x_291;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_291, 0);
x_298 = lean_ctor_get(x_291, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_291);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_257);
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_300 = !lean_is_exclusive(x_268);
if (x_300 == 0)
{
return x_268;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_268, 0);
x_302 = lean_ctor_get(x_268, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_268);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_256, 1);
lean_inc(x_304);
lean_dec(x_256);
x_305 = lean_ctor_get(x_304, 4);
lean_inc(x_305);
x_306 = lean_ctor_get_uint8(x_305, sizeof(void*)*1);
lean_dec(x_305);
if (x_306 == 0)
{
lean_object* x_307; 
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_257);
lean_ctor_set(x_307, 1, x_304);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_308 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_309 = l_Lean_Meta_tracer;
x_310 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4;
x_311 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_308, x_309, x_310);
lean_inc(x_9);
x_312 = lean_apply_2(x_311, x_9, x_304);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; uint8_t x_314; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_unbox(x_313);
lean_dec(x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_315 = lean_ctor_get(x_312, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_316 = x_312;
} else {
 lean_dec_ref(x_312);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_257);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_318 = lean_ctor_get(x_312, 1);
lean_inc(x_318);
lean_dec(x_312);
x_319 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_319, 0, x_4);
x_320 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7;
x_321 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_322, 0, x_248);
x_323 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
x_324 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_325 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_326, 0, x_37);
x_327 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_320);
x_329 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_329, 0, x_251);
x_330 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
x_331 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
x_332 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3;
x_333 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_331, x_332, x_330);
x_334 = lean_apply_2(x_333, x_9, x_318);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_334, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_336 = x_334;
} else {
 lean_dec_ref(x_334);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_257);
lean_ctor_set(x_337, 1, x_335);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_257);
x_338 = lean_ctor_get(x_334, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_334, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_340 = x_334;
} else {
 lean_dec_ref(x_334);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_257);
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_342 = lean_ctor_get(x_312, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_312, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_344 = x_312;
} else {
 lean_dec_ref(x_312);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(1, 2, 0);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_343);
return x_345;
}
}
}
}
else
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_4);
x_346 = lean_ctor_get(x_256, 1);
lean_inc(x_346);
lean_dec(x_256);
x_347 = l_Lean_Meta_assignExprMVar(x_21, x_37, x_9, x_346);
lean_dec(x_9);
if (lean_obj_tag(x_347) == 0)
{
uint8_t x_348; 
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_dec(x_349);
lean_ctor_set(x_347, 0, x_257);
return x_347;
}
else
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
lean_dec(x_347);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_257);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
else
{
uint8_t x_352; 
lean_dec(x_257);
x_352 = !lean_is_exclusive(x_347);
if (x_352 == 0)
{
return x_347;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_347, 0);
x_354 = lean_ctor_get(x_347, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_347);
x_355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
return x_355;
}
}
}
}
else
{
uint8_t x_356; 
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_4);
x_356 = !lean_is_exclusive(x_256);
if (x_356 == 0)
{
return x_256;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_256, 0);
x_358 = lean_ctor_get(x_256, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_256);
x_359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
return x_359;
}
}
}
else
{
lean_object* x_360; uint8_t x_361; uint8_t x_362; uint8_t x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_360 = lean_ctor_get(x_13, 0);
x_361 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 1);
x_362 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 2);
x_363 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 3);
lean_inc(x_360);
lean_dec(x_13);
x_364 = 1;
x_365 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_365, 0, x_360);
lean_ctor_set_uint8(x_365, sizeof(void*)*1, x_19);
lean_ctor_set_uint8(x_365, sizeof(void*)*1 + 1, x_361);
lean_ctor_set_uint8(x_365, sizeof(void*)*1 + 2, x_362);
lean_ctor_set_uint8(x_365, sizeof(void*)*1 + 3, x_363);
lean_ctor_set_uint8(x_365, sizeof(void*)*1 + 4, x_364);
x_366 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_14);
lean_ctor_set(x_366, 2, x_15);
lean_inc(x_251);
lean_inc(x_248);
x_367 = lean_apply_4(x_2, x_248, x_251, x_366, x_252);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; uint8_t x_369; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_unbox(x_368);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
lean_dec(x_21);
x_370 = lean_ctor_get(x_367, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_371 = x_367;
} else {
 lean_dec_ref(x_367);
 x_371 = lean_box(0);
}
x_372 = lean_ctor_get(x_370, 4);
lean_inc(x_372);
x_373 = lean_ctor_get_uint8(x_372, sizeof(void*)*1);
lean_dec(x_372);
if (x_373 == 0)
{
lean_object* x_374; 
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
if (lean_is_scalar(x_371)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_371;
}
lean_ctor_set(x_374, 0, x_368);
lean_ctor_set(x_374, 1, x_370);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_371);
x_375 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_376 = l_Lean_Meta_tracer;
x_377 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4;
x_378 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_375, x_376, x_377);
lean_inc(x_9);
x_379 = lean_apply_2(x_378, x_9, x_370);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; uint8_t x_381; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_unbox(x_380);
lean_dec(x_380);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_382 = lean_ctor_get(x_379, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_383 = x_379;
} else {
 lean_dec_ref(x_379);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_368);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_385 = lean_ctor_get(x_379, 1);
lean_inc(x_385);
lean_dec(x_379);
x_386 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_386, 0, x_4);
x_387 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7;
x_388 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
x_389 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_389, 0, x_248);
x_390 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
x_391 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_392 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
x_393 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_393, 0, x_37);
x_394 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_387);
x_396 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_396, 0, x_251);
x_397 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
x_398 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
x_399 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3;
x_400 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_398, x_399, x_397);
x_401 = lean_apply_2(x_400, x_9, x_385);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_403 = x_401;
} else {
 lean_dec_ref(x_401);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_368);
lean_ctor_set(x_404, 1, x_402);
return x_404;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_368);
x_405 = lean_ctor_get(x_401, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_401, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_407 = x_401;
} else {
 lean_dec_ref(x_401);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 2, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_406);
return x_408;
}
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_368);
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_409 = lean_ctor_get(x_379, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_379, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_411 = x_379;
} else {
 lean_dec_ref(x_379);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 2, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_410);
return x_412;
}
}
}
else
{
lean_object* x_413; lean_object* x_414; 
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_4);
x_413 = lean_ctor_get(x_367, 1);
lean_inc(x_413);
lean_dec(x_367);
x_414 = l_Lean_Meta_assignExprMVar(x_21, x_37, x_9, x_413);
lean_dec(x_9);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_416 = x_414;
} else {
 lean_dec_ref(x_414);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(0, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_368);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_368);
x_418 = lean_ctor_get(x_414, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_414, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_420 = x_414;
} else {
 lean_dec_ref(x_414);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_4);
x_422 = lean_ctor_get(x_367, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_367, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_424 = x_367;
} else {
 lean_dec_ref(x_367);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_248);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_426 = !lean_is_exclusive(x_250);
if (x_426 == 0)
{
return x_250;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_250, 0);
x_428 = lean_ctor_get(x_250, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_250);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
else
{
uint8_t x_430; 
lean_dec(x_246);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_430 = !lean_is_exclusive(x_247);
if (x_430 == 0)
{
return x_247;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_247, 0);
x_432 = lean_ctor_get(x_247, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_247);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
}
}
else
{
uint8_t x_434; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_434 = !lean_is_exclusive(x_36);
if (x_434 == 0)
{
return x_36;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_36, 0);
x_436 = lean_ctor_get(x_36, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_36);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
}
else
{
uint8_t x_438; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_438 = !lean_is_exclusive(x_22);
if (x_438 == 0)
{
return x_22;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_22, 0);
x_440 = lean_ctor_get(x_22, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_22);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
return x_441;
}
}
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_11);
x_450 = lean_ctor_get(x_9, 0);
lean_inc(x_450);
x_451 = lean_array_fget(x_8, x_7);
lean_inc(x_9);
x_452 = l___private_Init_Lean_Meta_ExprDefEq_13__simpAssignmentArg(x_451, x_9, x_10);
if (lean_obj_tag(x_452) == 0)
{
uint8_t x_453; 
x_453 = !lean_is_exclusive(x_452);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_452, 0);
x_455 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
x_456 = lean_array_fset(x_8, x_7, x_454);
if (lean_obj_tag(x_454) == 1)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; 
x_457 = lean_ctor_get(x_454, 0);
lean_inc(x_457);
x_458 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__2___boxed), 2, 1);
lean_closure_set(x_458, 0, x_454);
x_459 = lean_array_get_size(x_456);
x_460 = lean_nat_dec_le(x_7, x_459);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; 
x_461 = l_Id_Monad;
x_462 = lean_unsigned_to_nat(0u);
lean_inc(x_456);
x_463 = l_Array_anyRangeMAux___main___rarg(x_461, x_456, x_459, lean_box(0), x_458, x_462);
x_464 = lean_unbox(x_463);
lean_dec(x_463);
if (x_464 == 0)
{
lean_object* x_465; uint8_t x_466; 
x_465 = lean_ctor_get(x_5, 1);
lean_inc(x_465);
x_466 = l_Lean_LocalContext_contains(x_465, x_457);
lean_dec(x_457);
lean_dec(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; 
lean_free_object(x_452);
lean_dec(x_450);
x_467 = lean_unsigned_to_nat(1u);
x_468 = lean_nat_add(x_7, x_467);
lean_dec(x_7);
x_7 = x_468;
x_8 = x_456;
x_10 = x_455;
goto _start;
}
else
{
uint8_t x_470; 
x_470 = lean_ctor_get_uint8(x_450, sizeof(void*)*1 + 2);
if (x_470 == 0)
{
uint8_t x_471; 
lean_dec(x_7);
lean_dec(x_5);
x_471 = lean_ctor_get_uint8(x_450, sizeof(void*)*1);
lean_dec(x_450);
if (x_471 == 0)
{
uint8_t x_472; lean_object* x_473; 
lean_dec(x_456);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_472 = 0;
x_473 = lean_box(x_472);
lean_ctor_set(x_452, 0, x_473);
return x_452;
}
else
{
lean_object* x_474; 
lean_free_object(x_452);
x_474 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_456, x_6, x_9, x_455);
return x_474;
}
}
else
{
lean_object* x_475; lean_object* x_476; 
lean_free_object(x_452);
lean_dec(x_450);
x_475 = lean_unsigned_to_nat(1u);
x_476 = lean_nat_add(x_7, x_475);
lean_dec(x_7);
x_7 = x_476;
x_8 = x_456;
x_10 = x_455;
goto _start;
}
}
}
else
{
uint8_t x_478; 
lean_dec(x_457);
lean_dec(x_7);
lean_dec(x_5);
x_478 = lean_ctor_get_uint8(x_450, sizeof(void*)*1);
lean_dec(x_450);
if (x_478 == 0)
{
uint8_t x_479; lean_object* x_480; 
lean_dec(x_456);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_479 = 0;
x_480 = lean_box(x_479);
lean_ctor_set(x_452, 0, x_480);
return x_452;
}
else
{
lean_object* x_481; 
lean_free_object(x_452);
x_481 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_456, x_6, x_9, x_455);
return x_481;
}
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; 
lean_dec(x_459);
x_482 = l_Id_Monad;
x_483 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_456);
x_484 = l_Array_anyRangeMAux___main___rarg(x_482, x_456, x_7, lean_box(0), x_458, x_483);
x_485 = lean_unbox(x_484);
lean_dec(x_484);
if (x_485 == 0)
{
lean_object* x_486; uint8_t x_487; 
x_486 = lean_ctor_get(x_5, 1);
lean_inc(x_486);
x_487 = l_Lean_LocalContext_contains(x_486, x_457);
lean_dec(x_457);
lean_dec(x_486);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; 
lean_free_object(x_452);
lean_dec(x_450);
x_488 = lean_unsigned_to_nat(1u);
x_489 = lean_nat_add(x_7, x_488);
lean_dec(x_7);
x_7 = x_489;
x_8 = x_456;
x_10 = x_455;
goto _start;
}
else
{
uint8_t x_491; 
x_491 = lean_ctor_get_uint8(x_450, sizeof(void*)*1 + 2);
if (x_491 == 0)
{
uint8_t x_492; 
lean_dec(x_7);
lean_dec(x_5);
x_492 = lean_ctor_get_uint8(x_450, sizeof(void*)*1);
lean_dec(x_450);
if (x_492 == 0)
{
uint8_t x_493; lean_object* x_494; 
lean_dec(x_456);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_493 = 0;
x_494 = lean_box(x_493);
lean_ctor_set(x_452, 0, x_494);
return x_452;
}
else
{
lean_object* x_495; 
lean_free_object(x_452);
x_495 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_456, x_6, x_9, x_455);
return x_495;
}
}
else
{
lean_object* x_496; lean_object* x_497; 
lean_free_object(x_452);
lean_dec(x_450);
x_496 = lean_unsigned_to_nat(1u);
x_497 = lean_nat_add(x_7, x_496);
lean_dec(x_7);
x_7 = x_497;
x_8 = x_456;
x_10 = x_455;
goto _start;
}
}
}
else
{
uint8_t x_499; 
lean_dec(x_457);
lean_dec(x_7);
lean_dec(x_5);
x_499 = lean_ctor_get_uint8(x_450, sizeof(void*)*1);
lean_dec(x_450);
if (x_499 == 0)
{
uint8_t x_500; lean_object* x_501; 
lean_dec(x_456);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_500 = 0;
x_501 = lean_box(x_500);
lean_ctor_set(x_452, 0, x_501);
return x_452;
}
else
{
lean_object* x_502; 
lean_free_object(x_452);
x_502 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_456, x_6, x_9, x_455);
return x_502;
}
}
}
}
else
{
uint8_t x_503; 
lean_dec(x_454);
lean_dec(x_7);
lean_dec(x_5);
x_503 = lean_ctor_get_uint8(x_450, sizeof(void*)*1);
lean_dec(x_450);
if (x_503 == 0)
{
uint8_t x_504; lean_object* x_505; 
lean_dec(x_456);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_504 = 0;
x_505 = lean_box(x_504);
lean_ctor_set(x_452, 0, x_505);
return x_452;
}
else
{
lean_object* x_506; 
lean_free_object(x_452);
x_506 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_456, x_6, x_9, x_455);
return x_506;
}
}
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_452, 0);
x_508 = lean_ctor_get(x_452, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_452);
lean_inc(x_507);
x_509 = lean_array_fset(x_8, x_7, x_507);
if (lean_obj_tag(x_507) == 1)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; 
x_510 = lean_ctor_get(x_507, 0);
lean_inc(x_510);
x_511 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__2___boxed), 2, 1);
lean_closure_set(x_511, 0, x_507);
x_512 = lean_array_get_size(x_509);
x_513 = lean_nat_dec_le(x_7, x_512);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; 
x_514 = l_Id_Monad;
x_515 = lean_unsigned_to_nat(0u);
lean_inc(x_509);
x_516 = l_Array_anyRangeMAux___main___rarg(x_514, x_509, x_512, lean_box(0), x_511, x_515);
x_517 = lean_unbox(x_516);
lean_dec(x_516);
if (x_517 == 0)
{
lean_object* x_518; uint8_t x_519; 
x_518 = lean_ctor_get(x_5, 1);
lean_inc(x_518);
x_519 = l_Lean_LocalContext_contains(x_518, x_510);
lean_dec(x_510);
lean_dec(x_518);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; 
lean_dec(x_450);
x_520 = lean_unsigned_to_nat(1u);
x_521 = lean_nat_add(x_7, x_520);
lean_dec(x_7);
x_7 = x_521;
x_8 = x_509;
x_10 = x_508;
goto _start;
}
else
{
uint8_t x_523; 
x_523 = lean_ctor_get_uint8(x_450, sizeof(void*)*1 + 2);
if (x_523 == 0)
{
uint8_t x_524; 
lean_dec(x_7);
lean_dec(x_5);
x_524 = lean_ctor_get_uint8(x_450, sizeof(void*)*1);
lean_dec(x_450);
if (x_524 == 0)
{
uint8_t x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_509);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_525 = 0;
x_526 = lean_box(x_525);
x_527 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_508);
return x_527;
}
else
{
lean_object* x_528; 
x_528 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_509, x_6, x_9, x_508);
return x_528;
}
}
else
{
lean_object* x_529; lean_object* x_530; 
lean_dec(x_450);
x_529 = lean_unsigned_to_nat(1u);
x_530 = lean_nat_add(x_7, x_529);
lean_dec(x_7);
x_7 = x_530;
x_8 = x_509;
x_10 = x_508;
goto _start;
}
}
}
else
{
uint8_t x_532; 
lean_dec(x_510);
lean_dec(x_7);
lean_dec(x_5);
x_532 = lean_ctor_get_uint8(x_450, sizeof(void*)*1);
lean_dec(x_450);
if (x_532 == 0)
{
uint8_t x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_509);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_533 = 0;
x_534 = lean_box(x_533);
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_508);
return x_535;
}
else
{
lean_object* x_536; 
x_536 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_509, x_6, x_9, x_508);
return x_536;
}
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; 
lean_dec(x_512);
x_537 = l_Id_Monad;
x_538 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_509);
x_539 = l_Array_anyRangeMAux___main___rarg(x_537, x_509, x_7, lean_box(0), x_511, x_538);
x_540 = lean_unbox(x_539);
lean_dec(x_539);
if (x_540 == 0)
{
lean_object* x_541; uint8_t x_542; 
x_541 = lean_ctor_get(x_5, 1);
lean_inc(x_541);
x_542 = l_Lean_LocalContext_contains(x_541, x_510);
lean_dec(x_510);
lean_dec(x_541);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; 
lean_dec(x_450);
x_543 = lean_unsigned_to_nat(1u);
x_544 = lean_nat_add(x_7, x_543);
lean_dec(x_7);
x_7 = x_544;
x_8 = x_509;
x_10 = x_508;
goto _start;
}
else
{
uint8_t x_546; 
x_546 = lean_ctor_get_uint8(x_450, sizeof(void*)*1 + 2);
if (x_546 == 0)
{
uint8_t x_547; 
lean_dec(x_7);
lean_dec(x_5);
x_547 = lean_ctor_get_uint8(x_450, sizeof(void*)*1);
lean_dec(x_450);
if (x_547 == 0)
{
uint8_t x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_509);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_548 = 0;
x_549 = lean_box(x_548);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_508);
return x_550;
}
else
{
lean_object* x_551; 
x_551 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_509, x_6, x_9, x_508);
return x_551;
}
}
else
{
lean_object* x_552; lean_object* x_553; 
lean_dec(x_450);
x_552 = lean_unsigned_to_nat(1u);
x_553 = lean_nat_add(x_7, x_552);
lean_dec(x_7);
x_7 = x_553;
x_8 = x_509;
x_10 = x_508;
goto _start;
}
}
}
else
{
uint8_t x_555; 
lean_dec(x_510);
lean_dec(x_7);
lean_dec(x_5);
x_555 = lean_ctor_get_uint8(x_450, sizeof(void*)*1);
lean_dec(x_450);
if (x_555 == 0)
{
uint8_t x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_509);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_556 = 0;
x_557 = lean_box(x_556);
x_558 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_508);
return x_558;
}
else
{
lean_object* x_559; 
x_559 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_509, x_6, x_9, x_508);
return x_559;
}
}
}
}
else
{
uint8_t x_560; 
lean_dec(x_507);
lean_dec(x_7);
lean_dec(x_5);
x_560 = lean_ctor_get_uint8(x_450, sizeof(void*)*1);
lean_dec(x_450);
if (x_560 == 0)
{
uint8_t x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_509);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_561 = 0;
x_562 = lean_box(x_561);
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_508);
return x_563;
}
else
{
lean_object* x_564; 
x_564 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_509, x_6, x_9, x_508);
return x_564;
}
}
}
}
else
{
uint8_t x_565; 
lean_dec(x_450);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_565 = !lean_is_exclusive(x_452);
if (x_565 == 0)
{
return x_452;
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_566 = lean_ctor_get(x_452, 0);
x_567 = lean_ctor_get(x_452, 1);
lean_inc(x_567);
lean_inc(x_566);
lean_dec(x_452);
x_568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_568, 0, x_566);
lean_ctor_set(x_568, 1, x_567);
return x_568;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_15__processAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_mvarId_x21(x_4);
x_10 = l_Lean_Meta_getMVarDecl(x_9, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main(x_1, x_2, x_3, x_4, x_11, x_6, x_13, x_5, x_7, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l___private_Init_Lean_Meta_ExprDefEq_16__unfold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_16__unfold(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_16__unfold___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__isDeltaCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = 1;
x_7 = l_Lean_Meta_getConstAux(x_5, x_6, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__isDeltaCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_ExprDefEq_17__isDeltaCandidate(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
uint8_t l___private_Init_Lean_Meta_ExprDefEq_18__sameHeadSymbol(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_4) == 4)
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = 0;
return x_7;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_18__sameHeadSymbol___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Meta_ExprDefEq_18__sameHeadSymbol(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_3 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_box(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Expr_constLevels_x21(x_1);
x_9 = l_Lean_Expr_constLevels_x21(x_2);
x_10 = l_Lean_Meta_isListLevelDefEq___main(x_8, x_9, x_4, x_5);
return x_10;
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unfoldRight");
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_apply_4(x_1, x_2, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = l_Bool_toLBool(x_15);
x_17 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_unbox(x_18);
lean_dec(x_18);
x_21 = l_Bool_toLBool(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = l_Lean_ConstantInfo_name(x_3);
x_29 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___closed__1;
x_30 = lean_name_mk_string(x_4, x_29);
x_31 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_inc(x_30);
x_32 = l_Lean_Name_append___main(x_31, x_30);
x_33 = l_Lean_Meta_tracer;
x_34 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_5, x_33, x_32);
lean_inc(x_8);
x_35 = lean_apply_2(x_34, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_6);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_apply_4(x_1, x_2, x_7, x_8, x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
x_43 = l_Bool_toLBool(x_42);
x_44 = lean_box(x_43);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = lean_unbox(x_45);
lean_dec(x_45);
x_48 = l_Bool_toLBool(x_47);
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_39);
if (x_51 == 0)
{
return x_39;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_35, 1);
lean_inc(x_55);
lean_dec(x_35);
x_56 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_56, 0, x_28);
x_57 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_6, x_30, x_56);
lean_inc(x_8);
x_58 = lean_apply_2(x_57, x_8, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_apply_4(x_1, x_2, x_7, x_8, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
x_64 = l_Bool_toLBool(x_63);
x_65 = lean_box(x_64);
lean_ctor_set(x_60, 0, x_65);
return x_60;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_60, 0);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_60);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_69 = l_Bool_toLBool(x_68);
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_60);
if (x_72 == 0)
{
return x_60;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_60, 0);
x_74 = lean_ctor_get(x_60, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_60);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_58);
if (x_76 == 0)
{
return x_58;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_58, 0);
x_78 = lean_ctor_get(x_58, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_58);
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
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_35);
if (x_80 == 0)
{
return x_35;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_35, 0);
x_82 = lean_ctor_get(x_35, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_35);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unfoldLeft");
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_apply_4(x_1, x_7, x_2, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = l_Bool_toLBool(x_15);
x_17 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_unbox(x_18);
lean_dec(x_18);
x_21 = l_Bool_toLBool(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = l_Lean_ConstantInfo_name(x_3);
x_29 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___closed__1;
x_30 = lean_name_mk_string(x_4, x_29);
x_31 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_inc(x_30);
x_32 = l_Lean_Name_append___main(x_31, x_30);
x_33 = l_Lean_Meta_tracer;
x_34 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_5, x_33, x_32);
lean_inc(x_8);
x_35 = lean_apply_2(x_34, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_6);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_apply_4(x_1, x_7, x_2, x_8, x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
x_43 = l_Bool_toLBool(x_42);
x_44 = lean_box(x_43);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = lean_unbox(x_45);
lean_dec(x_45);
x_48 = l_Bool_toLBool(x_47);
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_39);
if (x_51 == 0)
{
return x_39;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_35, 1);
lean_inc(x_55);
lean_dec(x_35);
x_56 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_56, 0, x_28);
x_57 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_6, x_30, x_56);
lean_inc(x_8);
x_58 = lean_apply_2(x_57, x_8, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_apply_4(x_1, x_7, x_2, x_8, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
x_64 = l_Bool_toLBool(x_63);
x_65 = lean_box(x_64);
lean_ctor_set(x_60, 0, x_65);
return x_60;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_60, 0);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_60);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_69 = l_Bool_toLBool(x_68);
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_60);
if (x_72 == 0)
{
return x_60;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_60, 0);
x_74 = lean_ctor_get(x_60, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_60);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_58);
if (x_76 == 0)
{
return x_58;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_58, 0);
x_78 = lean_ctor_get(x_58, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_58);
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
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_35);
if (x_80 == 0)
{
return x_35;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_35, 0);
x_82 = lean_ctor_get(x_35, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_35);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_11 = l_Lean_Name_append___main(x_10, x_1);
x_12 = l_Lean_Meta_tracer;
x_13 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_2, x_12, x_11);
x_14 = lean_apply_2(x_13, x_4, x_5);
return x_14;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_4 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_2, x_3, x_9);
x_11 = lean_apply_2(x_10, x_5, x_6);
return x_11;
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_4(x_1, x_2, x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = l_Bool_toLBool(x_10);
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_unbox(x_13);
lean_dec(x_13);
x_16 = l_Bool_toLBool(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unfoldLeftRight");
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_apply_4(x_1, x_2, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = l_Bool_toLBool(x_15);
x_17 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_unbox(x_18);
lean_dec(x_18);
x_21 = l_Bool_toLBool(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__7___closed__1;
x_29 = lean_name_mk_string(x_3, x_28);
x_30 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_inc(x_29);
x_31 = l_Lean_Name_append___main(x_30, x_29);
x_32 = l_Lean_Meta_tracer;
x_33 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_4, x_32, x_31);
lean_inc(x_8);
x_34 = lean_apply_2(x_33, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_apply_4(x_1, x_2, x_7, x_8, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
x_42 = l_Bool_toLBool(x_41);
x_43 = lean_box(x_42);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_47 = l_Bool_toLBool(x_46);
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_38);
if (x_50 == 0)
{
return x_38;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_38);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_dec(x_34);
x_55 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_55, 0, x_5);
x_56 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_6, x_29, x_55);
lean_inc(x_8);
x_57 = lean_apply_2(x_56, x_8, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_apply_4(x_1, x_2, x_7, x_8, x_58);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
x_63 = l_Bool_toLBool(x_62);
x_64 = lean_box(x_63);
lean_ctor_set(x_59, 0, x_64);
return x_59;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_59, 0);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_59);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_68 = l_Bool_toLBool(x_67);
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_59);
if (x_71 == 0)
{
return x_59;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_59, 0);
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_59);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_57);
if (x_75 == 0)
{
return x_57;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_57, 0);
x_77 = lean_ctor_get(x_57, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_57);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_34);
if (x_79 == 0)
{
return x_34;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_34, 0);
x_81 = lean_ctor_get(x_34, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_34);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = l_Lean_ConstantInfo_name(x_1);
x_15 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___closed__1;
lean_inc(x_2);
x_16 = lean_name_mk_string(x_2, x_15);
lean_inc(x_3);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__4___boxed), 5, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_3);
x_18 = l_Lean_Meta_tracer___closed__3;
lean_inc(x_4);
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, lean_box(0));
lean_closure_set(x_19, 2, lean_box(0));
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_17);
lean_inc(x_5);
lean_inc(x_14);
x_20 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__5___boxed), 6, 3);
lean_closure_set(x_20, 0, x_14);
lean_closure_set(x_20, 1, x_5);
lean_closure_set(x_20, 2, x_16);
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, lean_box(0));
lean_closure_set(x_21, 2, lean_box(0));
lean_closure_set(x_21, 3, x_19);
lean_closure_set(x_21, 4, x_20);
lean_inc(x_7);
lean_inc(x_11);
lean_inc(x_6);
x_22 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__6___boxed), 6, 3);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_11);
lean_closure_set(x_22, 2, x_7);
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, lean_box(0));
lean_closure_set(x_23, 2, lean_box(0));
lean_closure_set(x_23, 3, x_21);
lean_closure_set(x_23, 4, x_22);
lean_inc(x_6);
x_24 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__7), 9, 6);
lean_closure_set(x_24, 0, x_6);
lean_closure_set(x_24, 1, x_11);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_14);
lean_closure_set(x_24, 5, x_5);
x_25 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_8, x_9, x_6, x_10, x_7, x_23, x_24, x_12, x_13);
return x_25;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_apply_4(x_1, x_2, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = l_Bool_toLBool(x_15);
x_17 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_unbox(x_18);
lean_dec(x_18);
x_21 = l_Bool_toLBool(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___closed__1;
x_29 = lean_name_mk_string(x_3, x_28);
x_30 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_inc(x_29);
x_31 = l_Lean_Name_append___main(x_30, x_29);
x_32 = l_Lean_Meta_tracer;
x_33 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_4, x_32, x_31);
lean_inc(x_8);
x_34 = lean_apply_2(x_33, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_apply_4(x_1, x_2, x_7, x_8, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
x_42 = l_Bool_toLBool(x_41);
x_43 = lean_box(x_42);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_47 = l_Bool_toLBool(x_46);
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_38);
if (x_50 == 0)
{
return x_38;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_38);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_dec(x_34);
x_55 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_55, 0, x_5);
x_56 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_6, x_29, x_55);
lean_inc(x_8);
x_57 = lean_apply_2(x_56, x_8, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_apply_4(x_1, x_2, x_7, x_8, x_58);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
x_63 = l_Bool_toLBool(x_62);
x_64 = lean_box(x_63);
lean_ctor_set(x_59, 0, x_64);
return x_59;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_59, 0);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_59);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_68 = l_Bool_toLBool(x_67);
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_59);
if (x_71 == 0)
{
return x_59;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_59, 0);
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_59);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_57);
if (x_75 == 0)
{
return x_57;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_57, 0);
x_77 = lean_ctor_get(x_57, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_57);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_34);
if (x_79 == 0)
{
return x_34;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_34, 0);
x_81 = lean_ctor_get(x_34, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_34);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l___private_Init_Lean_Meta_ExprDefEq_18__sameHeadSymbol(x_1, x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 4);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_apply_4(x_2, x_3, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_19 = l_Bool_toLBool(x_18);
x_20 = lean_box(x_19);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_unbox(x_21);
lean_dec(x_21);
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
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__7___closed__1;
x_32 = lean_name_mk_string(x_4, x_31);
x_33 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_inc(x_32);
x_34 = l_Lean_Name_append___main(x_33, x_32);
x_35 = l_Lean_Meta_tracer;
x_36 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_5, x_35, x_34);
lean_inc(x_10);
x_37 = lean_apply_2(x_36, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_apply_4(x_2, x_3, x_9, x_10, x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
x_45 = l_Bool_toLBool(x_44);
x_46 = lean_box(x_45);
lean_ctor_set(x_41, 0, x_46);
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
x_50 = l_Bool_toLBool(x_49);
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_41);
if (x_53 == 0)
{
return x_41;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_41, 0);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_41);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_37, 1);
lean_inc(x_57);
lean_dec(x_37);
x_58 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_58, 0, x_6);
x_59 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_7, x_32, x_58);
lean_inc(x_10);
x_60 = lean_apply_2(x_59, x_10, x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_apply_4(x_2, x_3, x_9, x_10, x_61);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
x_66 = l_Bool_toLBool(x_65);
x_67 = lean_box(x_66);
lean_ctor_set(x_62, 0, x_67);
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = lean_unbox(x_68);
lean_dec(x_68);
x_71 = l_Bool_toLBool(x_70);
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
return x_73;
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_62);
if (x_74 == 0)
{
return x_62;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_62, 0);
x_76 = lean_ctor_get(x_62, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_62);
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
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_60);
if (x_78 == 0)
{
return x_60;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_60, 0);
x_80 = lean_ctor_get(x_60, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_60);
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
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_37);
if (x_82 == 0)
{
return x_37;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_37, 0);
x_84 = lean_ctor_get(x_37, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_37);
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
lean_object* x_86; uint8_t x_87; 
lean_dec(x_6);
lean_dec(x_3);
x_86 = lean_ctor_get(x_11, 4);
lean_inc(x_86);
x_87 = lean_ctor_get_uint8(x_86, sizeof(void*)*1);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_88 = lean_apply_4(x_2, x_1, x_9, x_10, x_11);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; uint8_t x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
x_92 = l_Bool_toLBool(x_91);
x_93 = lean_box(x_92);
lean_ctor_set(x_88, 0, x_93);
return x_88;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_88, 0);
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_88);
x_96 = lean_unbox(x_94);
lean_dec(x_94);
x_97 = l_Bool_toLBool(x_96);
x_98 = lean_box(x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_95);
return x_99;
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_88);
if (x_100 == 0)
{
return x_88;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_88, 0);
x_102 = lean_ctor_get(x_88, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_88);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___closed__1;
x_105 = lean_name_mk_string(x_4, x_104);
x_106 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_inc(x_105);
x_107 = l_Lean_Name_append___main(x_106, x_105);
x_108 = l_Lean_Meta_tracer;
x_109 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_5, x_108, x_107);
lean_inc(x_10);
x_110 = lean_apply_2(x_109, x_10, x_11);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_apply_4(x_2, x_1, x_9, x_10, x_113);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; uint8_t x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
x_118 = l_Bool_toLBool(x_117);
x_119 = lean_box(x_118);
lean_ctor_set(x_114, 0, x_119);
return x_114;
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_114, 0);
x_121 = lean_ctor_get(x_114, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_114);
x_122 = lean_unbox(x_120);
lean_dec(x_120);
x_123 = l_Bool_toLBool(x_122);
x_124 = lean_box(x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_121);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_114);
if (x_126 == 0)
{
return x_114;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_114, 0);
x_128 = lean_ctor_get(x_114, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_114);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_110, 1);
lean_inc(x_130);
lean_dec(x_110);
x_131 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_131, 0, x_8);
x_132 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_7, x_105, x_131);
lean_inc(x_10);
x_133 = lean_apply_2(x_132, x_10, x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_apply_4(x_2, x_1, x_9, x_10, x_134);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; uint8_t x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
x_139 = l_Bool_toLBool(x_138);
x_140 = lean_box(x_139);
lean_ctor_set(x_135, 0, x_140);
return x_135;
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_135, 0);
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_135);
x_143 = lean_unbox(x_141);
lean_dec(x_141);
x_144 = l_Bool_toLBool(x_143);
x_145 = lean_box(x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_142);
return x_146;
}
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_135);
if (x_147 == 0)
{
return x_135;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_135, 0);
x_149 = lean_ctor_get(x_135, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_135);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_133);
if (x_151 == 0)
{
return x_133;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_133, 0);
x_153 = lean_ctor_get(x_133, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_133);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_105);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_155 = !lean_is_exclusive(x_110);
if (x_155 == 0)
{
return x_110;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_110, 0);
x_157 = lean_ctor_get(x_110, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_110);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = l___private_Init_Lean_Meta_ExprDefEq_18__sameHeadSymbol(x_13, x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___closed__1;
lean_inc(x_2);
x_18 = lean_name_mk_string(x_2, x_17);
lean_inc(x_3);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__4___boxed), 5, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_3);
x_20 = l_Lean_Meta_tracer___closed__3;
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, lean_box(0));
lean_closure_set(x_21, 2, lean_box(0));
lean_closure_set(x_21, 3, x_20);
lean_closure_set(x_21, 4, x_19);
lean_inc(x_6);
lean_inc(x_5);
x_22 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__5___boxed), 6, 3);
lean_closure_set(x_22, 0, x_5);
lean_closure_set(x_22, 1, x_6);
lean_closure_set(x_22, 2, x_18);
lean_inc(x_4);
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, lean_box(0));
lean_closure_set(x_23, 2, lean_box(0));
lean_closure_set(x_23, 3, x_21);
lean_closure_set(x_23, 4, x_22);
lean_inc(x_1);
lean_inc(x_13);
lean_inc(x_7);
x_24 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__6___boxed), 6, 3);
lean_closure_set(x_24, 0, x_7);
lean_closure_set(x_24, 1, x_13);
lean_closure_set(x_24, 2, x_1);
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_25, 0, x_4);
lean_closure_set(x_25, 1, lean_box(0));
lean_closure_set(x_25, 2, lean_box(0));
lean_closure_set(x_25, 3, x_23);
lean_closure_set(x_25, 4, x_24);
lean_inc(x_7);
x_26 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__10), 11, 8);
lean_closure_set(x_26, 0, x_8);
lean_closure_set(x_26, 1, x_7);
lean_closure_set(x_26, 2, x_13);
lean_closure_set(x_26, 3, x_2);
lean_closure_set(x_26, 4, x_3);
lean_closure_set(x_26, 5, x_5);
lean_closure_set(x_26, 6, x_6);
lean_closure_set(x_26, 7, x_9);
x_27 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_10, x_11, x_7, x_12, x_1, x_25, x_26, x_14, x_15);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_28 = lean_ctor_get(x_15, 4);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_apply_4(x_7, x_13, x_1, x_14, x_15);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
x_34 = l_Bool_toLBool(x_33);
x_35 = lean_box(x_34);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_unbox(x_36);
lean_dec(x_36);
x_39 = l_Bool_toLBool(x_38);
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___closed__1;
x_47 = lean_name_mk_string(x_2, x_46);
x_48 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_inc(x_47);
x_49 = l_Lean_Name_append___main(x_48, x_47);
x_50 = l_Lean_Meta_tracer;
x_51 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_3, x_50, x_49);
lean_inc(x_14);
x_52 = lean_apply_2(x_51, x_14, x_15);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_47);
lean_dec(x_6);
lean_dec(x_5);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_apply_4(x_7, x_13, x_1, x_14, x_55);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
x_60 = l_Bool_toLBool(x_59);
x_61 = lean_box(x_60);
lean_ctor_set(x_56, 0, x_61);
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_64 = lean_unbox(x_62);
lean_dec(x_62);
x_65 = l_Bool_toLBool(x_64);
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_56);
if (x_68 == 0)
{
return x_56;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_56, 0);
x_70 = lean_ctor_get(x_56, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_56);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_52, 1);
lean_inc(x_72);
lean_dec(x_52);
x_73 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_73, 0, x_5);
x_74 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_6, x_47, x_73);
lean_inc(x_14);
x_75 = lean_apply_2(x_74, x_14, x_72);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_apply_4(x_7, x_13, x_1, x_14, x_76);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
x_81 = l_Bool_toLBool(x_80);
x_82 = lean_box(x_81);
lean_ctor_set(x_77, 0, x_82);
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_77, 0);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_77);
x_85 = lean_unbox(x_83);
lean_dec(x_83);
x_86 = l_Bool_toLBool(x_85);
x_87 = lean_box(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_77);
if (x_89 == 0)
{
return x_77;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_77, 0);
x_91 = lean_ctor_get(x_77, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_77);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_75);
if (x_93 == 0)
{
return x_75;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_75, 0);
x_95 = lean_ctor_get(x_75, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_75);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_47);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_52);
if (x_97 == 0)
{
return x_52;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_52, 0);
x_99 = lean_ctor_get(x_52, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_52);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_apply_4(x_1, x_7, x_2, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = l_Bool_toLBool(x_15);
x_17 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_unbox(x_18);
lean_dec(x_18);
x_21 = l_Bool_toLBool(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___closed__1;
x_29 = lean_name_mk_string(x_3, x_28);
x_30 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_inc(x_29);
x_31 = l_Lean_Name_append___main(x_30, x_29);
x_32 = l_Lean_Meta_tracer;
x_33 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_4, x_32, x_31);
lean_inc(x_8);
x_34 = lean_apply_2(x_33, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_apply_4(x_1, x_7, x_2, x_8, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
x_42 = l_Bool_toLBool(x_41);
x_43 = lean_box(x_42);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_47 = l_Bool_toLBool(x_46);
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_38);
if (x_50 == 0)
{
return x_38;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_38);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_dec(x_34);
x_55 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_55, 0, x_5);
x_56 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_6, x_29, x_55);
lean_inc(x_8);
x_57 = lean_apply_2(x_56, x_8, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_apply_4(x_1, x_7, x_2, x_8, x_58);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
x_63 = l_Bool_toLBool(x_62);
x_64 = lean_box(x_63);
lean_ctor_set(x_59, 0, x_64);
return x_59;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_59, 0);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_59);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_68 = l_Bool_toLBool(x_67);
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_59);
if (x_71 == 0)
{
return x_59;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_59, 0);
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_59);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_57);
if (x_75 == 0)
{
return x_57;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_57, 0);
x_77 = lean_ctor_get(x_57, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_57);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_34);
if (x_79 == 0)
{
return x_34;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_34, 0);
x_81 = lean_ctor_get(x_34, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_34);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delta");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__4;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_EIO_Monad___closed__1;
x_2 = 2;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_ReaderT_pure___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = l_Lean_Expr_getAppFn___main(x_4);
x_9 = l_Lean_Expr_getAppFn___main(x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Expr_getAppNumArgsAux___main(x_4, x_10);
x_12 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
lean_inc(x_4);
x_16 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_4, x_13, x_15);
x_17 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_10);
lean_inc(x_17);
x_18 = lean_mk_array(x_17, x_12);
x_19 = lean_nat_sub(x_17, x_14);
lean_dec(x_17);
lean_inc(x_5);
x_20 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_5, x_18, x_19);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs), 8, 6);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_8);
lean_closure_set(x_21, 4, x_16);
lean_closure_set(x_21, 5, x_20);
lean_inc(x_9);
lean_inc(x_8);
x_22 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__1___boxed), 5, 2);
lean_closure_set(x_22, 0, x_8);
lean_closure_set(x_22, 1, x_9);
x_23 = l_EIO_Monad___closed__1;
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, lean_box(0));
lean_closure_set(x_24, 2, lean_box(0));
lean_closure_set(x_24, 3, x_21);
lean_closure_set(x_24, 4, x_22);
x_25 = l___private_Init_Lean_Meta_ExprDefEq_17__isDeltaCandidate(x_8, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = l___private_Init_Lean_Meta_ExprDefEq_17__isDeltaCandidate(x_9, x_6, x_28);
lean_dec(x_9);
if (lean_obj_tag(x_29) == 0)
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_30; 
lean_free_object(x_25);
lean_dec(x_24);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = 2;
x_34 = lean_box(x_33);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = 2;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_dec(x_29);
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_42 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_43 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_2);
x_44 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___boxed), 9, 6);
lean_closure_set(x_44, 0, x_2);
lean_closure_set(x_44, 1, x_4);
lean_closure_set(x_44, 2, x_40);
lean_closure_set(x_44, 3, x_41);
lean_closure_set(x_44, 4, x_42);
lean_closure_set(x_44, 5, x_43);
lean_inc(x_1);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_45, 0, x_1);
x_46 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
x_47 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_45, x_2, x_3, x_5, x_46, x_44, x_6, x_39);
return x_47;
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_29, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_25);
lean_dec(x_24);
x_49 = lean_ctor_get(x_29, 1);
lean_inc(x_49);
lean_dec(x_29);
x_50 = lean_ctor_get(x_27, 0);
lean_inc(x_50);
lean_dec(x_27);
x_51 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_52 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_53 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_2);
x_54 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___boxed), 9, 6);
lean_closure_set(x_54, 0, x_2);
lean_closure_set(x_54, 1, x_5);
lean_closure_set(x_54, 2, x_50);
lean_closure_set(x_54, 3, x_51);
lean_closure_set(x_54, 4, x_52);
lean_closure_set(x_54, 5, x_53);
lean_inc(x_1);
x_55 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_55, 0, x_1);
x_56 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
x_57 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_55, x_2, x_3, x_4, x_56, x_54, x_6, x_49);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_77; lean_object* x_78; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_58 = lean_ctor_get(x_29, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_59 = x_29;
} else {
 lean_dec_ref(x_29);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_27, 0);
lean_inc(x_60);
lean_dec(x_27);
x_61 = lean_ctor_get(x_48, 0);
lean_inc(x_61);
lean_dec(x_48);
x_263 = l_Lean_ConstantInfo_name(x_60);
x_264 = l_Lean_ConstantInfo_name(x_61);
x_265 = lean_name_eq(x_263, x_264);
if (x_265 == 0)
{
lean_object* x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; lean_object* x_270; 
lean_dec(x_59);
lean_free_object(x_25);
lean_dec(x_24);
x_266 = lean_ctor_get(x_6, 0);
lean_inc(x_266);
x_267 = lean_ctor_get_uint8(x_266, sizeof(void*)*1 + 4);
lean_dec(x_266);
x_268 = 2;
x_269 = l_Lean_Meta_TransparencyMode_beq(x_267, x_268);
if (x_269 == 0)
{
lean_object* x_281; uint8_t x_282; lean_object* x_283; lean_object* x_295; lean_object* x_308; uint8_t x_348; lean_object* x_349; 
x_281 = lean_ctor_get(x_58, 0);
lean_inc(x_281);
lean_inc(x_263);
lean_inc(x_281);
x_282 = l_Lean_isReducible(x_281, x_263);
lean_inc(x_264);
x_348 = l_Lean_isReducible(x_281, x_264);
if (x_282 == 0)
{
lean_object* x_386; 
x_386 = lean_box(0);
x_349 = x_386;
goto block_385;
}
else
{
if (x_348 == 0)
{
uint8_t x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_387 = l_Lean_Expr_hasExprMVar(x_4);
x_388 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_389 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_390 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_263);
lean_inc(x_5);
lean_inc(x_2);
x_391 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__12), 9, 6);
lean_closure_set(x_391, 0, x_2);
lean_closure_set(x_391, 1, x_5);
lean_closure_set(x_391, 2, x_388);
lean_closure_set(x_391, 3, x_389);
lean_closure_set(x_391, 4, x_263);
lean_closure_set(x_391, 5, x_390);
lean_inc(x_1);
x_392 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_392, 0, x_1);
if (x_387 == 0)
{
uint8_t x_401; 
x_401 = l_Lean_Expr_hasExprMVar(x_5);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_402 = l_Lean_ConstantInfo_hints(x_60);
lean_dec(x_60);
x_403 = l_Lean_ConstantInfo_hints(x_61);
lean_dec(x_61);
x_404 = l_Lean_ReducibilityHints_lt(x_402, x_403);
if (x_404 == 0)
{
uint8_t x_405; 
x_405 = l_Lean_ReducibilityHints_lt(x_403, x_402);
lean_dec(x_402);
lean_dec(x_403);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_inc(x_264);
lean_inc(x_4);
lean_inc(x_2);
x_406 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_406, 0, x_2);
lean_closure_set(x_406, 1, x_4);
lean_closure_set(x_406, 2, x_388);
lean_closure_set(x_406, 3, x_389);
lean_closure_set(x_406, 4, x_264);
lean_closure_set(x_406, 5, x_390);
x_407 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_392);
lean_inc(x_1);
x_408 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_408, 0, x_1);
lean_closure_set(x_408, 1, x_392);
lean_closure_set(x_408, 2, x_2);
lean_closure_set(x_408, 3, x_3);
lean_closure_set(x_408, 4, x_5);
lean_closure_set(x_408, 5, x_407);
lean_closure_set(x_408, 6, x_406);
lean_inc(x_3);
lean_inc(x_392);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_409 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_409, 0, x_5);
lean_closure_set(x_409, 1, x_388);
lean_closure_set(x_409, 2, x_389);
lean_closure_set(x_409, 3, x_23);
lean_closure_set(x_409, 4, x_263);
lean_closure_set(x_409, 5, x_390);
lean_closure_set(x_409, 6, x_2);
lean_closure_set(x_409, 7, x_4);
lean_closure_set(x_409, 8, x_264);
lean_closure_set(x_409, 9, x_1);
lean_closure_set(x_409, 10, x_392);
lean_closure_set(x_409, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_392);
lean_inc(x_1);
x_410 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_410, 0, x_1);
lean_closure_set(x_410, 1, x_392);
lean_closure_set(x_410, 2, x_2);
lean_closure_set(x_410, 3, x_3);
lean_closure_set(x_410, 4, x_4);
lean_closure_set(x_410, 5, x_408);
lean_closure_set(x_410, 6, x_409);
x_411 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_392, x_2, x_3, x_4, x_410, x_391, x_6, x_58);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_inc(x_264);
lean_inc(x_4);
lean_inc(x_2);
x_412 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_412, 0, x_2);
lean_closure_set(x_412, 1, x_4);
lean_closure_set(x_412, 2, x_388);
lean_closure_set(x_412, 3, x_389);
lean_closure_set(x_412, 4, x_264);
lean_closure_set(x_412, 5, x_390);
x_413 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_412);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_392);
lean_inc(x_1);
x_414 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_414, 0, x_1);
lean_closure_set(x_414, 1, x_392);
lean_closure_set(x_414, 2, x_2);
lean_closure_set(x_414, 3, x_3);
lean_closure_set(x_414, 4, x_5);
lean_closure_set(x_414, 5, x_413);
lean_closure_set(x_414, 6, x_412);
lean_inc(x_3);
lean_inc(x_392);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_415 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_415, 0, x_5);
lean_closure_set(x_415, 1, x_388);
lean_closure_set(x_415, 2, x_389);
lean_closure_set(x_415, 3, x_23);
lean_closure_set(x_415, 4, x_263);
lean_closure_set(x_415, 5, x_390);
lean_closure_set(x_415, 6, x_2);
lean_closure_set(x_415, 7, x_4);
lean_closure_set(x_415, 8, x_264);
lean_closure_set(x_415, 9, x_1);
lean_closure_set(x_415, 10, x_392);
lean_closure_set(x_415, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_392);
lean_inc(x_1);
x_416 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_416, 0, x_1);
lean_closure_set(x_416, 1, x_392);
lean_closure_set(x_416, 2, x_2);
lean_closure_set(x_416, 3, x_3);
lean_closure_set(x_416, 4, x_4);
lean_closure_set(x_416, 5, x_414);
lean_closure_set(x_416, 6, x_415);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_392);
lean_inc(x_1);
x_417 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_417, 0, x_1);
lean_closure_set(x_417, 1, x_392);
lean_closure_set(x_417, 2, x_2);
lean_closure_set(x_417, 3, x_3);
lean_closure_set(x_417, 4, x_5);
lean_closure_set(x_417, 5, x_416);
lean_closure_set(x_417, 6, x_412);
x_418 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_392, x_2, x_3, x_4, x_417, x_391, x_6, x_58);
return x_418;
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_403);
lean_dec(x_402);
lean_inc(x_264);
lean_inc(x_4);
lean_inc(x_2);
x_419 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_419, 0, x_2);
lean_closure_set(x_419, 1, x_4);
lean_closure_set(x_419, 2, x_388);
lean_closure_set(x_419, 3, x_389);
lean_closure_set(x_419, 4, x_264);
lean_closure_set(x_419, 5, x_390);
x_420 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_392);
lean_inc(x_1);
x_421 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_421, 0, x_1);
lean_closure_set(x_421, 1, x_392);
lean_closure_set(x_421, 2, x_2);
lean_closure_set(x_421, 3, x_3);
lean_closure_set(x_421, 4, x_5);
lean_closure_set(x_421, 5, x_420);
lean_closure_set(x_421, 6, x_419);
lean_inc(x_3);
lean_inc(x_392);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_422 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_422, 0, x_5);
lean_closure_set(x_422, 1, x_388);
lean_closure_set(x_422, 2, x_389);
lean_closure_set(x_422, 3, x_23);
lean_closure_set(x_422, 4, x_263);
lean_closure_set(x_422, 5, x_390);
lean_closure_set(x_422, 6, x_2);
lean_closure_set(x_422, 7, x_4);
lean_closure_set(x_422, 8, x_264);
lean_closure_set(x_422, 9, x_1);
lean_closure_set(x_422, 10, x_392);
lean_closure_set(x_422, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_392);
lean_inc(x_1);
x_423 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_423, 0, x_1);
lean_closure_set(x_423, 1, x_392);
lean_closure_set(x_423, 2, x_2);
lean_closure_set(x_423, 3, x_3);
lean_closure_set(x_423, 4, x_4);
lean_closure_set(x_423, 5, x_421);
lean_closure_set(x_423, 6, x_422);
lean_inc(x_391);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_392);
lean_inc(x_1);
x_424 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_424, 0, x_1);
lean_closure_set(x_424, 1, x_392);
lean_closure_set(x_424, 2, x_2);
lean_closure_set(x_424, 3, x_3);
lean_closure_set(x_424, 4, x_4);
lean_closure_set(x_424, 5, x_423);
lean_closure_set(x_424, 6, x_391);
x_425 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_392, x_2, x_3, x_4, x_424, x_391, x_6, x_58);
return x_425;
}
}
else
{
lean_object* x_426; 
lean_dec(x_61);
lean_dec(x_60);
x_426 = lean_box(0);
x_393 = x_426;
goto block_400;
}
}
else
{
lean_object* x_427; 
lean_dec(x_61);
lean_dec(x_60);
x_427 = lean_box(0);
x_393 = x_427;
goto block_400;
}
block_400:
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_393);
lean_inc(x_264);
lean_inc(x_4);
lean_inc(x_2);
x_394 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_394, 0, x_2);
lean_closure_set(x_394, 1, x_4);
lean_closure_set(x_394, 2, x_388);
lean_closure_set(x_394, 3, x_389);
lean_closure_set(x_394, 4, x_264);
lean_closure_set(x_394, 5, x_390);
x_395 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_392);
lean_inc(x_1);
x_396 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_396, 0, x_1);
lean_closure_set(x_396, 1, x_392);
lean_closure_set(x_396, 2, x_2);
lean_closure_set(x_396, 3, x_3);
lean_closure_set(x_396, 4, x_5);
lean_closure_set(x_396, 5, x_395);
lean_closure_set(x_396, 6, x_394);
lean_inc(x_3);
lean_inc(x_392);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_397 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_397, 0, x_5);
lean_closure_set(x_397, 1, x_388);
lean_closure_set(x_397, 2, x_389);
lean_closure_set(x_397, 3, x_23);
lean_closure_set(x_397, 4, x_263);
lean_closure_set(x_397, 5, x_390);
lean_closure_set(x_397, 6, x_2);
lean_closure_set(x_397, 7, x_4);
lean_closure_set(x_397, 8, x_264);
lean_closure_set(x_397, 9, x_1);
lean_closure_set(x_397, 10, x_392);
lean_closure_set(x_397, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_392);
lean_inc(x_1);
x_398 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_398, 0, x_1);
lean_closure_set(x_398, 1, x_392);
lean_closure_set(x_398, 2, x_2);
lean_closure_set(x_398, 3, x_3);
lean_closure_set(x_398, 4, x_4);
lean_closure_set(x_398, 5, x_396);
lean_closure_set(x_398, 6, x_397);
x_399 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_392, x_2, x_3, x_4, x_398, x_391, x_6, x_58);
return x_399;
}
}
else
{
lean_object* x_428; 
x_428 = lean_box(0);
x_349 = x_428;
goto block_385;
}
}
block_294:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_283);
x_284 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_285 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_286 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_264);
lean_inc(x_4);
lean_inc(x_2);
x_287 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_287, 0, x_2);
lean_closure_set(x_287, 1, x_4);
lean_closure_set(x_287, 2, x_284);
lean_closure_set(x_287, 3, x_285);
lean_closure_set(x_287, 4, x_264);
lean_closure_set(x_287, 5, x_286);
lean_inc(x_1);
x_288 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_288, 0, x_1);
x_289 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_287);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_288);
lean_inc(x_1);
x_290 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_290, 0, x_1);
lean_closure_set(x_290, 1, x_288);
lean_closure_set(x_290, 2, x_2);
lean_closure_set(x_290, 3, x_3);
lean_closure_set(x_290, 4, x_5);
lean_closure_set(x_290, 5, x_289);
lean_closure_set(x_290, 6, x_287);
lean_inc(x_3);
lean_inc(x_288);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_291 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_291, 0, x_5);
lean_closure_set(x_291, 1, x_284);
lean_closure_set(x_291, 2, x_285);
lean_closure_set(x_291, 3, x_23);
lean_closure_set(x_291, 4, x_263);
lean_closure_set(x_291, 5, x_286);
lean_closure_set(x_291, 6, x_2);
lean_closure_set(x_291, 7, x_4);
lean_closure_set(x_291, 8, x_264);
lean_closure_set(x_291, 9, x_1);
lean_closure_set(x_291, 10, x_288);
lean_closure_set(x_291, 11, x_3);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_288);
lean_inc(x_1);
x_292 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_292, 0, x_1);
lean_closure_set(x_292, 1, x_288);
lean_closure_set(x_292, 2, x_2);
lean_closure_set(x_292, 3, x_3);
lean_closure_set(x_292, 4, x_4);
lean_closure_set(x_292, 5, x_290);
lean_closure_set(x_292, 6, x_291);
x_293 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_288, x_2, x_3, x_5, x_292, x_287, x_6, x_58);
return x_293;
}
block_307:
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_295);
x_296 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_297 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_298 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_264);
lean_inc(x_4);
lean_inc(x_2);
x_299 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_299, 0, x_2);
lean_closure_set(x_299, 1, x_4);
lean_closure_set(x_299, 2, x_296);
lean_closure_set(x_299, 3, x_297);
lean_closure_set(x_299, 4, x_264);
lean_closure_set(x_299, 5, x_298);
lean_inc(x_1);
x_300 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_300, 0, x_1);
x_301 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_300);
lean_inc(x_1);
x_302 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_302, 0, x_1);
lean_closure_set(x_302, 1, x_300);
lean_closure_set(x_302, 2, x_2);
lean_closure_set(x_302, 3, x_3);
lean_closure_set(x_302, 4, x_5);
lean_closure_set(x_302, 5, x_301);
lean_closure_set(x_302, 6, x_299);
lean_inc(x_3);
lean_inc(x_300);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_263);
lean_inc(x_5);
x_303 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_303, 0, x_5);
lean_closure_set(x_303, 1, x_296);
lean_closure_set(x_303, 2, x_297);
lean_closure_set(x_303, 3, x_23);
lean_closure_set(x_303, 4, x_263);
lean_closure_set(x_303, 5, x_298);
lean_closure_set(x_303, 6, x_2);
lean_closure_set(x_303, 7, x_4);
lean_closure_set(x_303, 8, x_264);
lean_closure_set(x_303, 9, x_1);
lean_closure_set(x_303, 10, x_300);
lean_closure_set(x_303, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_300);
lean_inc(x_1);
x_304 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_304, 0, x_1);
lean_closure_set(x_304, 1, x_300);
lean_closure_set(x_304, 2, x_2);
lean_closure_set(x_304, 3, x_3);
lean_closure_set(x_304, 4, x_4);
lean_closure_set(x_304, 5, x_302);
lean_closure_set(x_304, 6, x_303);
lean_inc(x_2);
x_305 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__12), 9, 6);
lean_closure_set(x_305, 0, x_2);
lean_closure_set(x_305, 1, x_5);
lean_closure_set(x_305, 2, x_296);
lean_closure_set(x_305, 3, x_297);
lean_closure_set(x_305, 4, x_263);
lean_closure_set(x_305, 5, x_298);
x_306 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_300, x_2, x_3, x_4, x_304, x_305, x_6, x_58);
return x_306;
}
block_347:
{
uint8_t x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_308);
x_309 = l_Lean_Expr_hasExprMVar(x_4);
x_310 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_311 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_312 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_264);
lean_inc(x_4);
lean_inc(x_2);
x_313 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_313, 0, x_2);
lean_closure_set(x_313, 1, x_4);
lean_closure_set(x_313, 2, x_310);
lean_closure_set(x_313, 3, x_311);
lean_closure_set(x_313, 4, x_264);
lean_closure_set(x_313, 5, x_312);
lean_inc(x_1);
x_314 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_314, 0, x_1);
if (x_309 == 0)
{
uint8_t x_322; 
x_322 = l_Lean_Expr_hasExprMVar(x_5);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_323 = l_Lean_ConstantInfo_hints(x_60);
lean_dec(x_60);
x_324 = l_Lean_ConstantInfo_hints(x_61);
lean_dec(x_61);
x_325 = l_Lean_ReducibilityHints_lt(x_323, x_324);
if (x_325 == 0)
{
uint8_t x_326; 
x_326 = l_Lean_ReducibilityHints_lt(x_324, x_323);
lean_dec(x_323);
lean_dec(x_324);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_327 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_313);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_314);
lean_inc(x_1);
x_328 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_328, 0, x_1);
lean_closure_set(x_328, 1, x_314);
lean_closure_set(x_328, 2, x_2);
lean_closure_set(x_328, 3, x_3);
lean_closure_set(x_328, 4, x_5);
lean_closure_set(x_328, 5, x_327);
lean_closure_set(x_328, 6, x_313);
lean_inc(x_3);
lean_inc(x_314);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_329 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_329, 0, x_5);
lean_closure_set(x_329, 1, x_310);
lean_closure_set(x_329, 2, x_311);
lean_closure_set(x_329, 3, x_23);
lean_closure_set(x_329, 4, x_263);
lean_closure_set(x_329, 5, x_312);
lean_closure_set(x_329, 6, x_2);
lean_closure_set(x_329, 7, x_4);
lean_closure_set(x_329, 8, x_264);
lean_closure_set(x_329, 9, x_1);
lean_closure_set(x_329, 10, x_314);
lean_closure_set(x_329, 11, x_3);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_314);
lean_inc(x_1);
x_330 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_330, 0, x_1);
lean_closure_set(x_330, 1, x_314);
lean_closure_set(x_330, 2, x_2);
lean_closure_set(x_330, 3, x_3);
lean_closure_set(x_330, 4, x_4);
lean_closure_set(x_330, 5, x_328);
lean_closure_set(x_330, 6, x_329);
x_331 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_314, x_2, x_3, x_5, x_330, x_313, x_6, x_58);
return x_331;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_332 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_313);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_314);
lean_inc(x_1);
x_333 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_333, 0, x_1);
lean_closure_set(x_333, 1, x_314);
lean_closure_set(x_333, 2, x_2);
lean_closure_set(x_333, 3, x_3);
lean_closure_set(x_333, 4, x_5);
lean_closure_set(x_333, 5, x_332);
lean_closure_set(x_333, 6, x_313);
lean_inc(x_3);
lean_inc(x_314);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_334 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_334, 0, x_5);
lean_closure_set(x_334, 1, x_310);
lean_closure_set(x_334, 2, x_311);
lean_closure_set(x_334, 3, x_23);
lean_closure_set(x_334, 4, x_263);
lean_closure_set(x_334, 5, x_312);
lean_closure_set(x_334, 6, x_2);
lean_closure_set(x_334, 7, x_4);
lean_closure_set(x_334, 8, x_264);
lean_closure_set(x_334, 9, x_1);
lean_closure_set(x_334, 10, x_314);
lean_closure_set(x_334, 11, x_3);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_314);
lean_inc(x_1);
x_335 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_335, 0, x_1);
lean_closure_set(x_335, 1, x_314);
lean_closure_set(x_335, 2, x_2);
lean_closure_set(x_335, 3, x_3);
lean_closure_set(x_335, 4, x_4);
lean_closure_set(x_335, 5, x_333);
lean_closure_set(x_335, 6, x_334);
lean_inc(x_313);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_314);
lean_inc(x_1);
x_336 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_336, 0, x_1);
lean_closure_set(x_336, 1, x_314);
lean_closure_set(x_336, 2, x_2);
lean_closure_set(x_336, 3, x_3);
lean_closure_set(x_336, 4, x_5);
lean_closure_set(x_336, 5, x_335);
lean_closure_set(x_336, 6, x_313);
x_337 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_314, x_2, x_3, x_5, x_336, x_313, x_6, x_58);
return x_337;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_324);
lean_dec(x_323);
x_338 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_313);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_314);
lean_inc(x_1);
x_339 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_339, 0, x_1);
lean_closure_set(x_339, 1, x_314);
lean_closure_set(x_339, 2, x_2);
lean_closure_set(x_339, 3, x_3);
lean_closure_set(x_339, 4, x_5);
lean_closure_set(x_339, 5, x_338);
lean_closure_set(x_339, 6, x_313);
lean_inc(x_3);
lean_inc(x_314);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_263);
lean_inc(x_5);
x_340 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_340, 0, x_5);
lean_closure_set(x_340, 1, x_310);
lean_closure_set(x_340, 2, x_311);
lean_closure_set(x_340, 3, x_23);
lean_closure_set(x_340, 4, x_263);
lean_closure_set(x_340, 5, x_312);
lean_closure_set(x_340, 6, x_2);
lean_closure_set(x_340, 7, x_4);
lean_closure_set(x_340, 8, x_264);
lean_closure_set(x_340, 9, x_1);
lean_closure_set(x_340, 10, x_314);
lean_closure_set(x_340, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_314);
lean_inc(x_1);
x_341 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_341, 0, x_1);
lean_closure_set(x_341, 1, x_314);
lean_closure_set(x_341, 2, x_2);
lean_closure_set(x_341, 3, x_3);
lean_closure_set(x_341, 4, x_4);
lean_closure_set(x_341, 5, x_339);
lean_closure_set(x_341, 6, x_340);
lean_inc(x_5);
lean_inc(x_2);
x_342 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__12), 9, 6);
lean_closure_set(x_342, 0, x_2);
lean_closure_set(x_342, 1, x_5);
lean_closure_set(x_342, 2, x_310);
lean_closure_set(x_342, 3, x_311);
lean_closure_set(x_342, 4, x_263);
lean_closure_set(x_342, 5, x_312);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_314);
lean_inc(x_1);
x_343 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_343, 0, x_1);
lean_closure_set(x_343, 1, x_314);
lean_closure_set(x_343, 2, x_2);
lean_closure_set(x_343, 3, x_3);
lean_closure_set(x_343, 4, x_4);
lean_closure_set(x_343, 5, x_341);
lean_closure_set(x_343, 6, x_342);
x_344 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_314, x_2, x_3, x_5, x_343, x_313, x_6, x_58);
return x_344;
}
}
else
{
lean_object* x_345; 
lean_dec(x_61);
lean_dec(x_60);
x_345 = lean_box(0);
x_315 = x_345;
goto block_321;
}
}
else
{
lean_object* x_346; 
lean_dec(x_61);
lean_dec(x_60);
x_346 = lean_box(0);
x_315 = x_346;
goto block_321;
}
block_321:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_315);
x_316 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_313);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_314);
lean_inc(x_1);
x_317 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_317, 0, x_1);
lean_closure_set(x_317, 1, x_314);
lean_closure_set(x_317, 2, x_2);
lean_closure_set(x_317, 3, x_3);
lean_closure_set(x_317, 4, x_5);
lean_closure_set(x_317, 5, x_316);
lean_closure_set(x_317, 6, x_313);
lean_inc(x_3);
lean_inc(x_314);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_318 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_318, 0, x_5);
lean_closure_set(x_318, 1, x_310);
lean_closure_set(x_318, 2, x_311);
lean_closure_set(x_318, 3, x_23);
lean_closure_set(x_318, 4, x_263);
lean_closure_set(x_318, 5, x_312);
lean_closure_set(x_318, 6, x_2);
lean_closure_set(x_318, 7, x_4);
lean_closure_set(x_318, 8, x_264);
lean_closure_set(x_318, 9, x_1);
lean_closure_set(x_318, 10, x_314);
lean_closure_set(x_318, 11, x_3);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_314);
lean_inc(x_1);
x_319 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_319, 0, x_1);
lean_closure_set(x_319, 1, x_314);
lean_closure_set(x_319, 2, x_2);
lean_closure_set(x_319, 3, x_3);
lean_closure_set(x_319, 4, x_4);
lean_closure_set(x_319, 5, x_317);
lean_closure_set(x_319, 6, x_318);
x_320 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_314, x_2, x_3, x_5, x_319, x_313, x_6, x_58);
return x_320;
}
}
block_385:
{
lean_dec(x_349);
if (x_282 == 0)
{
if (x_348 == 0)
{
uint8_t x_350; 
x_350 = l_Lean_Expr_hasExprMVar(x_4);
if (x_350 == 0)
{
uint8_t x_351; 
x_351 = l_Lean_Expr_hasExprMVar(x_5);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_352 = l_Lean_ConstantInfo_hints(x_60);
lean_dec(x_60);
x_353 = l_Lean_ConstantInfo_hints(x_61);
lean_dec(x_61);
x_354 = l_Lean_ReducibilityHints_lt(x_352, x_353);
if (x_354 == 0)
{
uint8_t x_355; 
x_355 = l_Lean_ReducibilityHints_lt(x_353, x_352);
lean_dec(x_352);
lean_dec(x_353);
if (x_355 == 0)
{
lean_object* x_356; 
x_356 = lean_box(0);
x_270 = x_356;
goto block_280;
}
else
{
lean_object* x_357; 
x_357 = lean_box(0);
x_283 = x_357;
goto block_294;
}
}
else
{
lean_object* x_358; 
lean_dec(x_353);
lean_dec(x_352);
x_358 = lean_box(0);
x_295 = x_358;
goto block_307;
}
}
else
{
lean_object* x_359; 
lean_dec(x_61);
lean_dec(x_60);
x_359 = lean_box(0);
x_270 = x_359;
goto block_280;
}
}
else
{
lean_object* x_360; 
lean_dec(x_61);
lean_dec(x_60);
x_360 = lean_box(0);
x_270 = x_360;
goto block_280;
}
}
else
{
lean_object* x_361; 
x_361 = lean_box(0);
x_308 = x_361;
goto block_347;
}
}
else
{
if (x_269 == 0)
{
uint8_t x_362; 
x_362 = l_Lean_Expr_hasExprMVar(x_4);
if (x_362 == 0)
{
uint8_t x_363; 
x_363 = l_Lean_Expr_hasExprMVar(x_5);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_364 = l_Lean_ConstantInfo_hints(x_60);
lean_dec(x_60);
x_365 = l_Lean_ConstantInfo_hints(x_61);
lean_dec(x_61);
x_366 = l_Lean_ReducibilityHints_lt(x_364, x_365);
if (x_366 == 0)
{
uint8_t x_367; 
x_367 = l_Lean_ReducibilityHints_lt(x_365, x_364);
lean_dec(x_364);
lean_dec(x_365);
if (x_367 == 0)
{
lean_object* x_368; 
x_368 = lean_box(0);
x_270 = x_368;
goto block_280;
}
else
{
lean_object* x_369; 
x_369 = lean_box(0);
x_283 = x_369;
goto block_294;
}
}
else
{
lean_object* x_370; 
lean_dec(x_365);
lean_dec(x_364);
x_370 = lean_box(0);
x_295 = x_370;
goto block_307;
}
}
else
{
lean_object* x_371; 
lean_dec(x_61);
lean_dec(x_60);
x_371 = lean_box(0);
x_270 = x_371;
goto block_280;
}
}
else
{
lean_object* x_372; 
lean_dec(x_61);
lean_dec(x_60);
x_372 = lean_box(0);
x_270 = x_372;
goto block_280;
}
}
else
{
if (x_348 == 0)
{
uint8_t x_373; 
x_373 = l_Lean_Expr_hasExprMVar(x_4);
if (x_373 == 0)
{
uint8_t x_374; 
x_374 = l_Lean_Expr_hasExprMVar(x_5);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; uint8_t x_377; 
x_375 = l_Lean_ConstantInfo_hints(x_60);
lean_dec(x_60);
x_376 = l_Lean_ConstantInfo_hints(x_61);
lean_dec(x_61);
x_377 = l_Lean_ReducibilityHints_lt(x_375, x_376);
if (x_377 == 0)
{
uint8_t x_378; 
x_378 = l_Lean_ReducibilityHints_lt(x_376, x_375);
lean_dec(x_375);
lean_dec(x_376);
if (x_378 == 0)
{
lean_object* x_379; 
x_379 = lean_box(0);
x_270 = x_379;
goto block_280;
}
else
{
lean_object* x_380; 
x_380 = lean_box(0);
x_283 = x_380;
goto block_294;
}
}
else
{
lean_object* x_381; 
lean_dec(x_376);
lean_dec(x_375);
x_381 = lean_box(0);
x_295 = x_381;
goto block_307;
}
}
else
{
lean_object* x_382; 
lean_dec(x_61);
lean_dec(x_60);
x_382 = lean_box(0);
x_270 = x_382;
goto block_280;
}
}
else
{
lean_object* x_383; 
lean_dec(x_61);
lean_dec(x_60);
x_383 = lean_box(0);
x_270 = x_383;
goto block_280;
}
}
else
{
lean_object* x_384; 
x_384 = lean_box(0);
x_308 = x_384;
goto block_347;
}
}
}
}
}
else
{
uint8_t x_429; 
x_429 = l_Lean_Expr_hasExprMVar(x_4);
if (x_429 == 0)
{
uint8_t x_430; 
x_430 = l_Lean_Expr_hasExprMVar(x_5);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_431 = l_Lean_ConstantInfo_hints(x_60);
lean_dec(x_60);
x_432 = l_Lean_ConstantInfo_hints(x_61);
lean_dec(x_61);
x_433 = l_Lean_ReducibilityHints_lt(x_431, x_432);
if (x_433 == 0)
{
uint8_t x_434; 
x_434 = l_Lean_ReducibilityHints_lt(x_432, x_431);
lean_dec(x_431);
lean_dec(x_432);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_435 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_436 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_437 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_264);
lean_inc(x_4);
lean_inc(x_2);
x_438 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_438, 0, x_2);
lean_closure_set(x_438, 1, x_4);
lean_closure_set(x_438, 2, x_435);
lean_closure_set(x_438, 3, x_436);
lean_closure_set(x_438, 4, x_264);
lean_closure_set(x_438, 5, x_437);
lean_inc(x_1);
x_439 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_439, 0, x_1);
x_440 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_439);
lean_inc(x_1);
x_441 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_441, 0, x_1);
lean_closure_set(x_441, 1, x_439);
lean_closure_set(x_441, 2, x_2);
lean_closure_set(x_441, 3, x_3);
lean_closure_set(x_441, 4, x_5);
lean_closure_set(x_441, 5, x_440);
lean_closure_set(x_441, 6, x_438);
lean_inc(x_3);
lean_inc(x_439);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_442 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_442, 0, x_5);
lean_closure_set(x_442, 1, x_435);
lean_closure_set(x_442, 2, x_436);
lean_closure_set(x_442, 3, x_23);
lean_closure_set(x_442, 4, x_263);
lean_closure_set(x_442, 5, x_437);
lean_closure_set(x_442, 6, x_2);
lean_closure_set(x_442, 7, x_4);
lean_closure_set(x_442, 8, x_264);
lean_closure_set(x_442, 9, x_1);
lean_closure_set(x_442, 10, x_439);
lean_closure_set(x_442, 11, x_3);
x_443 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_439, x_2, x_3, x_4, x_441, x_442, x_6, x_58);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_444 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_445 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_446 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_264);
lean_inc(x_4);
lean_inc(x_2);
x_447 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_447, 0, x_2);
lean_closure_set(x_447, 1, x_4);
lean_closure_set(x_447, 2, x_444);
lean_closure_set(x_447, 3, x_445);
lean_closure_set(x_447, 4, x_264);
lean_closure_set(x_447, 5, x_446);
lean_inc(x_1);
x_448 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_448, 0, x_1);
x_449 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_447);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_448);
lean_inc(x_1);
x_450 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_450, 0, x_1);
lean_closure_set(x_450, 1, x_448);
lean_closure_set(x_450, 2, x_2);
lean_closure_set(x_450, 3, x_3);
lean_closure_set(x_450, 4, x_5);
lean_closure_set(x_450, 5, x_449);
lean_closure_set(x_450, 6, x_447);
lean_inc(x_3);
lean_inc(x_448);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_451 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_451, 0, x_5);
lean_closure_set(x_451, 1, x_444);
lean_closure_set(x_451, 2, x_445);
lean_closure_set(x_451, 3, x_23);
lean_closure_set(x_451, 4, x_263);
lean_closure_set(x_451, 5, x_446);
lean_closure_set(x_451, 6, x_2);
lean_closure_set(x_451, 7, x_4);
lean_closure_set(x_451, 8, x_264);
lean_closure_set(x_451, 9, x_1);
lean_closure_set(x_451, 10, x_448);
lean_closure_set(x_451, 11, x_3);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_448);
lean_inc(x_1);
x_452 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_452, 0, x_1);
lean_closure_set(x_452, 1, x_448);
lean_closure_set(x_452, 2, x_2);
lean_closure_set(x_452, 3, x_3);
lean_closure_set(x_452, 4, x_4);
lean_closure_set(x_452, 5, x_450);
lean_closure_set(x_452, 6, x_451);
x_453 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_448, x_2, x_3, x_5, x_452, x_447, x_6, x_58);
return x_453;
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_432);
lean_dec(x_431);
x_454 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_455 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_456 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_264);
lean_inc(x_4);
lean_inc(x_2);
x_457 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_457, 0, x_2);
lean_closure_set(x_457, 1, x_4);
lean_closure_set(x_457, 2, x_454);
lean_closure_set(x_457, 3, x_455);
lean_closure_set(x_457, 4, x_264);
lean_closure_set(x_457, 5, x_456);
lean_inc(x_1);
x_458 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_458, 0, x_1);
x_459 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_458);
lean_inc(x_1);
x_460 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_460, 0, x_1);
lean_closure_set(x_460, 1, x_458);
lean_closure_set(x_460, 2, x_2);
lean_closure_set(x_460, 3, x_3);
lean_closure_set(x_460, 4, x_5);
lean_closure_set(x_460, 5, x_459);
lean_closure_set(x_460, 6, x_457);
lean_inc(x_3);
lean_inc(x_458);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_263);
lean_inc(x_5);
x_461 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_461, 0, x_5);
lean_closure_set(x_461, 1, x_454);
lean_closure_set(x_461, 2, x_455);
lean_closure_set(x_461, 3, x_23);
lean_closure_set(x_461, 4, x_263);
lean_closure_set(x_461, 5, x_456);
lean_closure_set(x_461, 6, x_2);
lean_closure_set(x_461, 7, x_4);
lean_closure_set(x_461, 8, x_264);
lean_closure_set(x_461, 9, x_1);
lean_closure_set(x_461, 10, x_458);
lean_closure_set(x_461, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_458);
lean_inc(x_1);
x_462 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_462, 0, x_1);
lean_closure_set(x_462, 1, x_458);
lean_closure_set(x_462, 2, x_2);
lean_closure_set(x_462, 3, x_3);
lean_closure_set(x_462, 4, x_4);
lean_closure_set(x_462, 5, x_460);
lean_closure_set(x_462, 6, x_461);
lean_inc(x_2);
x_463 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__12), 9, 6);
lean_closure_set(x_463, 0, x_2);
lean_closure_set(x_463, 1, x_5);
lean_closure_set(x_463, 2, x_454);
lean_closure_set(x_463, 3, x_455);
lean_closure_set(x_463, 4, x_263);
lean_closure_set(x_463, 5, x_456);
x_464 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_458, x_2, x_3, x_4, x_462, x_463, x_6, x_58);
return x_464;
}
}
else
{
lean_object* x_465; 
lean_dec(x_61);
lean_dec(x_60);
x_465 = lean_box(0);
x_270 = x_465;
goto block_280;
}
}
else
{
lean_object* x_466; 
lean_dec(x_61);
lean_dec(x_60);
x_466 = lean_box(0);
x_270 = x_466;
goto block_280;
}
}
block_280:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_270);
x_271 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_272 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_273 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_264);
lean_inc(x_4);
lean_inc(x_2);
x_274 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_274, 0, x_2);
lean_closure_set(x_274, 1, x_4);
lean_closure_set(x_274, 2, x_271);
lean_closure_set(x_274, 3, x_272);
lean_closure_set(x_274, 4, x_264);
lean_closure_set(x_274, 5, x_273);
lean_inc(x_1);
x_275 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_275, 0, x_1);
x_276 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_275);
lean_inc(x_1);
x_277 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_277, 0, x_1);
lean_closure_set(x_277, 1, x_275);
lean_closure_set(x_277, 2, x_2);
lean_closure_set(x_277, 3, x_3);
lean_closure_set(x_277, 4, x_5);
lean_closure_set(x_277, 5, x_276);
lean_closure_set(x_277, 6, x_274);
lean_inc(x_3);
lean_inc(x_275);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_278 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_278, 0, x_5);
lean_closure_set(x_278, 1, x_271);
lean_closure_set(x_278, 2, x_272);
lean_closure_set(x_278, 3, x_23);
lean_closure_set(x_278, 4, x_263);
lean_closure_set(x_278, 5, x_273);
lean_closure_set(x_278, 6, x_2);
lean_closure_set(x_278, 7, x_4);
lean_closure_set(x_278, 8, x_264);
lean_closure_set(x_278, 9, x_1);
lean_closure_set(x_278, 10, x_275);
lean_closure_set(x_278, 11, x_3);
x_279 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_275, x_2, x_3, x_4, x_277, x_278, x_6, x_58);
return x_279;
}
}
else
{
lean_dec(x_264);
lean_dec(x_263);
switch (lean_obj_tag(x_4)) {
case 4:
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_free_object(x_25);
x_467 = lean_ctor_get(x_4, 1);
lean_inc(x_467);
lean_dec(x_4);
x_468 = lean_ctor_get(x_5, 1);
lean_inc(x_468);
lean_dec(x_5);
x_469 = l_Lean_Meta_isListLevelDefEq___main(x_467, x_468, x_6, x_58);
if (lean_obj_tag(x_469) == 0)
{
uint8_t x_470; 
x_470 = !lean_is_exclusive(x_469);
if (x_470 == 0)
{
lean_object* x_471; uint8_t x_472; uint8_t x_473; lean_object* x_474; 
x_471 = lean_ctor_get(x_469, 0);
x_472 = lean_unbox(x_471);
lean_dec(x_471);
x_473 = l_Bool_toLBool(x_472);
x_474 = lean_box(x_473);
lean_ctor_set(x_469, 0, x_474);
return x_469;
}
else
{
lean_object* x_475; lean_object* x_476; uint8_t x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; 
x_475 = lean_ctor_get(x_469, 0);
x_476 = lean_ctor_get(x_469, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_469);
x_477 = lean_unbox(x_475);
lean_dec(x_475);
x_478 = l_Bool_toLBool(x_477);
x_479 = lean_box(x_478);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_476);
return x_480;
}
}
else
{
uint8_t x_481; 
x_481 = !lean_is_exclusive(x_469);
if (x_481 == 0)
{
return x_469;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_469, 0);
x_483 = lean_ctor_get(x_469, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_469);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
else
{
uint8_t x_485; lean_object* x_486; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_485 = 0;
x_486 = lean_box(x_485);
lean_ctor_set(x_25, 1, x_58);
lean_ctor_set(x_25, 0, x_486);
return x_25;
}
}
case 5:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_487; uint8_t x_488; 
lean_free_object(x_25);
x_487 = lean_ctor_get(x_58, 4);
lean_inc(x_487);
x_488 = lean_ctor_get_uint8(x_487, sizeof(void*)*1);
lean_dec(x_487);
if (x_488 == 0)
{
uint8_t x_489; 
x_489 = 0;
x_77 = x_489;
x_78 = x_58;
goto block_262;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_490 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_491 = l_Lean_Meta_tracer;
x_492 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__4;
x_493 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_490, x_491, x_492);
lean_inc(x_6);
x_494 = lean_apply_2(x_493, x_6, x_58);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; uint8_t x_497; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = lean_unbox(x_495);
lean_dec(x_495);
x_77 = x_497;
x_78 = x_496;
goto block_262;
}
else
{
uint8_t x_498; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_498 = !lean_is_exclusive(x_494);
if (x_498 == 0)
{
return x_494;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_494, 0);
x_500 = lean_ctor_get(x_494, 1);
lean_inc(x_500);
lean_inc(x_499);
lean_dec(x_494);
x_501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
return x_501;
}
}
}
}
else
{
uint8_t x_502; lean_object* x_503; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_502 = 0;
x_503 = lean_box(x_502);
lean_ctor_set(x_25, 1, x_58);
lean_ctor_set(x_25, 0, x_503);
return x_25;
}
}
default: 
{
uint8_t x_504; lean_object* x_505; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_504 = 0;
x_505 = lean_box(x_504);
lean_ctor_set(x_25, 1, x_58);
lean_ctor_set(x_25, 0, x_505);
return x_25;
}
}
}
block_76:
{
if (x_62 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_59);
x_64 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_65 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_66 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_4);
lean_inc(x_2);
x_67 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___boxed), 9, 6);
lean_closure_set(x_67, 0, x_2);
lean_closure_set(x_67, 1, x_4);
lean_closure_set(x_67, 2, x_61);
lean_closure_set(x_67, 3, x_64);
lean_closure_set(x_67, 4, x_65);
lean_closure_set(x_67, 5, x_66);
lean_inc(x_1);
x_68 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_68, 0, x_1);
x_69 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_68);
lean_inc(x_1);
x_70 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_70, 0, x_1);
lean_closure_set(x_70, 1, x_68);
lean_closure_set(x_70, 2, x_2);
lean_closure_set(x_70, 3, x_3);
lean_closure_set(x_70, 4, x_5);
lean_closure_set(x_70, 5, x_69);
lean_closure_set(x_70, 6, x_67);
lean_inc(x_3);
lean_inc(x_68);
lean_inc(x_1);
lean_inc(x_2);
x_71 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__8___boxed), 13, 10);
lean_closure_set(x_71, 0, x_60);
lean_closure_set(x_71, 1, x_64);
lean_closure_set(x_71, 2, x_65);
lean_closure_set(x_71, 3, x_23);
lean_closure_set(x_71, 4, x_66);
lean_closure_set(x_71, 5, x_2);
lean_closure_set(x_71, 6, x_5);
lean_closure_set(x_71, 7, x_1);
lean_closure_set(x_71, 8, x_68);
lean_closure_set(x_71, 9, x_3);
x_72 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_68, x_2, x_3, x_4, x_70, x_71, x_6, x_63);
return x_72;
}
else
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = 1;
x_74 = lean_box(x_73);
if (lean_is_scalar(x_59)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_59;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_63);
return x_75;
}
}
block_262:
{
if (x_77 == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_78, 4);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
uint8_t x_82; lean_object* x_83; 
x_82 = 1;
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_82);
lean_inc(x_6);
x_83 = l_Lean_Meta_try(x_24, x_6, x_78);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 4);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
lean_dec(x_83);
x_87 = !lean_is_exclusive(x_84);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_84, 4);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_85);
if (x_89 == 0)
{
uint8_t x_90; uint8_t x_91; 
x_90 = 0;
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_90);
x_91 = lean_unbox(x_86);
lean_dec(x_86);
x_62 = x_91;
x_63 = x_84;
goto block_76;
}
else
{
lean_object* x_92; uint8_t x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
lean_dec(x_85);
x_93 = 0;
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_93);
lean_ctor_set(x_84, 4, x_94);
x_95 = lean_unbox(x_86);
lean_dec(x_86);
x_62 = x_95;
x_63 = x_84;
goto block_76;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_96 = lean_ctor_get(x_84, 0);
x_97 = lean_ctor_get(x_84, 1);
x_98 = lean_ctor_get(x_84, 2);
x_99 = lean_ctor_get(x_84, 3);
x_100 = lean_ctor_get(x_84, 5);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_84);
x_101 = lean_ctor_get(x_85, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_102 = x_85;
} else {
 lean_dec_ref(x_85);
 x_102 = lean_box(0);
}
x_103 = 0;
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 1, 1);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_105, 0, x_96);
lean_ctor_set(x_105, 1, x_97);
lean_ctor_set(x_105, 2, x_98);
lean_ctor_set(x_105, 3, x_99);
lean_ctor_set(x_105, 4, x_104);
lean_ctor_set(x_105, 5, x_100);
x_106 = lean_unbox(x_86);
lean_dec(x_86);
x_62 = x_106;
x_63 = x_105;
goto block_76;
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = lean_ctor_get(x_83, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 4);
lean_inc(x_108);
x_109 = !lean_is_exclusive(x_83);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_83, 1);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_107);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_107, 4);
lean_dec(x_112);
x_113 = !lean_is_exclusive(x_108);
if (x_113 == 0)
{
uint8_t x_114; 
x_114 = 0;
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_114);
return x_83;
}
else
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_108, 0);
lean_inc(x_115);
lean_dec(x_108);
x_116 = 0;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
lean_ctor_set(x_107, 4, x_117);
return x_83;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_118 = lean_ctor_get(x_107, 0);
x_119 = lean_ctor_get(x_107, 1);
x_120 = lean_ctor_get(x_107, 2);
x_121 = lean_ctor_get(x_107, 3);
x_122 = lean_ctor_get(x_107, 5);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_107);
x_123 = lean_ctor_get(x_108, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_124 = x_108;
} else {
 lean_dec_ref(x_108);
 x_124 = lean_box(0);
}
x_125 = 0;
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 1, 1);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_127, 0, x_118);
lean_ctor_set(x_127, 1, x_119);
lean_ctor_set(x_127, 2, x_120);
lean_ctor_set(x_127, 3, x_121);
lean_ctor_set(x_127, 4, x_126);
lean_ctor_set(x_127, 5, x_122);
lean_ctor_set(x_83, 1, x_127);
return x_83;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_128 = lean_ctor_get(x_83, 0);
lean_inc(x_128);
lean_dec(x_83);
x_129 = lean_ctor_get(x_107, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_107, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_107, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_107, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_107, 5);
lean_inc(x_133);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 lean_ctor_release(x_107, 4);
 lean_ctor_release(x_107, 5);
 x_134 = x_107;
} else {
 lean_dec_ref(x_107);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_108, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_136 = x_108;
} else {
 lean_dec_ref(x_108);
 x_136 = lean_box(0);
}
x_137 = 0;
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 1, 1);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set_uint8(x_138, sizeof(void*)*1, x_137);
if (lean_is_scalar(x_134)) {
 x_139 = lean_alloc_ctor(0, 6, 0);
} else {
 x_139 = x_134;
}
lean_ctor_set(x_139, 0, x_129);
lean_ctor_set(x_139, 1, x_130);
lean_ctor_set(x_139, 2, x_131);
lean_ctor_set(x_139, 3, x_132);
lean_ctor_set(x_139, 4, x_138);
lean_ctor_set(x_139, 5, x_133);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_128);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_80, 0);
lean_inc(x_141);
lean_dec(x_80);
x_142 = 1;
x_143 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set_uint8(x_143, sizeof(void*)*1, x_142);
lean_ctor_set(x_78, 4, x_143);
lean_inc(x_6);
x_144 = l_Lean_Meta_try(x_24, x_6, x_78);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_145, 4);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 0);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_145, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_145, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_145, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_145, 5);
lean_inc(x_152);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 lean_ctor_release(x_145, 2);
 lean_ctor_release(x_145, 3);
 lean_ctor_release(x_145, 4);
 lean_ctor_release(x_145, 5);
 x_153 = x_145;
} else {
 lean_dec_ref(x_145);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_146, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_155 = x_146;
} else {
 lean_dec_ref(x_146);
 x_155 = lean_box(0);
}
x_156 = 0;
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 1, 1);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_156);
if (lean_is_scalar(x_153)) {
 x_158 = lean_alloc_ctor(0, 6, 0);
} else {
 x_158 = x_153;
}
lean_ctor_set(x_158, 0, x_148);
lean_ctor_set(x_158, 1, x_149);
lean_ctor_set(x_158, 2, x_150);
lean_ctor_set(x_158, 3, x_151);
lean_ctor_set(x_158, 4, x_157);
lean_ctor_set(x_158, 5, x_152);
x_159 = lean_unbox(x_147);
lean_dec(x_147);
x_62 = x_159;
x_63 = x_158;
goto block_76;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_ctor_get(x_144, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 4);
lean_inc(x_161);
x_162 = lean_ctor_get(x_144, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_163 = x_144;
} else {
 lean_dec_ref(x_144);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_160, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_160, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_160, 5);
lean_inc(x_168);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 lean_ctor_release(x_160, 5);
 x_169 = x_160;
} else {
 lean_dec_ref(x_160);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_161, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_171 = x_161;
} else {
 lean_dec_ref(x_161);
 x_171 = lean_box(0);
}
x_172 = 0;
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 1, 1);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_172);
if (lean_is_scalar(x_169)) {
 x_174 = lean_alloc_ctor(0, 6, 0);
} else {
 x_174 = x_169;
}
lean_ctor_set(x_174, 0, x_164);
lean_ctor_set(x_174, 1, x_165);
lean_ctor_set(x_174, 2, x_166);
lean_ctor_set(x_174, 3, x_167);
lean_ctor_set(x_174, 4, x_173);
lean_ctor_set(x_174, 5, x_168);
if (lean_is_scalar(x_163)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_163;
}
lean_ctor_set(x_175, 0, x_162);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_176 = lean_ctor_get(x_78, 4);
x_177 = lean_ctor_get(x_78, 0);
x_178 = lean_ctor_get(x_78, 1);
x_179 = lean_ctor_get(x_78, 2);
x_180 = lean_ctor_get(x_78, 3);
x_181 = lean_ctor_get(x_78, 5);
lean_inc(x_181);
lean_inc(x_176);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_78);
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
x_184 = 1;
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 1, 1);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set_uint8(x_185, sizeof(void*)*1, x_184);
x_186 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_186, 0, x_177);
lean_ctor_set(x_186, 1, x_178);
lean_ctor_set(x_186, 2, x_179);
lean_ctor_set(x_186, 3, x_180);
lean_ctor_set(x_186, 4, x_185);
lean_ctor_set(x_186, 5, x_181);
lean_inc(x_6);
x_187 = l_Lean_Meta_try(x_24, x_6, x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 4);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 5);
lean_inc(x_195);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 x_196 = x_188;
} else {
 lean_dec_ref(x_188);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_189, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_198 = x_189;
} else {
 lean_dec_ref(x_189);
 x_198 = lean_box(0);
}
x_199 = 0;
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 1, 1);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_199);
if (lean_is_scalar(x_196)) {
 x_201 = lean_alloc_ctor(0, 6, 0);
} else {
 x_201 = x_196;
}
lean_ctor_set(x_201, 0, x_191);
lean_ctor_set(x_201, 1, x_192);
lean_ctor_set(x_201, 2, x_193);
lean_ctor_set(x_201, 3, x_194);
lean_ctor_set(x_201, 4, x_200);
lean_ctor_set(x_201, 5, x_195);
x_202 = lean_unbox(x_190);
lean_dec(x_190);
x_62 = x_202;
x_63 = x_201;
goto block_76;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_ctor_get(x_187, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_203, 4);
lean_inc(x_204);
x_205 = lean_ctor_get(x_187, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_206 = x_187;
} else {
 lean_dec_ref(x_187);
 x_206 = lean_box(0);
}
x_207 = lean_ctor_get(x_203, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_203, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_203, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_203, 3);
lean_inc(x_210);
x_211 = lean_ctor_get(x_203, 5);
lean_inc(x_211);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 lean_ctor_release(x_203, 2);
 lean_ctor_release(x_203, 3);
 lean_ctor_release(x_203, 4);
 lean_ctor_release(x_203, 5);
 x_212 = x_203;
} else {
 lean_dec_ref(x_203);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_204, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_214 = x_204;
} else {
 lean_dec_ref(x_204);
 x_214 = lean_box(0);
}
x_215 = 0;
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(0, 1, 1);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set_uint8(x_216, sizeof(void*)*1, x_215);
if (lean_is_scalar(x_212)) {
 x_217 = lean_alloc_ctor(0, 6, 0);
} else {
 x_217 = x_212;
}
lean_ctor_set(x_217, 0, x_207);
lean_ctor_set(x_217, 1, x_208);
lean_ctor_set(x_217, 2, x_209);
lean_ctor_set(x_217, 3, x_210);
lean_ctor_set(x_217, 4, x_216);
lean_ctor_set(x_217, 5, x_211);
if (lean_is_scalar(x_206)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_206;
}
lean_ctor_set(x_218, 0, x_205);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_220 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
x_221 = l___private_Init_Lean_Trace_2__getResetTraces___rarg(x_219, x_220);
lean_inc(x_6);
x_222 = lean_apply_2(x_221, x_6, x_78);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
lean_inc(x_6);
x_225 = l_Lean_Meta_try(x_24, x_6, x_224);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
lean_inc(x_223);
x_229 = l___private_Init_Lean_Trace_1__addNode___rarg(x_220, x_223, x_228);
lean_inc(x_6);
x_230 = lean_apply_2(x_229, x_6, x_227);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; uint8_t x_232; 
lean_dec(x_223);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_unbox(x_226);
lean_dec(x_226);
x_62 = x_232;
x_63 = x_231;
goto block_76;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_226);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_230, 1);
lean_inc(x_234);
lean_dec(x_230);
x_235 = l___private_Init_Lean_Trace_1__addNode___rarg(x_220, x_223, x_228);
x_236 = lean_apply_2(x_235, x_6, x_234);
if (lean_obj_tag(x_236) == 0)
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_236);
if (x_237 == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_236, 0);
lean_dec(x_238);
lean_ctor_set_tag(x_236, 1);
lean_ctor_set(x_236, 0, x_233);
return x_236;
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_236, 1);
lean_inc(x_239);
lean_dec(x_236);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_233);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
else
{
uint8_t x_241; 
lean_dec(x_233);
x_241 = !lean_is_exclusive(x_236);
if (x_241 == 0)
{
return x_236;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_236, 0);
x_243 = lean_ctor_get(x_236, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_236);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_245 = lean_ctor_get(x_225, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_225, 1);
lean_inc(x_246);
lean_dec(x_225);
x_247 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_248 = l___private_Init_Lean_Trace_1__addNode___rarg(x_220, x_223, x_247);
x_249 = lean_apply_2(x_248, x_6, x_246);
if (lean_obj_tag(x_249) == 0)
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_249, 0);
lean_dec(x_251);
lean_ctor_set_tag(x_249, 1);
lean_ctor_set(x_249, 0, x_245);
return x_249;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
lean_dec(x_249);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_245);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
else
{
uint8_t x_254; 
lean_dec(x_245);
x_254 = !lean_is_exclusive(x_249);
if (x_254 == 0)
{
return x_249;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_249, 0);
x_256 = lean_ctor_get(x_249, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_249);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
}
else
{
uint8_t x_258; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_258 = !lean_is_exclusive(x_222);
if (x_258 == 0)
{
return x_222;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_222, 0);
x_260 = lean_ctor_get(x_222, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_222);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
}
}
}
}
else
{
uint8_t x_506; 
lean_free_object(x_25);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_506 = !lean_is_exclusive(x_29);
if (x_506 == 0)
{
return x_29;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_29, 0);
x_508 = lean_ctor_get(x_29, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_29);
x_509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
return x_509;
}
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_510 = lean_ctor_get(x_25, 0);
x_511 = lean_ctor_get(x_25, 1);
lean_inc(x_511);
lean_inc(x_510);
lean_dec(x_25);
x_512 = l___private_Init_Lean_Meta_ExprDefEq_17__isDeltaCandidate(x_9, x_6, x_511);
lean_dec(x_9);
if (lean_obj_tag(x_512) == 0)
{
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_513; 
lean_dec(x_24);
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; uint8_t x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_515 = x_512;
} else {
 lean_dec_ref(x_512);
 x_515 = lean_box(0);
}
x_516 = 2;
x_517 = lean_box(x_516);
if (lean_is_scalar(x_515)) {
 x_518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_518 = x_515;
}
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_514);
return x_518;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_519 = lean_ctor_get(x_512, 1);
lean_inc(x_519);
lean_dec(x_512);
x_520 = lean_ctor_get(x_513, 0);
lean_inc(x_520);
lean_dec(x_513);
x_521 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_522 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_523 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_2);
x_524 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___boxed), 9, 6);
lean_closure_set(x_524, 0, x_2);
lean_closure_set(x_524, 1, x_4);
lean_closure_set(x_524, 2, x_520);
lean_closure_set(x_524, 3, x_521);
lean_closure_set(x_524, 4, x_522);
lean_closure_set(x_524, 5, x_523);
lean_inc(x_1);
x_525 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_525, 0, x_1);
x_526 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
x_527 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_525, x_2, x_3, x_5, x_526, x_524, x_6, x_519);
return x_527;
}
}
else
{
lean_object* x_528; 
x_528 = lean_ctor_get(x_512, 0);
lean_inc(x_528);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_24);
x_529 = lean_ctor_get(x_512, 1);
lean_inc(x_529);
lean_dec(x_512);
x_530 = lean_ctor_get(x_510, 0);
lean_inc(x_530);
lean_dec(x_510);
x_531 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_532 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_533 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_2);
x_534 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___boxed), 9, 6);
lean_closure_set(x_534, 0, x_2);
lean_closure_set(x_534, 1, x_5);
lean_closure_set(x_534, 2, x_530);
lean_closure_set(x_534, 3, x_531);
lean_closure_set(x_534, 4, x_532);
lean_closure_set(x_534, 5, x_533);
lean_inc(x_1);
x_535 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_535, 0, x_1);
x_536 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
x_537 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_535, x_2, x_3, x_4, x_536, x_534, x_6, x_529);
return x_537;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; lean_object* x_543; uint8_t x_557; lean_object* x_558; lean_object* x_645; lean_object* x_646; uint8_t x_647; 
x_538 = lean_ctor_get(x_512, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_539 = x_512;
} else {
 lean_dec_ref(x_512);
 x_539 = lean_box(0);
}
x_540 = lean_ctor_get(x_510, 0);
lean_inc(x_540);
lean_dec(x_510);
x_541 = lean_ctor_get(x_528, 0);
lean_inc(x_541);
lean_dec(x_528);
x_645 = l_Lean_ConstantInfo_name(x_540);
x_646 = l_Lean_ConstantInfo_name(x_541);
x_647 = lean_name_eq(x_645, x_646);
if (x_647 == 0)
{
lean_object* x_648; uint8_t x_649; uint8_t x_650; uint8_t x_651; lean_object* x_652; 
lean_dec(x_539);
lean_dec(x_24);
x_648 = lean_ctor_get(x_6, 0);
lean_inc(x_648);
x_649 = lean_ctor_get_uint8(x_648, sizeof(void*)*1 + 4);
lean_dec(x_648);
x_650 = 2;
x_651 = l_Lean_Meta_TransparencyMode_beq(x_649, x_650);
if (x_651 == 0)
{
lean_object* x_663; uint8_t x_664; lean_object* x_665; lean_object* x_677; lean_object* x_690; uint8_t x_730; lean_object* x_731; 
x_663 = lean_ctor_get(x_538, 0);
lean_inc(x_663);
lean_inc(x_645);
lean_inc(x_663);
x_664 = l_Lean_isReducible(x_663, x_645);
lean_inc(x_646);
x_730 = l_Lean_isReducible(x_663, x_646);
if (x_664 == 0)
{
lean_object* x_768; 
x_768 = lean_box(0);
x_731 = x_768;
goto block_767;
}
else
{
if (x_730 == 0)
{
uint8_t x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_769 = l_Lean_Expr_hasExprMVar(x_4);
x_770 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_771 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_772 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_645);
lean_inc(x_5);
lean_inc(x_2);
x_773 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__12), 9, 6);
lean_closure_set(x_773, 0, x_2);
lean_closure_set(x_773, 1, x_5);
lean_closure_set(x_773, 2, x_770);
lean_closure_set(x_773, 3, x_771);
lean_closure_set(x_773, 4, x_645);
lean_closure_set(x_773, 5, x_772);
lean_inc(x_1);
x_774 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_774, 0, x_1);
if (x_769 == 0)
{
uint8_t x_783; 
x_783 = l_Lean_Expr_hasExprMVar(x_5);
if (x_783 == 0)
{
lean_object* x_784; lean_object* x_785; uint8_t x_786; 
x_784 = l_Lean_ConstantInfo_hints(x_540);
lean_dec(x_540);
x_785 = l_Lean_ConstantInfo_hints(x_541);
lean_dec(x_541);
x_786 = l_Lean_ReducibilityHints_lt(x_784, x_785);
if (x_786 == 0)
{
uint8_t x_787; 
x_787 = l_Lean_ReducibilityHints_lt(x_785, x_784);
lean_dec(x_784);
lean_dec(x_785);
if (x_787 == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
lean_inc(x_646);
lean_inc(x_4);
lean_inc(x_2);
x_788 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_788, 0, x_2);
lean_closure_set(x_788, 1, x_4);
lean_closure_set(x_788, 2, x_770);
lean_closure_set(x_788, 3, x_771);
lean_closure_set(x_788, 4, x_646);
lean_closure_set(x_788, 5, x_772);
x_789 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_774);
lean_inc(x_1);
x_790 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_790, 0, x_1);
lean_closure_set(x_790, 1, x_774);
lean_closure_set(x_790, 2, x_2);
lean_closure_set(x_790, 3, x_3);
lean_closure_set(x_790, 4, x_5);
lean_closure_set(x_790, 5, x_789);
lean_closure_set(x_790, 6, x_788);
lean_inc(x_3);
lean_inc(x_774);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_791 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_791, 0, x_5);
lean_closure_set(x_791, 1, x_770);
lean_closure_set(x_791, 2, x_771);
lean_closure_set(x_791, 3, x_23);
lean_closure_set(x_791, 4, x_645);
lean_closure_set(x_791, 5, x_772);
lean_closure_set(x_791, 6, x_2);
lean_closure_set(x_791, 7, x_4);
lean_closure_set(x_791, 8, x_646);
lean_closure_set(x_791, 9, x_1);
lean_closure_set(x_791, 10, x_774);
lean_closure_set(x_791, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_774);
lean_inc(x_1);
x_792 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_792, 0, x_1);
lean_closure_set(x_792, 1, x_774);
lean_closure_set(x_792, 2, x_2);
lean_closure_set(x_792, 3, x_3);
lean_closure_set(x_792, 4, x_4);
lean_closure_set(x_792, 5, x_790);
lean_closure_set(x_792, 6, x_791);
x_793 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_774, x_2, x_3, x_4, x_792, x_773, x_6, x_538);
return x_793;
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
lean_inc(x_646);
lean_inc(x_4);
lean_inc(x_2);
x_794 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_794, 0, x_2);
lean_closure_set(x_794, 1, x_4);
lean_closure_set(x_794, 2, x_770);
lean_closure_set(x_794, 3, x_771);
lean_closure_set(x_794, 4, x_646);
lean_closure_set(x_794, 5, x_772);
x_795 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_794);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_774);
lean_inc(x_1);
x_796 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_796, 0, x_1);
lean_closure_set(x_796, 1, x_774);
lean_closure_set(x_796, 2, x_2);
lean_closure_set(x_796, 3, x_3);
lean_closure_set(x_796, 4, x_5);
lean_closure_set(x_796, 5, x_795);
lean_closure_set(x_796, 6, x_794);
lean_inc(x_3);
lean_inc(x_774);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_797 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_797, 0, x_5);
lean_closure_set(x_797, 1, x_770);
lean_closure_set(x_797, 2, x_771);
lean_closure_set(x_797, 3, x_23);
lean_closure_set(x_797, 4, x_645);
lean_closure_set(x_797, 5, x_772);
lean_closure_set(x_797, 6, x_2);
lean_closure_set(x_797, 7, x_4);
lean_closure_set(x_797, 8, x_646);
lean_closure_set(x_797, 9, x_1);
lean_closure_set(x_797, 10, x_774);
lean_closure_set(x_797, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_774);
lean_inc(x_1);
x_798 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_798, 0, x_1);
lean_closure_set(x_798, 1, x_774);
lean_closure_set(x_798, 2, x_2);
lean_closure_set(x_798, 3, x_3);
lean_closure_set(x_798, 4, x_4);
lean_closure_set(x_798, 5, x_796);
lean_closure_set(x_798, 6, x_797);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_774);
lean_inc(x_1);
x_799 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_799, 0, x_1);
lean_closure_set(x_799, 1, x_774);
lean_closure_set(x_799, 2, x_2);
lean_closure_set(x_799, 3, x_3);
lean_closure_set(x_799, 4, x_5);
lean_closure_set(x_799, 5, x_798);
lean_closure_set(x_799, 6, x_794);
x_800 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_774, x_2, x_3, x_4, x_799, x_773, x_6, x_538);
return x_800;
}
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_785);
lean_dec(x_784);
lean_inc(x_646);
lean_inc(x_4);
lean_inc(x_2);
x_801 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_801, 0, x_2);
lean_closure_set(x_801, 1, x_4);
lean_closure_set(x_801, 2, x_770);
lean_closure_set(x_801, 3, x_771);
lean_closure_set(x_801, 4, x_646);
lean_closure_set(x_801, 5, x_772);
x_802 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_774);
lean_inc(x_1);
x_803 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_803, 0, x_1);
lean_closure_set(x_803, 1, x_774);
lean_closure_set(x_803, 2, x_2);
lean_closure_set(x_803, 3, x_3);
lean_closure_set(x_803, 4, x_5);
lean_closure_set(x_803, 5, x_802);
lean_closure_set(x_803, 6, x_801);
lean_inc(x_3);
lean_inc(x_774);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_804 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_804, 0, x_5);
lean_closure_set(x_804, 1, x_770);
lean_closure_set(x_804, 2, x_771);
lean_closure_set(x_804, 3, x_23);
lean_closure_set(x_804, 4, x_645);
lean_closure_set(x_804, 5, x_772);
lean_closure_set(x_804, 6, x_2);
lean_closure_set(x_804, 7, x_4);
lean_closure_set(x_804, 8, x_646);
lean_closure_set(x_804, 9, x_1);
lean_closure_set(x_804, 10, x_774);
lean_closure_set(x_804, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_774);
lean_inc(x_1);
x_805 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_805, 0, x_1);
lean_closure_set(x_805, 1, x_774);
lean_closure_set(x_805, 2, x_2);
lean_closure_set(x_805, 3, x_3);
lean_closure_set(x_805, 4, x_4);
lean_closure_set(x_805, 5, x_803);
lean_closure_set(x_805, 6, x_804);
lean_inc(x_773);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_774);
lean_inc(x_1);
x_806 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_806, 0, x_1);
lean_closure_set(x_806, 1, x_774);
lean_closure_set(x_806, 2, x_2);
lean_closure_set(x_806, 3, x_3);
lean_closure_set(x_806, 4, x_4);
lean_closure_set(x_806, 5, x_805);
lean_closure_set(x_806, 6, x_773);
x_807 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_774, x_2, x_3, x_4, x_806, x_773, x_6, x_538);
return x_807;
}
}
else
{
lean_object* x_808; 
lean_dec(x_541);
lean_dec(x_540);
x_808 = lean_box(0);
x_775 = x_808;
goto block_782;
}
}
else
{
lean_object* x_809; 
lean_dec(x_541);
lean_dec(x_540);
x_809 = lean_box(0);
x_775 = x_809;
goto block_782;
}
block_782:
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
lean_dec(x_775);
lean_inc(x_646);
lean_inc(x_4);
lean_inc(x_2);
x_776 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_776, 0, x_2);
lean_closure_set(x_776, 1, x_4);
lean_closure_set(x_776, 2, x_770);
lean_closure_set(x_776, 3, x_771);
lean_closure_set(x_776, 4, x_646);
lean_closure_set(x_776, 5, x_772);
x_777 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_774);
lean_inc(x_1);
x_778 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_778, 0, x_1);
lean_closure_set(x_778, 1, x_774);
lean_closure_set(x_778, 2, x_2);
lean_closure_set(x_778, 3, x_3);
lean_closure_set(x_778, 4, x_5);
lean_closure_set(x_778, 5, x_777);
lean_closure_set(x_778, 6, x_776);
lean_inc(x_3);
lean_inc(x_774);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_779 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_779, 0, x_5);
lean_closure_set(x_779, 1, x_770);
lean_closure_set(x_779, 2, x_771);
lean_closure_set(x_779, 3, x_23);
lean_closure_set(x_779, 4, x_645);
lean_closure_set(x_779, 5, x_772);
lean_closure_set(x_779, 6, x_2);
lean_closure_set(x_779, 7, x_4);
lean_closure_set(x_779, 8, x_646);
lean_closure_set(x_779, 9, x_1);
lean_closure_set(x_779, 10, x_774);
lean_closure_set(x_779, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_774);
lean_inc(x_1);
x_780 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_780, 0, x_1);
lean_closure_set(x_780, 1, x_774);
lean_closure_set(x_780, 2, x_2);
lean_closure_set(x_780, 3, x_3);
lean_closure_set(x_780, 4, x_4);
lean_closure_set(x_780, 5, x_778);
lean_closure_set(x_780, 6, x_779);
x_781 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_774, x_2, x_3, x_4, x_780, x_773, x_6, x_538);
return x_781;
}
}
else
{
lean_object* x_810; 
x_810 = lean_box(0);
x_731 = x_810;
goto block_767;
}
}
block_676:
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_665);
x_666 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_667 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_668 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_646);
lean_inc(x_4);
lean_inc(x_2);
x_669 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_669, 0, x_2);
lean_closure_set(x_669, 1, x_4);
lean_closure_set(x_669, 2, x_666);
lean_closure_set(x_669, 3, x_667);
lean_closure_set(x_669, 4, x_646);
lean_closure_set(x_669, 5, x_668);
lean_inc(x_1);
x_670 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_670, 0, x_1);
x_671 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_669);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_670);
lean_inc(x_1);
x_672 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_672, 0, x_1);
lean_closure_set(x_672, 1, x_670);
lean_closure_set(x_672, 2, x_2);
lean_closure_set(x_672, 3, x_3);
lean_closure_set(x_672, 4, x_5);
lean_closure_set(x_672, 5, x_671);
lean_closure_set(x_672, 6, x_669);
lean_inc(x_3);
lean_inc(x_670);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_673 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_673, 0, x_5);
lean_closure_set(x_673, 1, x_666);
lean_closure_set(x_673, 2, x_667);
lean_closure_set(x_673, 3, x_23);
lean_closure_set(x_673, 4, x_645);
lean_closure_set(x_673, 5, x_668);
lean_closure_set(x_673, 6, x_2);
lean_closure_set(x_673, 7, x_4);
lean_closure_set(x_673, 8, x_646);
lean_closure_set(x_673, 9, x_1);
lean_closure_set(x_673, 10, x_670);
lean_closure_set(x_673, 11, x_3);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_670);
lean_inc(x_1);
x_674 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_674, 0, x_1);
lean_closure_set(x_674, 1, x_670);
lean_closure_set(x_674, 2, x_2);
lean_closure_set(x_674, 3, x_3);
lean_closure_set(x_674, 4, x_4);
lean_closure_set(x_674, 5, x_672);
lean_closure_set(x_674, 6, x_673);
x_675 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_670, x_2, x_3, x_5, x_674, x_669, x_6, x_538);
return x_675;
}
block_689:
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
lean_dec(x_677);
x_678 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_679 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_680 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_646);
lean_inc(x_4);
lean_inc(x_2);
x_681 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_681, 0, x_2);
lean_closure_set(x_681, 1, x_4);
lean_closure_set(x_681, 2, x_678);
lean_closure_set(x_681, 3, x_679);
lean_closure_set(x_681, 4, x_646);
lean_closure_set(x_681, 5, x_680);
lean_inc(x_1);
x_682 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_682, 0, x_1);
x_683 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_682);
lean_inc(x_1);
x_684 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_684, 0, x_1);
lean_closure_set(x_684, 1, x_682);
lean_closure_set(x_684, 2, x_2);
lean_closure_set(x_684, 3, x_3);
lean_closure_set(x_684, 4, x_5);
lean_closure_set(x_684, 5, x_683);
lean_closure_set(x_684, 6, x_681);
lean_inc(x_3);
lean_inc(x_682);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_645);
lean_inc(x_5);
x_685 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_685, 0, x_5);
lean_closure_set(x_685, 1, x_678);
lean_closure_set(x_685, 2, x_679);
lean_closure_set(x_685, 3, x_23);
lean_closure_set(x_685, 4, x_645);
lean_closure_set(x_685, 5, x_680);
lean_closure_set(x_685, 6, x_2);
lean_closure_set(x_685, 7, x_4);
lean_closure_set(x_685, 8, x_646);
lean_closure_set(x_685, 9, x_1);
lean_closure_set(x_685, 10, x_682);
lean_closure_set(x_685, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_682);
lean_inc(x_1);
x_686 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_686, 0, x_1);
lean_closure_set(x_686, 1, x_682);
lean_closure_set(x_686, 2, x_2);
lean_closure_set(x_686, 3, x_3);
lean_closure_set(x_686, 4, x_4);
lean_closure_set(x_686, 5, x_684);
lean_closure_set(x_686, 6, x_685);
lean_inc(x_2);
x_687 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__12), 9, 6);
lean_closure_set(x_687, 0, x_2);
lean_closure_set(x_687, 1, x_5);
lean_closure_set(x_687, 2, x_678);
lean_closure_set(x_687, 3, x_679);
lean_closure_set(x_687, 4, x_645);
lean_closure_set(x_687, 5, x_680);
x_688 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_682, x_2, x_3, x_4, x_686, x_687, x_6, x_538);
return x_688;
}
block_729:
{
uint8_t x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
lean_dec(x_690);
x_691 = l_Lean_Expr_hasExprMVar(x_4);
x_692 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_693 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_694 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_646);
lean_inc(x_4);
lean_inc(x_2);
x_695 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_695, 0, x_2);
lean_closure_set(x_695, 1, x_4);
lean_closure_set(x_695, 2, x_692);
lean_closure_set(x_695, 3, x_693);
lean_closure_set(x_695, 4, x_646);
lean_closure_set(x_695, 5, x_694);
lean_inc(x_1);
x_696 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_696, 0, x_1);
if (x_691 == 0)
{
uint8_t x_704; 
x_704 = l_Lean_Expr_hasExprMVar(x_5);
if (x_704 == 0)
{
lean_object* x_705; lean_object* x_706; uint8_t x_707; 
x_705 = l_Lean_ConstantInfo_hints(x_540);
lean_dec(x_540);
x_706 = l_Lean_ConstantInfo_hints(x_541);
lean_dec(x_541);
x_707 = l_Lean_ReducibilityHints_lt(x_705, x_706);
if (x_707 == 0)
{
uint8_t x_708; 
x_708 = l_Lean_ReducibilityHints_lt(x_706, x_705);
lean_dec(x_705);
lean_dec(x_706);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_709 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_695);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_696);
lean_inc(x_1);
x_710 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_710, 0, x_1);
lean_closure_set(x_710, 1, x_696);
lean_closure_set(x_710, 2, x_2);
lean_closure_set(x_710, 3, x_3);
lean_closure_set(x_710, 4, x_5);
lean_closure_set(x_710, 5, x_709);
lean_closure_set(x_710, 6, x_695);
lean_inc(x_3);
lean_inc(x_696);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_711 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_711, 0, x_5);
lean_closure_set(x_711, 1, x_692);
lean_closure_set(x_711, 2, x_693);
lean_closure_set(x_711, 3, x_23);
lean_closure_set(x_711, 4, x_645);
lean_closure_set(x_711, 5, x_694);
lean_closure_set(x_711, 6, x_2);
lean_closure_set(x_711, 7, x_4);
lean_closure_set(x_711, 8, x_646);
lean_closure_set(x_711, 9, x_1);
lean_closure_set(x_711, 10, x_696);
lean_closure_set(x_711, 11, x_3);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_696);
lean_inc(x_1);
x_712 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_712, 0, x_1);
lean_closure_set(x_712, 1, x_696);
lean_closure_set(x_712, 2, x_2);
lean_closure_set(x_712, 3, x_3);
lean_closure_set(x_712, 4, x_4);
lean_closure_set(x_712, 5, x_710);
lean_closure_set(x_712, 6, x_711);
x_713 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_696, x_2, x_3, x_5, x_712, x_695, x_6, x_538);
return x_713;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_714 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_695);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_696);
lean_inc(x_1);
x_715 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_715, 0, x_1);
lean_closure_set(x_715, 1, x_696);
lean_closure_set(x_715, 2, x_2);
lean_closure_set(x_715, 3, x_3);
lean_closure_set(x_715, 4, x_5);
lean_closure_set(x_715, 5, x_714);
lean_closure_set(x_715, 6, x_695);
lean_inc(x_3);
lean_inc(x_696);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_716 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_716, 0, x_5);
lean_closure_set(x_716, 1, x_692);
lean_closure_set(x_716, 2, x_693);
lean_closure_set(x_716, 3, x_23);
lean_closure_set(x_716, 4, x_645);
lean_closure_set(x_716, 5, x_694);
lean_closure_set(x_716, 6, x_2);
lean_closure_set(x_716, 7, x_4);
lean_closure_set(x_716, 8, x_646);
lean_closure_set(x_716, 9, x_1);
lean_closure_set(x_716, 10, x_696);
lean_closure_set(x_716, 11, x_3);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_696);
lean_inc(x_1);
x_717 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_717, 0, x_1);
lean_closure_set(x_717, 1, x_696);
lean_closure_set(x_717, 2, x_2);
lean_closure_set(x_717, 3, x_3);
lean_closure_set(x_717, 4, x_4);
lean_closure_set(x_717, 5, x_715);
lean_closure_set(x_717, 6, x_716);
lean_inc(x_695);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_696);
lean_inc(x_1);
x_718 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_718, 0, x_1);
lean_closure_set(x_718, 1, x_696);
lean_closure_set(x_718, 2, x_2);
lean_closure_set(x_718, 3, x_3);
lean_closure_set(x_718, 4, x_5);
lean_closure_set(x_718, 5, x_717);
lean_closure_set(x_718, 6, x_695);
x_719 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_696, x_2, x_3, x_5, x_718, x_695, x_6, x_538);
return x_719;
}
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
lean_dec(x_706);
lean_dec(x_705);
x_720 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_695);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_696);
lean_inc(x_1);
x_721 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_721, 0, x_1);
lean_closure_set(x_721, 1, x_696);
lean_closure_set(x_721, 2, x_2);
lean_closure_set(x_721, 3, x_3);
lean_closure_set(x_721, 4, x_5);
lean_closure_set(x_721, 5, x_720);
lean_closure_set(x_721, 6, x_695);
lean_inc(x_3);
lean_inc(x_696);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_645);
lean_inc(x_5);
x_722 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_722, 0, x_5);
lean_closure_set(x_722, 1, x_692);
lean_closure_set(x_722, 2, x_693);
lean_closure_set(x_722, 3, x_23);
lean_closure_set(x_722, 4, x_645);
lean_closure_set(x_722, 5, x_694);
lean_closure_set(x_722, 6, x_2);
lean_closure_set(x_722, 7, x_4);
lean_closure_set(x_722, 8, x_646);
lean_closure_set(x_722, 9, x_1);
lean_closure_set(x_722, 10, x_696);
lean_closure_set(x_722, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_696);
lean_inc(x_1);
x_723 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_723, 0, x_1);
lean_closure_set(x_723, 1, x_696);
lean_closure_set(x_723, 2, x_2);
lean_closure_set(x_723, 3, x_3);
lean_closure_set(x_723, 4, x_4);
lean_closure_set(x_723, 5, x_721);
lean_closure_set(x_723, 6, x_722);
lean_inc(x_5);
lean_inc(x_2);
x_724 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__12), 9, 6);
lean_closure_set(x_724, 0, x_2);
lean_closure_set(x_724, 1, x_5);
lean_closure_set(x_724, 2, x_692);
lean_closure_set(x_724, 3, x_693);
lean_closure_set(x_724, 4, x_645);
lean_closure_set(x_724, 5, x_694);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_696);
lean_inc(x_1);
x_725 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_725, 0, x_1);
lean_closure_set(x_725, 1, x_696);
lean_closure_set(x_725, 2, x_2);
lean_closure_set(x_725, 3, x_3);
lean_closure_set(x_725, 4, x_4);
lean_closure_set(x_725, 5, x_723);
lean_closure_set(x_725, 6, x_724);
x_726 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_696, x_2, x_3, x_5, x_725, x_695, x_6, x_538);
return x_726;
}
}
else
{
lean_object* x_727; 
lean_dec(x_541);
lean_dec(x_540);
x_727 = lean_box(0);
x_697 = x_727;
goto block_703;
}
}
else
{
lean_object* x_728; 
lean_dec(x_541);
lean_dec(x_540);
x_728 = lean_box(0);
x_697 = x_728;
goto block_703;
}
block_703:
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
lean_dec(x_697);
x_698 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_695);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_696);
lean_inc(x_1);
x_699 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_699, 0, x_1);
lean_closure_set(x_699, 1, x_696);
lean_closure_set(x_699, 2, x_2);
lean_closure_set(x_699, 3, x_3);
lean_closure_set(x_699, 4, x_5);
lean_closure_set(x_699, 5, x_698);
lean_closure_set(x_699, 6, x_695);
lean_inc(x_3);
lean_inc(x_696);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_700 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_700, 0, x_5);
lean_closure_set(x_700, 1, x_692);
lean_closure_set(x_700, 2, x_693);
lean_closure_set(x_700, 3, x_23);
lean_closure_set(x_700, 4, x_645);
lean_closure_set(x_700, 5, x_694);
lean_closure_set(x_700, 6, x_2);
lean_closure_set(x_700, 7, x_4);
lean_closure_set(x_700, 8, x_646);
lean_closure_set(x_700, 9, x_1);
lean_closure_set(x_700, 10, x_696);
lean_closure_set(x_700, 11, x_3);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_696);
lean_inc(x_1);
x_701 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_701, 0, x_1);
lean_closure_set(x_701, 1, x_696);
lean_closure_set(x_701, 2, x_2);
lean_closure_set(x_701, 3, x_3);
lean_closure_set(x_701, 4, x_4);
lean_closure_set(x_701, 5, x_699);
lean_closure_set(x_701, 6, x_700);
x_702 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_696, x_2, x_3, x_5, x_701, x_695, x_6, x_538);
return x_702;
}
}
block_767:
{
lean_dec(x_731);
if (x_664 == 0)
{
if (x_730 == 0)
{
uint8_t x_732; 
x_732 = l_Lean_Expr_hasExprMVar(x_4);
if (x_732 == 0)
{
uint8_t x_733; 
x_733 = l_Lean_Expr_hasExprMVar(x_5);
if (x_733 == 0)
{
lean_object* x_734; lean_object* x_735; uint8_t x_736; 
x_734 = l_Lean_ConstantInfo_hints(x_540);
lean_dec(x_540);
x_735 = l_Lean_ConstantInfo_hints(x_541);
lean_dec(x_541);
x_736 = l_Lean_ReducibilityHints_lt(x_734, x_735);
if (x_736 == 0)
{
uint8_t x_737; 
x_737 = l_Lean_ReducibilityHints_lt(x_735, x_734);
lean_dec(x_734);
lean_dec(x_735);
if (x_737 == 0)
{
lean_object* x_738; 
x_738 = lean_box(0);
x_652 = x_738;
goto block_662;
}
else
{
lean_object* x_739; 
x_739 = lean_box(0);
x_665 = x_739;
goto block_676;
}
}
else
{
lean_object* x_740; 
lean_dec(x_735);
lean_dec(x_734);
x_740 = lean_box(0);
x_677 = x_740;
goto block_689;
}
}
else
{
lean_object* x_741; 
lean_dec(x_541);
lean_dec(x_540);
x_741 = lean_box(0);
x_652 = x_741;
goto block_662;
}
}
else
{
lean_object* x_742; 
lean_dec(x_541);
lean_dec(x_540);
x_742 = lean_box(0);
x_652 = x_742;
goto block_662;
}
}
else
{
lean_object* x_743; 
x_743 = lean_box(0);
x_690 = x_743;
goto block_729;
}
}
else
{
if (x_651 == 0)
{
uint8_t x_744; 
x_744 = l_Lean_Expr_hasExprMVar(x_4);
if (x_744 == 0)
{
uint8_t x_745; 
x_745 = l_Lean_Expr_hasExprMVar(x_5);
if (x_745 == 0)
{
lean_object* x_746; lean_object* x_747; uint8_t x_748; 
x_746 = l_Lean_ConstantInfo_hints(x_540);
lean_dec(x_540);
x_747 = l_Lean_ConstantInfo_hints(x_541);
lean_dec(x_541);
x_748 = l_Lean_ReducibilityHints_lt(x_746, x_747);
if (x_748 == 0)
{
uint8_t x_749; 
x_749 = l_Lean_ReducibilityHints_lt(x_747, x_746);
lean_dec(x_746);
lean_dec(x_747);
if (x_749 == 0)
{
lean_object* x_750; 
x_750 = lean_box(0);
x_652 = x_750;
goto block_662;
}
else
{
lean_object* x_751; 
x_751 = lean_box(0);
x_665 = x_751;
goto block_676;
}
}
else
{
lean_object* x_752; 
lean_dec(x_747);
lean_dec(x_746);
x_752 = lean_box(0);
x_677 = x_752;
goto block_689;
}
}
else
{
lean_object* x_753; 
lean_dec(x_541);
lean_dec(x_540);
x_753 = lean_box(0);
x_652 = x_753;
goto block_662;
}
}
else
{
lean_object* x_754; 
lean_dec(x_541);
lean_dec(x_540);
x_754 = lean_box(0);
x_652 = x_754;
goto block_662;
}
}
else
{
if (x_730 == 0)
{
uint8_t x_755; 
x_755 = l_Lean_Expr_hasExprMVar(x_4);
if (x_755 == 0)
{
uint8_t x_756; 
x_756 = l_Lean_Expr_hasExprMVar(x_5);
if (x_756 == 0)
{
lean_object* x_757; lean_object* x_758; uint8_t x_759; 
x_757 = l_Lean_ConstantInfo_hints(x_540);
lean_dec(x_540);
x_758 = l_Lean_ConstantInfo_hints(x_541);
lean_dec(x_541);
x_759 = l_Lean_ReducibilityHints_lt(x_757, x_758);
if (x_759 == 0)
{
uint8_t x_760; 
x_760 = l_Lean_ReducibilityHints_lt(x_758, x_757);
lean_dec(x_757);
lean_dec(x_758);
if (x_760 == 0)
{
lean_object* x_761; 
x_761 = lean_box(0);
x_652 = x_761;
goto block_662;
}
else
{
lean_object* x_762; 
x_762 = lean_box(0);
x_665 = x_762;
goto block_676;
}
}
else
{
lean_object* x_763; 
lean_dec(x_758);
lean_dec(x_757);
x_763 = lean_box(0);
x_677 = x_763;
goto block_689;
}
}
else
{
lean_object* x_764; 
lean_dec(x_541);
lean_dec(x_540);
x_764 = lean_box(0);
x_652 = x_764;
goto block_662;
}
}
else
{
lean_object* x_765; 
lean_dec(x_541);
lean_dec(x_540);
x_765 = lean_box(0);
x_652 = x_765;
goto block_662;
}
}
else
{
lean_object* x_766; 
x_766 = lean_box(0);
x_690 = x_766;
goto block_729;
}
}
}
}
}
else
{
uint8_t x_811; 
x_811 = l_Lean_Expr_hasExprMVar(x_4);
if (x_811 == 0)
{
uint8_t x_812; 
x_812 = l_Lean_Expr_hasExprMVar(x_5);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; uint8_t x_815; 
x_813 = l_Lean_ConstantInfo_hints(x_540);
lean_dec(x_540);
x_814 = l_Lean_ConstantInfo_hints(x_541);
lean_dec(x_541);
x_815 = l_Lean_ReducibilityHints_lt(x_813, x_814);
if (x_815 == 0)
{
uint8_t x_816; 
x_816 = l_Lean_ReducibilityHints_lt(x_814, x_813);
lean_dec(x_813);
lean_dec(x_814);
if (x_816 == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_817 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_818 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_819 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_646);
lean_inc(x_4);
lean_inc(x_2);
x_820 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_820, 0, x_2);
lean_closure_set(x_820, 1, x_4);
lean_closure_set(x_820, 2, x_817);
lean_closure_set(x_820, 3, x_818);
lean_closure_set(x_820, 4, x_646);
lean_closure_set(x_820, 5, x_819);
lean_inc(x_1);
x_821 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_821, 0, x_1);
x_822 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_821);
lean_inc(x_1);
x_823 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_823, 0, x_1);
lean_closure_set(x_823, 1, x_821);
lean_closure_set(x_823, 2, x_2);
lean_closure_set(x_823, 3, x_3);
lean_closure_set(x_823, 4, x_5);
lean_closure_set(x_823, 5, x_822);
lean_closure_set(x_823, 6, x_820);
lean_inc(x_3);
lean_inc(x_821);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_824 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_824, 0, x_5);
lean_closure_set(x_824, 1, x_817);
lean_closure_set(x_824, 2, x_818);
lean_closure_set(x_824, 3, x_23);
lean_closure_set(x_824, 4, x_645);
lean_closure_set(x_824, 5, x_819);
lean_closure_set(x_824, 6, x_2);
lean_closure_set(x_824, 7, x_4);
lean_closure_set(x_824, 8, x_646);
lean_closure_set(x_824, 9, x_1);
lean_closure_set(x_824, 10, x_821);
lean_closure_set(x_824, 11, x_3);
x_825 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_821, x_2, x_3, x_4, x_823, x_824, x_6, x_538);
return x_825;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_826 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_827 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_828 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_646);
lean_inc(x_4);
lean_inc(x_2);
x_829 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_829, 0, x_2);
lean_closure_set(x_829, 1, x_4);
lean_closure_set(x_829, 2, x_826);
lean_closure_set(x_829, 3, x_827);
lean_closure_set(x_829, 4, x_646);
lean_closure_set(x_829, 5, x_828);
lean_inc(x_1);
x_830 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_830, 0, x_1);
x_831 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_829);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_830);
lean_inc(x_1);
x_832 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_832, 0, x_1);
lean_closure_set(x_832, 1, x_830);
lean_closure_set(x_832, 2, x_2);
lean_closure_set(x_832, 3, x_3);
lean_closure_set(x_832, 4, x_5);
lean_closure_set(x_832, 5, x_831);
lean_closure_set(x_832, 6, x_829);
lean_inc(x_3);
lean_inc(x_830);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_833 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_833, 0, x_5);
lean_closure_set(x_833, 1, x_826);
lean_closure_set(x_833, 2, x_827);
lean_closure_set(x_833, 3, x_23);
lean_closure_set(x_833, 4, x_645);
lean_closure_set(x_833, 5, x_828);
lean_closure_set(x_833, 6, x_2);
lean_closure_set(x_833, 7, x_4);
lean_closure_set(x_833, 8, x_646);
lean_closure_set(x_833, 9, x_1);
lean_closure_set(x_833, 10, x_830);
lean_closure_set(x_833, 11, x_3);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_830);
lean_inc(x_1);
x_834 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_834, 0, x_1);
lean_closure_set(x_834, 1, x_830);
lean_closure_set(x_834, 2, x_2);
lean_closure_set(x_834, 3, x_3);
lean_closure_set(x_834, 4, x_4);
lean_closure_set(x_834, 5, x_832);
lean_closure_set(x_834, 6, x_833);
x_835 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_830, x_2, x_3, x_5, x_834, x_829, x_6, x_538);
return x_835;
}
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
lean_dec(x_814);
lean_dec(x_813);
x_836 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_837 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_838 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_646);
lean_inc(x_4);
lean_inc(x_2);
x_839 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_839, 0, x_2);
lean_closure_set(x_839, 1, x_4);
lean_closure_set(x_839, 2, x_836);
lean_closure_set(x_839, 3, x_837);
lean_closure_set(x_839, 4, x_646);
lean_closure_set(x_839, 5, x_838);
lean_inc(x_1);
x_840 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_840, 0, x_1);
x_841 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_840);
lean_inc(x_1);
x_842 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_842, 0, x_1);
lean_closure_set(x_842, 1, x_840);
lean_closure_set(x_842, 2, x_2);
lean_closure_set(x_842, 3, x_3);
lean_closure_set(x_842, 4, x_5);
lean_closure_set(x_842, 5, x_841);
lean_closure_set(x_842, 6, x_839);
lean_inc(x_3);
lean_inc(x_840);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_645);
lean_inc(x_5);
x_843 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_843, 0, x_5);
lean_closure_set(x_843, 1, x_836);
lean_closure_set(x_843, 2, x_837);
lean_closure_set(x_843, 3, x_23);
lean_closure_set(x_843, 4, x_645);
lean_closure_set(x_843, 5, x_838);
lean_closure_set(x_843, 6, x_2);
lean_closure_set(x_843, 7, x_4);
lean_closure_set(x_843, 8, x_646);
lean_closure_set(x_843, 9, x_1);
lean_closure_set(x_843, 10, x_840);
lean_closure_set(x_843, 11, x_3);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_840);
lean_inc(x_1);
x_844 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_844, 0, x_1);
lean_closure_set(x_844, 1, x_840);
lean_closure_set(x_844, 2, x_2);
lean_closure_set(x_844, 3, x_3);
lean_closure_set(x_844, 4, x_4);
lean_closure_set(x_844, 5, x_842);
lean_closure_set(x_844, 6, x_843);
lean_inc(x_2);
x_845 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__12), 9, 6);
lean_closure_set(x_845, 0, x_2);
lean_closure_set(x_845, 1, x_5);
lean_closure_set(x_845, 2, x_836);
lean_closure_set(x_845, 3, x_837);
lean_closure_set(x_845, 4, x_645);
lean_closure_set(x_845, 5, x_838);
x_846 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_840, x_2, x_3, x_4, x_844, x_845, x_6, x_538);
return x_846;
}
}
else
{
lean_object* x_847; 
lean_dec(x_541);
lean_dec(x_540);
x_847 = lean_box(0);
x_652 = x_847;
goto block_662;
}
}
else
{
lean_object* x_848; 
lean_dec(x_541);
lean_dec(x_540);
x_848 = lean_box(0);
x_652 = x_848;
goto block_662;
}
}
block_662:
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_652);
x_653 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_654 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_655 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_646);
lean_inc(x_4);
lean_inc(x_2);
x_656 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__9), 9, 6);
lean_closure_set(x_656, 0, x_2);
lean_closure_set(x_656, 1, x_4);
lean_closure_set(x_656, 2, x_653);
lean_closure_set(x_656, 3, x_654);
lean_closure_set(x_656, 4, x_646);
lean_closure_set(x_656, 5, x_655);
lean_inc(x_1);
x_657 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_657, 0, x_1);
x_658 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_657);
lean_inc(x_1);
x_659 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_659, 0, x_1);
lean_closure_set(x_659, 1, x_657);
lean_closure_set(x_659, 2, x_2);
lean_closure_set(x_659, 3, x_3);
lean_closure_set(x_659, 4, x_5);
lean_closure_set(x_659, 5, x_658);
lean_closure_set(x_659, 6, x_656);
lean_inc(x_3);
lean_inc(x_657);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_660 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__11), 15, 12);
lean_closure_set(x_660, 0, x_5);
lean_closure_set(x_660, 1, x_653);
lean_closure_set(x_660, 2, x_654);
lean_closure_set(x_660, 3, x_23);
lean_closure_set(x_660, 4, x_645);
lean_closure_set(x_660, 5, x_655);
lean_closure_set(x_660, 6, x_2);
lean_closure_set(x_660, 7, x_4);
lean_closure_set(x_660, 8, x_646);
lean_closure_set(x_660, 9, x_1);
lean_closure_set(x_660, 10, x_657);
lean_closure_set(x_660, 11, x_3);
x_661 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_657, x_2, x_3, x_4, x_659, x_660, x_6, x_538);
return x_661;
}
}
else
{
lean_dec(x_646);
lean_dec(x_645);
switch (lean_obj_tag(x_4)) {
case 4:
{
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_849 = lean_ctor_get(x_4, 1);
lean_inc(x_849);
lean_dec(x_4);
x_850 = lean_ctor_get(x_5, 1);
lean_inc(x_850);
lean_dec(x_5);
x_851 = l_Lean_Meta_isListLevelDefEq___main(x_849, x_850, x_6, x_538);
if (lean_obj_tag(x_851) == 0)
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; uint8_t x_855; uint8_t x_856; lean_object* x_857; lean_object* x_858; 
x_852 = lean_ctor_get(x_851, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_851, 1);
lean_inc(x_853);
if (lean_is_exclusive(x_851)) {
 lean_ctor_release(x_851, 0);
 lean_ctor_release(x_851, 1);
 x_854 = x_851;
} else {
 lean_dec_ref(x_851);
 x_854 = lean_box(0);
}
x_855 = lean_unbox(x_852);
lean_dec(x_852);
x_856 = l_Bool_toLBool(x_855);
x_857 = lean_box(x_856);
if (lean_is_scalar(x_854)) {
 x_858 = lean_alloc_ctor(0, 2, 0);
} else {
 x_858 = x_854;
}
lean_ctor_set(x_858, 0, x_857);
lean_ctor_set(x_858, 1, x_853);
return x_858;
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; 
x_859 = lean_ctor_get(x_851, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_851, 1);
lean_inc(x_860);
if (lean_is_exclusive(x_851)) {
 lean_ctor_release(x_851, 0);
 lean_ctor_release(x_851, 1);
 x_861 = x_851;
} else {
 lean_dec_ref(x_851);
 x_861 = lean_box(0);
}
if (lean_is_scalar(x_861)) {
 x_862 = lean_alloc_ctor(1, 2, 0);
} else {
 x_862 = x_861;
}
lean_ctor_set(x_862, 0, x_859);
lean_ctor_set(x_862, 1, x_860);
return x_862;
}
}
else
{
uint8_t x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_863 = 0;
x_864 = lean_box(x_863);
x_865 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_538);
return x_865;
}
}
case 5:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_866; uint8_t x_867; 
x_866 = lean_ctor_get(x_538, 4);
lean_inc(x_866);
x_867 = lean_ctor_get_uint8(x_866, sizeof(void*)*1);
lean_dec(x_866);
if (x_867 == 0)
{
uint8_t x_868; 
x_868 = 0;
x_557 = x_868;
x_558 = x_538;
goto block_644;
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_869 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_870 = l_Lean_Meta_tracer;
x_871 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__4;
x_872 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_869, x_870, x_871);
lean_inc(x_6);
x_873 = lean_apply_2(x_872, x_6, x_538);
if (lean_obj_tag(x_873) == 0)
{
lean_object* x_874; lean_object* x_875; uint8_t x_876; 
x_874 = lean_ctor_get(x_873, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_873, 1);
lean_inc(x_875);
lean_dec(x_873);
x_876 = lean_unbox(x_874);
lean_dec(x_874);
x_557 = x_876;
x_558 = x_875;
goto block_644;
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_877 = lean_ctor_get(x_873, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_873, 1);
lean_inc(x_878);
if (lean_is_exclusive(x_873)) {
 lean_ctor_release(x_873, 0);
 lean_ctor_release(x_873, 1);
 x_879 = x_873;
} else {
 lean_dec_ref(x_873);
 x_879 = lean_box(0);
}
if (lean_is_scalar(x_879)) {
 x_880 = lean_alloc_ctor(1, 2, 0);
} else {
 x_880 = x_879;
}
lean_ctor_set(x_880, 0, x_877);
lean_ctor_set(x_880, 1, x_878);
return x_880;
}
}
}
else
{
uint8_t x_881; lean_object* x_882; lean_object* x_883; 
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_881 = 0;
x_882 = lean_box(x_881);
x_883 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_538);
return x_883;
}
}
default: 
{
uint8_t x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_884 = 0;
x_885 = lean_box(x_884);
x_886 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_886, 0, x_885);
lean_ctor_set(x_886, 1, x_538);
return x_886;
}
}
}
block_556:
{
if (x_542 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_539);
x_544 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_545 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_546 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_inc(x_4);
lean_inc(x_2);
x_547 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___boxed), 9, 6);
lean_closure_set(x_547, 0, x_2);
lean_closure_set(x_547, 1, x_4);
lean_closure_set(x_547, 2, x_541);
lean_closure_set(x_547, 3, x_544);
lean_closure_set(x_547, 4, x_545);
lean_closure_set(x_547, 5, x_546);
lean_inc(x_1);
x_548 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_548, 0, x_1);
x_549 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_548);
lean_inc(x_1);
x_550 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinitionAux___rarg), 9, 7);
lean_closure_set(x_550, 0, x_1);
lean_closure_set(x_550, 1, x_548);
lean_closure_set(x_550, 2, x_2);
lean_closure_set(x_550, 3, x_3);
lean_closure_set(x_550, 4, x_5);
lean_closure_set(x_550, 5, x_549);
lean_closure_set(x_550, 6, x_547);
lean_inc(x_3);
lean_inc(x_548);
lean_inc(x_1);
lean_inc(x_2);
x_551 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__8___boxed), 13, 10);
lean_closure_set(x_551, 0, x_540);
lean_closure_set(x_551, 1, x_544);
lean_closure_set(x_551, 2, x_545);
lean_closure_set(x_551, 3, x_23);
lean_closure_set(x_551, 4, x_546);
lean_closure_set(x_551, 5, x_2);
lean_closure_set(x_551, 6, x_5);
lean_closure_set(x_551, 7, x_1);
lean_closure_set(x_551, 8, x_548);
lean_closure_set(x_551, 9, x_3);
x_552 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_548, x_2, x_3, x_4, x_550, x_551, x_6, x_543);
return x_552;
}
else
{
uint8_t x_553; lean_object* x_554; lean_object* x_555; 
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_553 = 1;
x_554 = lean_box(x_553);
if (lean_is_scalar(x_539)) {
 x_555 = lean_alloc_ctor(0, 2, 0);
} else {
 x_555 = x_539;
}
lean_ctor_set(x_555, 0, x_554);
lean_ctor_set(x_555, 1, x_543);
return x_555;
}
}
block_644:
{
if (x_557 == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; uint8_t x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_559 = lean_ctor_get(x_558, 4);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
x_562 = lean_ctor_get(x_558, 2);
lean_inc(x_562);
x_563 = lean_ctor_get(x_558, 3);
lean_inc(x_563);
x_564 = lean_ctor_get(x_558, 5);
lean_inc(x_564);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 lean_ctor_release(x_558, 2);
 lean_ctor_release(x_558, 3);
 lean_ctor_release(x_558, 4);
 lean_ctor_release(x_558, 5);
 x_565 = x_558;
} else {
 lean_dec_ref(x_558);
 x_565 = lean_box(0);
}
x_566 = lean_ctor_get(x_559, 0);
lean_inc(x_566);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 x_567 = x_559;
} else {
 lean_dec_ref(x_559);
 x_567 = lean_box(0);
}
x_568 = 1;
if (lean_is_scalar(x_567)) {
 x_569 = lean_alloc_ctor(0, 1, 1);
} else {
 x_569 = x_567;
}
lean_ctor_set(x_569, 0, x_566);
lean_ctor_set_uint8(x_569, sizeof(void*)*1, x_568);
if (lean_is_scalar(x_565)) {
 x_570 = lean_alloc_ctor(0, 6, 0);
} else {
 x_570 = x_565;
}
lean_ctor_set(x_570, 0, x_560);
lean_ctor_set(x_570, 1, x_561);
lean_ctor_set(x_570, 2, x_562);
lean_ctor_set(x_570, 3, x_563);
lean_ctor_set(x_570, 4, x_569);
lean_ctor_set(x_570, 5, x_564);
lean_inc(x_6);
x_571 = l_Lean_Meta_try(x_24, x_6, x_570);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; lean_object* x_584; lean_object* x_585; uint8_t x_586; 
x_572 = lean_ctor_get(x_571, 1);
lean_inc(x_572);
x_573 = lean_ctor_get(x_572, 4);
lean_inc(x_573);
x_574 = lean_ctor_get(x_571, 0);
lean_inc(x_574);
lean_dec(x_571);
x_575 = lean_ctor_get(x_572, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_572, 1);
lean_inc(x_576);
x_577 = lean_ctor_get(x_572, 2);
lean_inc(x_577);
x_578 = lean_ctor_get(x_572, 3);
lean_inc(x_578);
x_579 = lean_ctor_get(x_572, 5);
lean_inc(x_579);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 lean_ctor_release(x_572, 2);
 lean_ctor_release(x_572, 3);
 lean_ctor_release(x_572, 4);
 lean_ctor_release(x_572, 5);
 x_580 = x_572;
} else {
 lean_dec_ref(x_572);
 x_580 = lean_box(0);
}
x_581 = lean_ctor_get(x_573, 0);
lean_inc(x_581);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 x_582 = x_573;
} else {
 lean_dec_ref(x_573);
 x_582 = lean_box(0);
}
x_583 = 0;
if (lean_is_scalar(x_582)) {
 x_584 = lean_alloc_ctor(0, 1, 1);
} else {
 x_584 = x_582;
}
lean_ctor_set(x_584, 0, x_581);
lean_ctor_set_uint8(x_584, sizeof(void*)*1, x_583);
if (lean_is_scalar(x_580)) {
 x_585 = lean_alloc_ctor(0, 6, 0);
} else {
 x_585 = x_580;
}
lean_ctor_set(x_585, 0, x_575);
lean_ctor_set(x_585, 1, x_576);
lean_ctor_set(x_585, 2, x_577);
lean_ctor_set(x_585, 3, x_578);
lean_ctor_set(x_585, 4, x_584);
lean_ctor_set(x_585, 5, x_579);
x_586 = lean_unbox(x_574);
lean_dec(x_574);
x_542 = x_586;
x_543 = x_585;
goto block_556;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; uint8_t x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_587 = lean_ctor_get(x_571, 1);
lean_inc(x_587);
x_588 = lean_ctor_get(x_587, 4);
lean_inc(x_588);
x_589 = lean_ctor_get(x_571, 0);
lean_inc(x_589);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_590 = x_571;
} else {
 lean_dec_ref(x_571);
 x_590 = lean_box(0);
}
x_591 = lean_ctor_get(x_587, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_587, 1);
lean_inc(x_592);
x_593 = lean_ctor_get(x_587, 2);
lean_inc(x_593);
x_594 = lean_ctor_get(x_587, 3);
lean_inc(x_594);
x_595 = lean_ctor_get(x_587, 5);
lean_inc(x_595);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 lean_ctor_release(x_587, 2);
 lean_ctor_release(x_587, 3);
 lean_ctor_release(x_587, 4);
 lean_ctor_release(x_587, 5);
 x_596 = x_587;
} else {
 lean_dec_ref(x_587);
 x_596 = lean_box(0);
}
x_597 = lean_ctor_get(x_588, 0);
lean_inc(x_597);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 x_598 = x_588;
} else {
 lean_dec_ref(x_588);
 x_598 = lean_box(0);
}
x_599 = 0;
if (lean_is_scalar(x_598)) {
 x_600 = lean_alloc_ctor(0, 1, 1);
} else {
 x_600 = x_598;
}
lean_ctor_set(x_600, 0, x_597);
lean_ctor_set_uint8(x_600, sizeof(void*)*1, x_599);
if (lean_is_scalar(x_596)) {
 x_601 = lean_alloc_ctor(0, 6, 0);
} else {
 x_601 = x_596;
}
lean_ctor_set(x_601, 0, x_591);
lean_ctor_set(x_601, 1, x_592);
lean_ctor_set(x_601, 2, x_593);
lean_ctor_set(x_601, 3, x_594);
lean_ctor_set(x_601, 4, x_600);
lean_ctor_set(x_601, 5, x_595);
if (lean_is_scalar(x_590)) {
 x_602 = lean_alloc_ctor(1, 2, 0);
} else {
 x_602 = x_590;
}
lean_ctor_set(x_602, 0, x_589);
lean_ctor_set(x_602, 1, x_601);
return x_602;
}
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_603 = l___private_Init_Lean_Meta_InferType_1__inferAppType___closed__1;
x_604 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
x_605 = l___private_Init_Lean_Trace_2__getResetTraces___rarg(x_603, x_604);
lean_inc(x_6);
x_606 = lean_apply_2(x_605, x_6, x_558);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
lean_inc(x_6);
x_609 = l_Lean_Meta_try(x_24, x_6, x_608);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_612 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
lean_inc(x_607);
x_613 = l___private_Init_Lean_Trace_1__addNode___rarg(x_604, x_607, x_612);
lean_inc(x_6);
x_614 = lean_apply_2(x_613, x_6, x_611);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; uint8_t x_616; 
lean_dec(x_607);
x_615 = lean_ctor_get(x_614, 1);
lean_inc(x_615);
lean_dec(x_614);
x_616 = lean_unbox(x_610);
lean_dec(x_610);
x_542 = x_616;
x_543 = x_615;
goto block_556;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_dec(x_610);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_617 = lean_ctor_get(x_614, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_614, 1);
lean_inc(x_618);
lean_dec(x_614);
x_619 = l___private_Init_Lean_Trace_1__addNode___rarg(x_604, x_607, x_612);
x_620 = lean_apply_2(x_619, x_6, x_618);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_621 = lean_ctor_get(x_620, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_622 = x_620;
} else {
 lean_dec_ref(x_620);
 x_622 = lean_box(0);
}
if (lean_is_scalar(x_622)) {
 x_623 = lean_alloc_ctor(1, 2, 0);
} else {
 x_623 = x_622;
 lean_ctor_set_tag(x_623, 1);
}
lean_ctor_set(x_623, 0, x_617);
lean_ctor_set(x_623, 1, x_621);
return x_623;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
lean_dec(x_617);
x_624 = lean_ctor_get(x_620, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_620, 1);
lean_inc(x_625);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_626 = x_620;
} else {
 lean_dec_ref(x_620);
 x_626 = lean_box(0);
}
if (lean_is_scalar(x_626)) {
 x_627 = lean_alloc_ctor(1, 2, 0);
} else {
 x_627 = x_626;
}
lean_ctor_set(x_627, 0, x_624);
lean_ctor_set(x_627, 1, x_625);
return x_627;
}
}
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_628 = lean_ctor_get(x_609, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_609, 1);
lean_inc(x_629);
lean_dec(x_609);
x_630 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2;
x_631 = l___private_Init_Lean_Trace_1__addNode___rarg(x_604, x_607, x_630);
x_632 = lean_apply_2(x_631, x_6, x_629);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_632, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_634 = x_632;
} else {
 lean_dec_ref(x_632);
 x_634 = lean_box(0);
}
if (lean_is_scalar(x_634)) {
 x_635 = lean_alloc_ctor(1, 2, 0);
} else {
 x_635 = x_634;
 lean_ctor_set_tag(x_635, 1);
}
lean_ctor_set(x_635, 0, x_628);
lean_ctor_set(x_635, 1, x_633);
return x_635;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_628);
x_636 = lean_ctor_get(x_632, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_632, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_638 = x_632;
} else {
 lean_dec_ref(x_632);
 x_638 = lean_box(0);
}
if (lean_is_scalar(x_638)) {
 x_639 = lean_alloc_ctor(1, 2, 0);
} else {
 x_639 = x_638;
}
lean_ctor_set(x_639, 0, x_636);
lean_ctor_set(x_639, 1, x_637);
return x_639;
}
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_640 = lean_ctor_get(x_606, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_606, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_642 = x_606;
} else {
 lean_dec_ref(x_606);
 x_642 = lean_box(0);
}
if (lean_is_scalar(x_642)) {
 x_643 = lean_alloc_ctor(1, 2, 0);
} else {
 x_643 = x_642;
}
lean_ctor_set(x_643, 0, x_640);
lean_ctor_set(x_643, 1, x_641);
return x_643;
}
}
}
}
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec(x_510);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_887 = lean_ctor_get(x_512, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_512, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_889 = x_512;
} else {
 lean_dec_ref(x_512);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(1, 2, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_887);
lean_ctor_set(x_890, 1, x_888);
return x_890;
}
}
}
else
{
uint8_t x_891; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_891 = !lean_is_exclusive(x_25);
if (x_891 == 0)
{
return x_25;
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_892 = lean_ctor_get(x_25, 0);
x_893 = lean_ctor_get(x_25, 1);
lean_inc(x_893);
lean_inc(x_892);
lean_dec(x_25);
x_894 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_894, 0, x_892);
lean_ctor_set(x_894, 1, x_893);
return x_894;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__1(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__5(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
lean_object* initialize_Init_Lean_Meta_WHNF(lean_object*);
lean_object* initialize_Init_Lean_Meta_InferType(lean_object*);
lean_object* initialize_Init_Lean_Meta_FunInfo(lean_object*);
lean_object* initialize_Init_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Init_Lean_Meta_Check(lean_object*);
lean_object* initialize_Init_Lean_Meta_Offset(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_ExprDefEq(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_InferType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_FunInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Check(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Offset(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1);
l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1 = _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1();
lean_mark_persistent(l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1);
l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2 = _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2();
lean_mark_persistent(l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2);
l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3 = _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3();
lean_mark_persistent(l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3);
l_Lean_Meta_CheckAssignment_Lean_MonadCache = _init_l_Lean_Meta_CheckAssignment_Lean_MonadCache();
lean_mark_persistent(l_Lean_Meta_CheckAssignment_Lean_MonadCache);
l_Lean_Meta_CheckAssignment_check___main___closed__1 = _init_l_Lean_Meta_CheckAssignment_check___main___closed__1();
lean_mark_persistent(l_Lean_Meta_CheckAssignment_check___main___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__2 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__2);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__3 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__3);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__4 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__4();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__4);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__5 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__5();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__5);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__6 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__6();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__6);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__7 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__7();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__7);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__8 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__8();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__8);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__9 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__9();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__9);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__11 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__11();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__11);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__12 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__12();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__12);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__13 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__13();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__13);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__14 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__14();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__14);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__16 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__16();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__16);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__17 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__17();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__17);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__18 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__18();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__18);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__19 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__19();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__19);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__20 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__20();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__20);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__21 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__21();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__21);
l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__22 = _init_l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__22();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__22);
l_Lean_Meta_checkAssignment___closed__1 = _init_l_Lean_Meta_checkAssignment___closed__1();
lean_mark_persistent(l_Lean_Meta_checkAssignment___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__2 = _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__2);
l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3 = _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3);
l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4 = _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4);
l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__5 = _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__5);
l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__6 = _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__6);
l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7 = _init_l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7);
l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__2___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__3___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__7___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__7___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___lambda__7___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__1 = _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__1);
l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2 = _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__2);
l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3 = _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__3);
l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__4 = _init_l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__4();
lean_mark_persistent(l___private_Init_Lean_Meta_ExprDefEq_19__isDefEqDelta___closed__4);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Init.Lean.Meta.ExprDefEq
// Imports: Init.Lean.Meta.WHNF Init.Lean.Meta.InferType Init.Lean.Meta.FunInfo Init.Lean.Meta.LevelDefEq
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
lean_object* l_Lean_Meta_inferTypeAuxAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__12;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_beq___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_checkMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4;
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoAuxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_cache(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__2;
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_mkAuxMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Meta_CheckAssignment_cache___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_13__simpAssignmentArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__3;
lean_object* l_HashMapImp_insert___at_Lean_Meta_CheckAssignment_cache___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__22;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__simpAssignmentArgAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__7;
lean_object* l_Lean_Meta_CheckAssignment_getMCtx___rarg(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__20;
lean_object* l_mkHashMap___at_Lean_Meta_checkAssignment___spec__2(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_15__processAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__5;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_check___main___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_CheckAssignment_cache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_usingDefault(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Id_Monad;
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_CheckAssignment_cache___spec__5(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__17;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__13;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_mkAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkAssignment___closed__1;
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache;
lean_object* l_Lean_Meta_isDefEqBindingDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Meta_CheckAssignment_findCached___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__6;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__11;
lean_object* l_AssocList_contains___main___at_Lean_Meta_CheckAssignment_cache___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFVar(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect___rarg(lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_InferType_1__getForallResultType___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__5;
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Meta_CheckAssignment_findCached___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_simpleMonadTracerAdapter___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Meta_CheckAssignment_cache___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__21;
lean_object* l_Lean_Meta_CheckAssignment_getMCtx___boxed(lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_check___main(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isEtaUnassignedMVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateApp_x21___closed__1;
lean_object* lean_metavar_ctx_assign_expr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__processAssignmentFOApproxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_ParamInfo_inhabited;
extern lean_object* l_Lean_Expr_updateLet_x21___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tracer;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__8;
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__processAssignmentFOApproxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_Meta_CheckAssignment_cache___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_MessageData_coeOfArrayExpr___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_findCached___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Meta_CheckAssignment_findCached___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__6;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_12__simpAssignmentArgAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__1;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticExprMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__18;
lean_object* l___private_Init_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_LevelDefEq_13__restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_checkFVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_checkAssignment___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__2;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_checkAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferTypeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__2;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7;
lean_object* l_Lean_Meta_CheckAssignment_findCached(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__9;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3;
lean_object* l_Lean_Meta_isDefEqBindingDomain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
lean_object* lean_metavar_ctx_mk_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__19;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__2;
lean_object* l_Lean_Meta_CheckAssignment_getMCtx(lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Meta_CheckAssignment_findCached___spec__1(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__14;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_check(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateProj_x21___closed__2;
extern lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Meta_isEtaUnassignedMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqBindingDomain___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__16;
lean_object* l_Lean_Meta_CheckAssignment_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_9__etaExpandedAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_7__visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_isWellFormed___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Meta_isDefEqBindingDomain___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__4;
lean_object* l___private_Init_Lean_Meta_LevelDefEq_12__processPostponed(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
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
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_46; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
x_36 = lean_ctor_get(x_24, 5);
x_37 = l_PersistentArray_empty___closed__3;
lean_inc(x_35);
lean_inc(x_34);
lean_ctor_set(x_24, 5, x_37);
lean_inc(x_5);
x_46 = lean_apply_4(x_2, x_3, x_32, x_5, x_24);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_34, x_35, x_36, x_5, x_49);
lean_dec(x_5);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_47);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; 
lean_dec(x_47);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = 0;
x_57 = l___private_Init_Lean_Meta_LevelDefEq_12__processPostponed(x_56, x_5, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_34, x_35, x_36, x_5, x_60);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_58);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_5);
x_66 = !lean_is_exclusive(x_57);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_57, 0);
lean_dec(x_67);
return x_57;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_57, 1);
lean_inc(x_68);
lean_dec(x_57);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_57, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_57, 1);
lean_inc(x_71);
lean_dec(x_57);
x_38 = x_70;
x_39 = x_71;
goto block_45;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_46, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_46, 1);
lean_inc(x_73);
lean_dec(x_46);
x_38 = x_72;
x_39 = x_73;
goto block_45;
}
block_45:
{
lean_object* x_40; uint8_t x_41; 
x_40 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_34, x_35, x_36, x_5, x_39);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_89; 
x_74 = lean_ctor_get(x_24, 0);
x_75 = lean_ctor_get(x_24, 1);
x_76 = lean_ctor_get(x_24, 2);
x_77 = lean_ctor_get(x_24, 3);
x_78 = lean_ctor_get(x_24, 4);
x_79 = lean_ctor_get(x_24, 5);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_24);
x_80 = l_PersistentArray_empty___closed__3;
lean_inc(x_75);
lean_inc(x_74);
x_81 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_80);
lean_inc(x_5);
x_89 = lean_apply_4(x_2, x_3, x_32, x_5, x_81);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_74, x_75, x_79, x_5, x_92);
lean_dec(x_5);
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
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
else
{
lean_object* x_97; uint8_t x_98; lean_object* x_99; 
lean_dec(x_90);
x_97 = lean_ctor_get(x_89, 1);
lean_inc(x_97);
lean_dec(x_89);
x_98 = 0;
x_99 = l___private_Init_Lean_Meta_LevelDefEq_12__processPostponed(x_98, x_5, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_74, x_75, x_79, x_5, x_102);
lean_dec(x_5);
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
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_5);
x_107 = lean_ctor_get(x_99, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_108 = x_99;
} else {
 lean_dec_ref(x_99);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_100);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_99, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_99, 1);
lean_inc(x_111);
lean_dec(x_99);
x_82 = x_110;
x_83 = x_111;
goto block_88;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_89, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_89, 1);
lean_inc(x_113);
lean_dec(x_89);
x_82 = x_112;
x_83 = x_113;
goto block_88;
}
block_88:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_74, x_75, x_79, x_5, x_83);
lean_dec(x_5);
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
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_22);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_22, 0);
lean_dec(x_115);
x_116 = 0;
x_117 = lean_box(x_116);
lean_ctor_set(x_22, 0, x_117);
return x_22;
}
else
{
lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_22, 1);
lean_inc(x_118);
lean_dec(x_22);
x_119 = 0;
x_120 = lean_box(x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_22);
if (x_122 == 0)
{
return x_22;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_22, 0);
x_124 = lean_ctor_get(x_22, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_22);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_126 = lean_ctor_get(x_14, 0);
x_127 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_128 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 1);
x_129 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 2);
x_130 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 3);
lean_inc(x_126);
lean_dec(x_14);
x_131 = 1;
x_132 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_132, 0, x_126);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_127);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 1, x_128);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 2, x_129);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 3, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 4, x_131);
x_133 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_17);
lean_ctor_set(x_133, 2, x_18);
x_134 = lean_apply_3(x_1, x_15, x_133, x_16);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 7)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint64_t x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_161; 
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 2);
lean_inc(x_139);
x_140 = lean_ctor_get_uint64(x_135, sizeof(void*)*3);
lean_dec(x_135);
x_141 = (uint8_t)((x_140 << 24) >> 61);
x_142 = l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1;
x_143 = l_Lean_mkApp(x_139, x_142);
x_144 = l_Lean_mkLambda(x_137, x_141, x_138, x_143);
x_145 = lean_ctor_get(x_136, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_136, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_136, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_136, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_136, 4);
lean_inc(x_149);
x_150 = lean_ctor_get(x_136, 5);
lean_inc(x_150);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 lean_ctor_release(x_136, 3);
 lean_ctor_release(x_136, 4);
 lean_ctor_release(x_136, 5);
 x_151 = x_136;
} else {
 lean_dec_ref(x_136);
 x_151 = lean_box(0);
}
x_152 = l_PersistentArray_empty___closed__3;
lean_inc(x_146);
lean_inc(x_145);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 6, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_145);
lean_ctor_set(x_153, 1, x_146);
lean_ctor_set(x_153, 2, x_147);
lean_ctor_set(x_153, 3, x_148);
lean_ctor_set(x_153, 4, x_149);
lean_ctor_set(x_153, 5, x_152);
lean_inc(x_5);
x_161 = lean_apply_4(x_2, x_3, x_144, x_5, x_153);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_unbox(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
x_165 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_145, x_146, x_150, x_5, x_164);
lean_dec(x_5);
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
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
else
{
lean_object* x_169; uint8_t x_170; lean_object* x_171; 
lean_dec(x_162);
x_169 = lean_ctor_get(x_161, 1);
lean_inc(x_169);
lean_dec(x_161);
x_170 = 0;
x_171 = l___private_Init_Lean_Meta_LevelDefEq_12__processPostponed(x_170, x_5, x_169);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_145, x_146, x_150, x_5, x_174);
lean_dec(x_5);
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
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_150);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_5);
x_179 = lean_ctor_get(x_171, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_180 = x_171;
} else {
 lean_dec_ref(x_171);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_172);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_171, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_171, 1);
lean_inc(x_183);
lean_dec(x_171);
x_154 = x_182;
x_155 = x_183;
goto block_160;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_161, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_161, 1);
lean_inc(x_185);
lean_dec(x_161);
x_154 = x_184;
x_155 = x_185;
goto block_160;
}
block_160:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_145, x_146, x_150, x_5, x_155);
lean_dec(x_5);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
 lean_ctor_set_tag(x_159, 1);
}
lean_ctor_set(x_159, 0, x_154);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_135);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_186 = lean_ctor_get(x_134, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_187 = x_134;
} else {
 lean_dec_ref(x_134);
 x_187 = lean_box(0);
}
x_188 = 0;
x_189 = lean_box(x_188);
if (lean_is_scalar(x_187)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_187;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_186);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_191 = lean_ctor_get(x_134, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_134, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_193 = x_134;
} else {
 lean_dec_ref(x_134);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_13);
if (x_195 == 0)
{
return x_13;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_13, 0);
x_197 = lean_ctor_get(x_13, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_13);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_199 = 0;
x_200 = lean_box(x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_6);
return x_201;
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
x_39 = l___private_Init_Lean_Meta_InferType_1__getForallResultType___closed__1;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_fget(x_3, x_5);
x_13 = l_Lean_Expr_fvarId_x21(x_12);
lean_inc(x_7);
x_14 = l_Lean_Meta_getLocalDecl(x_13, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_LocalDecl_type(x_15);
lean_dec(x_15);
x_18 = l_Lean_Expr_Inhabited;
x_19 = lean_array_get(x_18, x_4, x_5);
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_17);
x_20 = lean_apply_4(x_2, x_17, x_19, x_7, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_1);
x_28 = l_Lean_Meta_isClass(x_1, x_17, x_7, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_5, x_31);
lean_dec(x_5);
x_5 = x_32;
x_8 = x_30;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_5, x_36);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_7);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_7, 2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_12);
x_41 = lean_array_push(x_39, x_40);
lean_ctor_set(x_7, 2, x_41);
x_5 = x_37;
x_8 = x_34;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get(x_7, 1);
x_45 = lean_ctor_get(x_7, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_7);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_12);
x_47 = lean_array_push(x_45, x_46);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_47);
x_5 = x_37;
x_7 = x_48;
x_8 = x_34;
goto _start;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_28);
if (x_50 == 0)
{
return x_28;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_28, 0);
x_52 = lean_ctor_get(x_28, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_28);
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
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_20);
if (x_54 == 0)
{
return x_20;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_14);
if (x_58 == 0)
{
return x_14;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_14, 0);
x_60 = lean_ctor_get(x_14, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_14);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
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
x_9 = l_Lean_Name_beq___main(x_5, x_8);
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
x_1 = l___private_Init_Lean_Meta_InferType_1__getForallResultType___closed__1;
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
x_131 = l_Lean_Name_beq___main(x_127, x_130);
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
x_191 = l_Lean_Name_beq___main(x_187, x_190);
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
x_26 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_3);
x_31 = lean_alloc_ctor(7, 2, 0);
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
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_mkMVar(x_1);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Array_umapMAux___main___at_Lean_MessageData_coeOfArrayExpr___spec__1(x_54, x_2);
x_56 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_3);
x_61 = lean_alloc_ctor(7, 2, 0);
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
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_mkMVar(x_1);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Array_umapMAux___main___at_Lean_MessageData_coeOfArrayExpr___spec__1(x_91, x_2);
x_93 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
x_95 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_3);
x_98 = lean_alloc_ctor(7, 2, 0);
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
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_mkMVar(x_1);
x_126 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Array_umapMAux___main___at_Lean_MessageData_coeOfArrayExpr___spec__1(x_128, x_2);
x_130 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_130);
x_132 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_134, 0, x_3);
x_135 = lean_alloc_ctor(7, 2, 0);
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
uint8_t x_9; lean_object* x_10; uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
x_23 = lean_ctor_get(x_8, 5);
x_32 = l_PersistentArray_empty___closed__3;
lean_inc(x_22);
lean_inc(x_21);
lean_ctor_set(x_8, 5, x_32);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_33 = l___private_Init_Lean_Meta_ExprDefEq_10__processAssignmentFOApproxAux(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_21, x_22, x_23, x_7, x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_unbox(x_34);
lean_dec(x_34);
x_9 = x_39;
x_10 = x_38;
goto block_19;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_dec(x_34);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
x_41 = 0;
x_42 = l___private_Init_Lean_Meta_LevelDefEq_12__processPostponed(x_41, x_7, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_21, x_22, x_23, x_7, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_unbox(x_43);
lean_dec(x_43);
x_9 = x_48;
x_10 = x_47;
goto block_19;
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_unbox(x_43);
lean_dec(x_43);
x_9 = x_50;
x_10 = x_49;
goto block_19;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_dec(x_42);
x_24 = x_51;
x_25 = x_52;
goto block_31;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_33, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_33, 1);
lean_inc(x_54);
lean_dec(x_33);
x_24 = x_53;
x_25 = x_54;
goto block_31;
}
block_31:
{
lean_object* x_26; uint8_t x_27; 
x_26 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_21, x_22, x_23, x_7, x_25);
lean_dec(x_7);
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
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_8, 0);
x_56 = lean_ctor_get(x_8, 1);
x_57 = lean_ctor_get(x_8, 2);
x_58 = lean_ctor_get(x_8, 3);
x_59 = lean_ctor_get(x_8, 4);
x_60 = lean_ctor_get(x_8, 5);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_8);
x_68 = l_PersistentArray_empty___closed__3;
lean_inc(x_56);
lean_inc(x_55);
x_69 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_69, 0, x_55);
lean_ctor_set(x_69, 1, x_56);
lean_ctor_set(x_69, 2, x_57);
lean_ctor_set(x_69, 3, x_58);
lean_ctor_set(x_69, 4, x_59);
lean_ctor_set(x_69, 5, x_68);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_70 = l___private_Init_Lean_Meta_ExprDefEq_10__processAssignmentFOApproxAux(x_2, x_4, x_5, x_6, x_7, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_55, x_56, x_60, x_7, x_73);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_unbox(x_71);
lean_dec(x_71);
x_9 = x_76;
x_10 = x_75;
goto block_19;
}
else
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; 
lean_dec(x_71);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_dec(x_70);
x_78 = 0;
x_79 = l___private_Init_Lean_Meta_LevelDefEq_12__processPostponed(x_78, x_7, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_55, x_56, x_60, x_7, x_82);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_unbox(x_80);
lean_dec(x_80);
x_9 = x_85;
x_10 = x_84;
goto block_19;
}
else
{
lean_object* x_86; uint8_t x_87; 
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_55);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = lean_unbox(x_80);
lean_dec(x_80);
x_9 = x_87;
x_10 = x_86;
goto block_19;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_ctor_get(x_79, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_79, 1);
lean_inc(x_89);
lean_dec(x_79);
x_61 = x_88;
x_62 = x_89;
goto block_67;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_ctor_get(x_70, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_70, 1);
lean_inc(x_91);
lean_dec(x_70);
x_61 = x_90;
x_62 = x_91;
goto block_67;
}
block_67:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_55, x_56, x_60, x_7, x_62);
lean_dec(x_7);
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
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
 lean_ctor_set_tag(x_66, 1);
}
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
block_19:
{
if (x_9 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_inferTypeAux), 4, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_EIO_Monad___closed__1;
x_13 = lean_box(x_9);
x_14 = lean_alloc_closure((void*)(l_ReaderT_pure___rarg___boxed), 4, 3);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, x_13);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main), 8, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
x_16 = l_Lean_Meta_unfoldDefinitionAux___rarg(x_1, x_11, x_2, x_3, x_6, x_14, x_15, x_7, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
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
lean_object* l_Lean_Meta_isTypeCorrect___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_isTypeCorrect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_isTypeCorrect___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_Meta_isTypeCorrect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_isTypeCorrect(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
uint8_t l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__1(lean_object* x_1, lean_object* x_2) {
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
x_2 = l___private_Init_Lean_Meta_InferType_1__getForallResultType___closed__1;
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
lean_dec(x_11);
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
lean_object* x_236; 
x_236 = lean_box(0);
x_20 = x_236;
goto block_235;
}
else
{
uint8_t x_237; 
x_237 = l_Array_isEmpty___rarg(x_8);
if (x_237 == 0)
{
lean_object* x_238; 
x_238 = lean_box(0);
x_20 = x_238;
goto block_235;
}
else
{
lean_object* x_239; uint8_t x_240; 
x_239 = l_Lean_Expr_getAppFn___main(x_17);
x_240 = lean_expr_eqv(x_239, x_4);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; 
x_241 = lean_box(0);
x_20 = x_241;
goto block_235;
}
else
{
lean_object* x_242; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_242 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_8, x_17, x_9, x_18);
return x_242;
}
}
}
block_235:
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
lean_dec(x_17);
lean_dec(x_3);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
lean_inc(x_9);
x_36 = l_Lean_Meta_mkLambda(x_8, x_35, x_9, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_usingDefault), 4, 1);
lean_closure_set(x_39, 0, x_1);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_39);
x_40 = l_Lean_Meta_inferTypeAuxAux___main(x_39, x_4, x_9, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_37);
x_43 = l_Lean_Meta_inferTypeAuxAux___main(x_39, x_37, x_9, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_47 = 1;
lean_ctor_set_uint8(x_13, sizeof(void*)*1 + 4, x_47);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_13);
lean_ctor_set(x_48, 1, x_14);
lean_ctor_set(x_48, 2, x_15);
lean_inc(x_44);
lean_inc(x_41);
x_49 = lean_apply_4(x_2, x_41, x_44, x_48, x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_21);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_49, 1);
x_54 = lean_ctor_get(x_49, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_53, 4);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_55, sizeof(void*)*1);
lean_dec(x_55);
if (x_56 == 0)
{
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_49);
x_57 = l___private_Init_Lean_Meta_InferType_1__getForallResultType___closed__1;
x_58 = l_Lean_Meta_tracer;
x_59 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4;
x_60 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_57, x_58, x_59);
lean_inc(x_9);
x_61 = lean_apply_2(x_60, x_9, x_53);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
uint8_t x_64; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_61, 0);
lean_dec(x_65);
lean_ctor_set(x_61, 0, x_50);
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_dec(x_61);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_50);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_4);
x_70 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_41);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_76, 0, x_37);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_70);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_44);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
x_82 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3;
x_83 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_81, x_82, x_80);
x_84 = lean_apply_2(x_83, x_9, x_68);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
lean_ctor_set(x_84, 0, x_50);
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_50);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_50);
x_89 = !lean_is_exclusive(x_84);
if (x_89 == 0)
{
return x_84;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_84, 0);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_84);
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
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_93 = !lean_is_exclusive(x_61);
if (x_93 == 0)
{
return x_61;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_61, 0);
x_95 = lean_ctor_get(x_61, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_61);
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
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_49, 1);
lean_inc(x_97);
lean_dec(x_49);
x_98 = lean_ctor_get(x_97, 4);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_98, sizeof(void*)*1);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_50);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = l___private_Init_Lean_Meta_InferType_1__getForallResultType___closed__1;
x_102 = l_Lean_Meta_tracer;
x_103 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4;
x_104 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_101, x_102, x_103);
lean_inc(x_9);
x_105 = lean_apply_2(x_104, x_9, x_97);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_109 = x_105;
} else {
 lean_dec_ref(x_105);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_50);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_dec(x_105);
x_112 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_112, 0, x_4);
x_113 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7;
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_115, 0, x_41);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_119, 0, x_37);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_113);
x_122 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_122, 0, x_44);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
x_125 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3;
x_126 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_124, x_125, x_123);
x_127 = lean_apply_2(x_126, x_9, x_111);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_50);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_50);
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_133 = x_127;
} else {
 lean_dec_ref(x_127);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_135 = lean_ctor_get(x_105, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_105, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_137 = x_105;
} else {
 lean_dec_ref(x_105);
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
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_4);
x_139 = lean_ctor_get(x_49, 1);
lean_inc(x_139);
lean_dec(x_49);
x_140 = l_Lean_Meta_assignExprMVar(x_21, x_37, x_9, x_139);
lean_dec(x_9);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_140, 0);
lean_dec(x_142);
lean_ctor_set(x_140, 0, x_50);
return x_140;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_50);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
else
{
uint8_t x_145; 
lean_dec(x_50);
x_145 = !lean_is_exclusive(x_140);
if (x_145 == 0)
{
return x_140;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_140, 0);
x_147 = lean_ctor_get(x_140, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_140);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_49);
if (x_149 == 0)
{
return x_49;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_49, 0);
x_151 = lean_ctor_get(x_49, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_49);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
lean_object* x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_153 = lean_ctor_get(x_13, 0);
x_154 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 1);
x_155 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 2);
x_156 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 3);
lean_inc(x_153);
lean_dec(x_13);
x_157 = 1;
x_158 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set_uint8(x_158, sizeof(void*)*1, x_19);
lean_ctor_set_uint8(x_158, sizeof(void*)*1 + 1, x_154);
lean_ctor_set_uint8(x_158, sizeof(void*)*1 + 2, x_155);
lean_ctor_set_uint8(x_158, sizeof(void*)*1 + 3, x_156);
lean_ctor_set_uint8(x_158, sizeof(void*)*1 + 4, x_157);
x_159 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_14);
lean_ctor_set(x_159, 2, x_15);
lean_inc(x_44);
lean_inc(x_41);
x_160 = lean_apply_4(x_2, x_41, x_44, x_159, x_45);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_dec(x_21);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_164 = x_160;
} else {
 lean_dec_ref(x_160);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_163, 4);
lean_inc(x_165);
x_166 = lean_ctor_get_uint8(x_165, sizeof(void*)*1);
lean_dec(x_165);
if (x_166 == 0)
{
lean_object* x_167; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_163);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_164);
x_168 = l___private_Init_Lean_Meta_InferType_1__getForallResultType___closed__1;
x_169 = l_Lean_Meta_tracer;
x_170 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__4;
x_171 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_168, x_169, x_170);
lean_inc(x_9);
x_172 = lean_apply_2(x_171, x_9, x_163);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_unbox(x_173);
lean_dec(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_176 = x_172;
} else {
 lean_dec_ref(x_172);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_161);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_178 = lean_ctor_get(x_172, 1);
lean_inc(x_178);
lean_dec(x_172);
x_179 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_179, 0, x_4);
x_180 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__7;
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_182, 0, x_41);
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_186, 0, x_37);
x_187 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_180);
x_189 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_189, 0, x_44);
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__1;
x_192 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___closed__3;
x_193 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_191, x_192, x_190);
x_194 = lean_apply_2(x_193, x_9, x_178);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
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
lean_ctor_set(x_197, 0, x_161);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_161);
x_198 = lean_ctor_get(x_194, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_200 = x_194;
} else {
 lean_dec_ref(x_194);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_161);
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_4);
x_202 = lean_ctor_get(x_172, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_172, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_204 = x_172;
} else {
 lean_dec_ref(x_172);
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
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_4);
x_206 = lean_ctor_get(x_160, 1);
lean_inc(x_206);
lean_dec(x_160);
x_207 = l_Lean_Meta_assignExprMVar(x_21, x_37, x_9, x_206);
lean_dec(x_9);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_161);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_161);
x_211 = lean_ctor_get(x_207, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_207, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_213 = x_207;
} else {
 lean_dec_ref(x_207);
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
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_4);
x_215 = lean_ctor_get(x_160, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_160, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_217 = x_160;
} else {
 lean_dec_ref(x_160);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_219 = !lean_is_exclusive(x_43);
if (x_219 == 0)
{
return x_43;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_43, 0);
x_221 = lean_ctor_get(x_43, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_43);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
else
{
uint8_t x_223; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_223 = !lean_is_exclusive(x_40);
if (x_223 == 0)
{
return x_40;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_40, 0);
x_225 = lean_ctor_get(x_40, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_40);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
else
{
uint8_t x_227; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_227 = !lean_is_exclusive(x_36);
if (x_227 == 0)
{
return x_36;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_36, 0);
x_229 = lean_ctor_get(x_36, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_36);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_22);
if (x_231 == 0)
{
return x_22;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_22, 0);
x_233 = lean_ctor_get(x_22, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_22);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_9, 0);
lean_inc(x_243);
x_244 = lean_array_fget(x_8, x_7);
lean_inc(x_9);
x_245 = l___private_Init_Lean_Meta_ExprDefEq_13__simpAssignmentArg(x_244, x_9, x_10);
if (lean_obj_tag(x_245) == 0)
{
uint8_t x_246; 
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_245, 0);
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
x_249 = lean_array_fset(x_8, x_7, x_247);
if (lean_obj_tag(x_247) == 1)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_250 = lean_ctor_get(x_247, 0);
lean_inc(x_250);
x_251 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_251, 0, x_247);
x_252 = lean_array_get_size(x_249);
x_253 = lean_nat_dec_le(x_7, x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_254 = l_Id_Monad;
x_255 = lean_unsigned_to_nat(0u);
lean_inc(x_249);
x_256 = l_Array_anyRangeMAux___main___rarg(x_254, x_249, x_252, lean_box(0), x_251, x_255);
x_257 = lean_unbox(x_256);
lean_dec(x_256);
if (x_257 == 0)
{
lean_object* x_258; uint8_t x_259; 
x_258 = lean_ctor_get(x_5, 1);
x_259 = l_Lean_LocalContext_contains(x_258, x_250);
lean_dec(x_250);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; 
lean_free_object(x_245);
lean_dec(x_243);
x_260 = lean_unsigned_to_nat(1u);
x_261 = lean_nat_add(x_7, x_260);
lean_dec(x_7);
x_7 = x_261;
x_8 = x_249;
x_10 = x_248;
goto _start;
}
else
{
uint8_t x_263; 
x_263 = lean_ctor_get_uint8(x_243, sizeof(void*)*1 + 2);
if (x_263 == 0)
{
uint8_t x_264; 
lean_dec(x_7);
x_264 = lean_ctor_get_uint8(x_243, sizeof(void*)*1);
lean_dec(x_243);
if (x_264 == 0)
{
uint8_t x_265; lean_object* x_266; 
lean_dec(x_249);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_265 = 0;
x_266 = lean_box(x_265);
lean_ctor_set(x_245, 0, x_266);
return x_245;
}
else
{
lean_object* x_267; 
lean_free_object(x_245);
x_267 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_249, x_6, x_9, x_248);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_free_object(x_245);
lean_dec(x_243);
x_268 = lean_unsigned_to_nat(1u);
x_269 = lean_nat_add(x_7, x_268);
lean_dec(x_7);
x_7 = x_269;
x_8 = x_249;
x_10 = x_248;
goto _start;
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_250);
lean_dec(x_7);
x_271 = lean_ctor_get_uint8(x_243, sizeof(void*)*1);
lean_dec(x_243);
if (x_271 == 0)
{
uint8_t x_272; lean_object* x_273; 
lean_dec(x_249);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_272 = 0;
x_273 = lean_box(x_272);
lean_ctor_set(x_245, 0, x_273);
return x_245;
}
else
{
lean_object* x_274; 
lean_free_object(x_245);
x_274 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_249, x_6, x_9, x_248);
return x_274;
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
lean_dec(x_252);
x_275 = l_Id_Monad;
x_276 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_249);
x_277 = l_Array_anyRangeMAux___main___rarg(x_275, x_249, x_7, lean_box(0), x_251, x_276);
x_278 = lean_unbox(x_277);
lean_dec(x_277);
if (x_278 == 0)
{
lean_object* x_279; uint8_t x_280; 
x_279 = lean_ctor_get(x_5, 1);
x_280 = l_Lean_LocalContext_contains(x_279, x_250);
lean_dec(x_250);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; 
lean_free_object(x_245);
lean_dec(x_243);
x_281 = lean_unsigned_to_nat(1u);
x_282 = lean_nat_add(x_7, x_281);
lean_dec(x_7);
x_7 = x_282;
x_8 = x_249;
x_10 = x_248;
goto _start;
}
else
{
uint8_t x_284; 
x_284 = lean_ctor_get_uint8(x_243, sizeof(void*)*1 + 2);
if (x_284 == 0)
{
uint8_t x_285; 
lean_dec(x_7);
x_285 = lean_ctor_get_uint8(x_243, sizeof(void*)*1);
lean_dec(x_243);
if (x_285 == 0)
{
uint8_t x_286; lean_object* x_287; 
lean_dec(x_249);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_286 = 0;
x_287 = lean_box(x_286);
lean_ctor_set(x_245, 0, x_287);
return x_245;
}
else
{
lean_object* x_288; 
lean_free_object(x_245);
x_288 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_249, x_6, x_9, x_248);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; 
lean_free_object(x_245);
lean_dec(x_243);
x_289 = lean_unsigned_to_nat(1u);
x_290 = lean_nat_add(x_7, x_289);
lean_dec(x_7);
x_7 = x_290;
x_8 = x_249;
x_10 = x_248;
goto _start;
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_250);
lean_dec(x_7);
x_292 = lean_ctor_get_uint8(x_243, sizeof(void*)*1);
lean_dec(x_243);
if (x_292 == 0)
{
uint8_t x_293; lean_object* x_294; 
lean_dec(x_249);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_293 = 0;
x_294 = lean_box(x_293);
lean_ctor_set(x_245, 0, x_294);
return x_245;
}
else
{
lean_object* x_295; 
lean_free_object(x_245);
x_295 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_249, x_6, x_9, x_248);
return x_295;
}
}
}
}
else
{
uint8_t x_296; 
lean_dec(x_247);
lean_dec(x_7);
x_296 = lean_ctor_get_uint8(x_243, sizeof(void*)*1);
lean_dec(x_243);
if (x_296 == 0)
{
uint8_t x_297; lean_object* x_298; 
lean_dec(x_249);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = 0;
x_298 = lean_box(x_297);
lean_ctor_set(x_245, 0, x_298);
return x_245;
}
else
{
lean_object* x_299; 
lean_free_object(x_245);
x_299 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_249, x_6, x_9, x_248);
return x_299;
}
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_245, 0);
x_301 = lean_ctor_get(x_245, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_245);
lean_inc(x_300);
x_302 = lean_array_fset(x_8, x_7, x_300);
if (lean_obj_tag(x_300) == 1)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_303 = lean_ctor_get(x_300, 0);
lean_inc(x_303);
x_304 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_304, 0, x_300);
x_305 = lean_array_get_size(x_302);
x_306 = lean_nat_dec_le(x_7, x_305);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_307 = l_Id_Monad;
x_308 = lean_unsigned_to_nat(0u);
lean_inc(x_302);
x_309 = l_Array_anyRangeMAux___main___rarg(x_307, x_302, x_305, lean_box(0), x_304, x_308);
x_310 = lean_unbox(x_309);
lean_dec(x_309);
if (x_310 == 0)
{
lean_object* x_311; uint8_t x_312; 
x_311 = lean_ctor_get(x_5, 1);
x_312 = l_Lean_LocalContext_contains(x_311, x_303);
lean_dec(x_303);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_243);
x_313 = lean_unsigned_to_nat(1u);
x_314 = lean_nat_add(x_7, x_313);
lean_dec(x_7);
x_7 = x_314;
x_8 = x_302;
x_10 = x_301;
goto _start;
}
else
{
uint8_t x_316; 
x_316 = lean_ctor_get_uint8(x_243, sizeof(void*)*1 + 2);
if (x_316 == 0)
{
uint8_t x_317; 
lean_dec(x_7);
x_317 = lean_ctor_get_uint8(x_243, sizeof(void*)*1);
lean_dec(x_243);
if (x_317 == 0)
{
uint8_t x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_302);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_318 = 0;
x_319 = lean_box(x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_301);
return x_320;
}
else
{
lean_object* x_321; 
x_321 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_302, x_6, x_9, x_301);
return x_321;
}
}
else
{
lean_object* x_322; lean_object* x_323; 
lean_dec(x_243);
x_322 = lean_unsigned_to_nat(1u);
x_323 = lean_nat_add(x_7, x_322);
lean_dec(x_7);
x_7 = x_323;
x_8 = x_302;
x_10 = x_301;
goto _start;
}
}
}
else
{
uint8_t x_325; 
lean_dec(x_303);
lean_dec(x_7);
x_325 = lean_ctor_get_uint8(x_243, sizeof(void*)*1);
lean_dec(x_243);
if (x_325 == 0)
{
uint8_t x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_302);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_326 = 0;
x_327 = lean_box(x_326);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_301);
return x_328;
}
else
{
lean_object* x_329; 
x_329 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_302, x_6, x_9, x_301);
return x_329;
}
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
lean_dec(x_305);
x_330 = l_Id_Monad;
x_331 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_302);
x_332 = l_Array_anyRangeMAux___main___rarg(x_330, x_302, x_7, lean_box(0), x_304, x_331);
x_333 = lean_unbox(x_332);
lean_dec(x_332);
if (x_333 == 0)
{
lean_object* x_334; uint8_t x_335; 
x_334 = lean_ctor_get(x_5, 1);
x_335 = l_Lean_LocalContext_contains(x_334, x_303);
lean_dec(x_303);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_243);
x_336 = lean_unsigned_to_nat(1u);
x_337 = lean_nat_add(x_7, x_336);
lean_dec(x_7);
x_7 = x_337;
x_8 = x_302;
x_10 = x_301;
goto _start;
}
else
{
uint8_t x_339; 
x_339 = lean_ctor_get_uint8(x_243, sizeof(void*)*1 + 2);
if (x_339 == 0)
{
uint8_t x_340; 
lean_dec(x_7);
x_340 = lean_ctor_get_uint8(x_243, sizeof(void*)*1);
lean_dec(x_243);
if (x_340 == 0)
{
uint8_t x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_302);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_341 = 0;
x_342 = lean_box(x_341);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_301);
return x_343;
}
else
{
lean_object* x_344; 
x_344 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_302, x_6, x_9, x_301);
return x_344;
}
}
else
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_243);
x_345 = lean_unsigned_to_nat(1u);
x_346 = lean_nat_add(x_7, x_345);
lean_dec(x_7);
x_7 = x_346;
x_8 = x_302;
x_10 = x_301;
goto _start;
}
}
}
else
{
uint8_t x_348; 
lean_dec(x_303);
lean_dec(x_7);
x_348 = lean_ctor_get_uint8(x_243, sizeof(void*)*1);
lean_dec(x_243);
if (x_348 == 0)
{
uint8_t x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_302);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_349 = 0;
x_350 = lean_box(x_349);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_301);
return x_351;
}
else
{
lean_object* x_352; 
x_352 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_302, x_6, x_9, x_301);
return x_352;
}
}
}
}
else
{
uint8_t x_353; 
lean_dec(x_300);
lean_dec(x_7);
x_353 = lean_ctor_get_uint8(x_243, sizeof(void*)*1);
lean_dec(x_243);
if (x_353 == 0)
{
uint8_t x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_302);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_354 = 0;
x_355 = lean_box(x_354);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_301);
return x_356;
}
else
{
lean_object* x_357; 
x_357 = l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(x_1, x_2, x_3, x_4, x_302, x_6, x_9, x_301);
return x_357;
}
}
}
}
else
{
uint8_t x_358; 
lean_dec(x_243);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_358 = !lean_is_exclusive(x_245);
if (x_358 == 0)
{
return x_245;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_245, 0);
x_360 = lean_ctor_get(x_245, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_245);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
return x_361;
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
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
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
lean_object* l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
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
lean_dec(x_11);
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
lean_object* initialize_Init_Lean_Meta_WHNF(lean_object*);
lean_object* initialize_Init_Lean_Meta_InferType(lean_object*);
lean_object* initialize_Init_Lean_Meta_FunInfo(lean_object*);
lean_object* initialize_Init_Lean_Meta_LevelDefEq(lean_object*);
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

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
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__12;
uint8_t lean_expr_has_fvar(lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_checkMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoAuxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_cache(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_expr_hash(lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__2;
lean_object* l_Lean_Meta_CheckAssignment_mkAuxMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Meta_CheckAssignment_cache___spec__6(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__3;
lean_object* l_HashMapImp_insert___at_Lean_Meta_CheckAssignment_cache___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_1__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_Meta_checkAssignment___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__22;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__7;
lean_object* l_Lean_Meta_CheckAssignment_getMCtx___rarg(lean_object*);
lean_object* l_Array_anyMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_unfoldDefinitionAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__20;
lean_object* l_mkHashMap___at_Lean_Meta_checkAssignment___spec__2(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__5;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_6__isDefEqBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_9__isDefEqFOApprox___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_CheckAssignment_cache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_usingDefault(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_mk_fvar(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_CheckAssignment_cache___spec__5(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__17;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__13;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_mkAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkAssignment___closed__1;
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache;
lean_object* l_Lean_Meta_isDefEqBindingDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Meta_CheckAssignment_findCached___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__6;
extern lean_object* l_Lean_Expr_updateForall_x21___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getRevArg_x21___main___closed__1;
extern lean_object* l_Lean_Expr_updateProj_x21___closed__1;
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__11;
lean_object* l_AssocList_contains___main___at_Lean_Meta_CheckAssignment_cache___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFVar(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_appFn_x21___closed__1;
extern lean_object* l___private_Init_Lean_Meta_InferType_1__getForallResultType___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Meta_CheckAssignment_findCached___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Meta_CheckAssignment_cache___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_11__processAssignmentFOApprox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__21;
lean_object* l_Lean_Meta_CheckAssignment_getMCtx___boxed(lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_check___main(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isEtaUnassignedMVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_assign_expr(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__processAssignmentFOApproxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_ParamInfo_inhabited;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__10;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__8;
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_10__processAssignmentFOApproxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_Meta_CheckAssignment_cache___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_MessageData_coeOfArrayExpr___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_inhabited;
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_findCached___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Meta_CheckAssignment_findCached___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_expr_mk_mvar(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__1;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_mk_bvar(lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticExprMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_Meta_LevelDefEq_7__isLevelDefEqAux___main___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_3__isDefEqArgsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_letName_x21___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__18;
extern lean_object* l_Lean_Expr_updateLambda_x21___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_LevelDefEq_13__restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_checkFVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_5__isDefEqBindingAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__2;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_checkAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferTypeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__2;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_findCached(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_Lean_MonadCache___closed__3;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__9;
uint8_t l_Array_anyMAux___main___at_Lean_Meta_checkAssignment___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqBindingDomain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_inhabited___closed__1;
lean_object* lean_metavar_ctx_mk_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__19;
lean_object* lean_expr_mk_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckAssignment_getMCtx(lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Meta_CheckAssignment_findCached___spec__1(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_expr_mvar(lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__14;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__1;
lean_object* l_Lean_Meta_CheckAssignment_check(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_4__isDefEqArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Meta_isEtaUnassignedMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqBindingDomain___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__16;
lean_object* l_Lean_Meta_CheckAssignment_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1;
lean_object* l___private_Init_Lean_Meta_ExprDefEq_7__visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_2__isDefEqArgsFirstPass___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isWellFormed___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqBindingDomain___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__4;
lean_object* l___private_Init_Lean_Meta_LevelDefEq_12__processPostponed(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_8__etaExpandedAux___main(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_Expr_getRevArg_x21___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_expr_mk_bvar(x_1);
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
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_23, sizeof(void*)*3);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 2);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1;
x_30 = lean_expr_mk_app(x_28, x_29);
x_31 = lean_expr_mk_lambda(x_25, x_26, x_27, x_30);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_45; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
x_35 = lean_ctor_get(x_24, 5);
x_36 = l_PersistentArray_empty___closed__3;
lean_inc(x_34);
lean_inc(x_33);
lean_ctor_set(x_24, 5, x_36);
lean_inc(x_5);
x_45 = lean_apply_4(x_2, x_3, x_31, x_5, x_24);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_33, x_34, x_35, x_5, x_48);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_46);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
lean_dec(x_46);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec(x_45);
x_55 = 0;
x_56 = l___private_Init_Lean_Meta_LevelDefEq_12__processPostponed(x_55, x_5, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_33, x_34, x_35, x_5, x_59);
lean_dec(x_5);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set(x_60, 0, x_57);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_5);
x_65 = !lean_is_exclusive(x_56);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_56, 0);
lean_dec(x_66);
return x_56;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_56, 1);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_56, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_56, 1);
lean_inc(x_70);
lean_dec(x_56);
x_37 = x_69;
x_38 = x_70;
goto block_44;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_45, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_45, 1);
lean_inc(x_72);
lean_dec(x_45);
x_37 = x_71;
x_38 = x_72;
goto block_44;
}
block_44:
{
lean_object* x_39; uint8_t x_40; 
x_39 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_33, x_34, x_35, x_5, x_38);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_37);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_88; 
x_73 = lean_ctor_get(x_24, 0);
x_74 = lean_ctor_get(x_24, 1);
x_75 = lean_ctor_get(x_24, 2);
x_76 = lean_ctor_get(x_24, 3);
x_77 = lean_ctor_get(x_24, 4);
x_78 = lean_ctor_get(x_24, 5);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_24);
x_79 = l_PersistentArray_empty___closed__3;
lean_inc(x_74);
lean_inc(x_73);
x_80 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set(x_80, 1, x_74);
lean_ctor_set(x_80, 2, x_75);
lean_ctor_set(x_80, 3, x_76);
lean_ctor_set(x_80, 4, x_77);
lean_ctor_set(x_80, 5, x_79);
lean_inc(x_5);
x_88 = lean_apply_4(x_2, x_3, x_31, x_5, x_80);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_73, x_74, x_78, x_5, x_91);
lean_dec(x_5);
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
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; 
lean_dec(x_89);
x_96 = lean_ctor_get(x_88, 1);
lean_inc(x_96);
lean_dec(x_88);
x_97 = 0;
x_98 = l___private_Init_Lean_Meta_LevelDefEq_12__processPostponed(x_97, x_5, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_73, x_74, x_78, x_5, x_101);
lean_dec(x_5);
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
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
x_106 = lean_ctor_get(x_98, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_107 = x_98;
} else {
 lean_dec_ref(x_98);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_99);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_98, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_98, 1);
lean_inc(x_110);
lean_dec(x_98);
x_81 = x_109;
x_82 = x_110;
goto block_87;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_88, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_88, 1);
lean_inc(x_112);
lean_dec(x_88);
x_81 = x_111;
x_82 = x_112;
goto block_87;
}
block_87:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_73, x_74, x_78, x_5, x_82);
lean_dec(x_5);
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
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_22);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_22, 0);
lean_dec(x_114);
x_115 = 0;
x_116 = lean_box(x_115);
lean_ctor_set(x_22, 0, x_116);
return x_22;
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_22, 1);
lean_inc(x_117);
lean_dec(x_22);
x_118 = 0;
x_119 = lean_box(x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_22);
if (x_121 == 0)
{
return x_22;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_22, 0);
x_123 = lean_ctor_get(x_22, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_22);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_14, 0);
x_126 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_127 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 1);
x_128 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 2);
x_129 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 3);
lean_inc(x_125);
lean_dec(x_14);
x_130 = 1;
x_131 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_131, 0, x_125);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_126);
lean_ctor_set_uint8(x_131, sizeof(void*)*1 + 1, x_127);
lean_ctor_set_uint8(x_131, sizeof(void*)*1 + 2, x_128);
lean_ctor_set_uint8(x_131, sizeof(void*)*1 + 3, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*1 + 4, x_130);
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_17);
lean_ctor_set(x_132, 2, x_18);
x_133 = lean_apply_3(x_1, x_15, x_132, x_16);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 7)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_159; 
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get_uint8(x_134, sizeof(void*)*3);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_134, 2);
lean_inc(x_139);
lean_dec(x_134);
x_140 = l___private_Init_Lean_Meta_ExprDefEq_1__isDefEqEta___closed__1;
x_141 = lean_expr_mk_app(x_139, x_140);
x_142 = lean_expr_mk_lambda(x_136, x_137, x_138, x_141);
x_143 = lean_ctor_get(x_135, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_135, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_135, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_135, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_135, 4);
lean_inc(x_147);
x_148 = lean_ctor_get(x_135, 5);
lean_inc(x_148);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 x_149 = x_135;
} else {
 lean_dec_ref(x_135);
 x_149 = lean_box(0);
}
x_150 = l_PersistentArray_empty___closed__3;
lean_inc(x_144);
lean_inc(x_143);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 6, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_143);
lean_ctor_set(x_151, 1, x_144);
lean_ctor_set(x_151, 2, x_145);
lean_ctor_set(x_151, 3, x_146);
lean_ctor_set(x_151, 4, x_147);
lean_ctor_set(x_151, 5, x_150);
lean_inc(x_5);
x_159 = lean_apply_4(x_2, x_3, x_142, x_5, x_151);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_unbox(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_143, x_144, x_148, x_5, x_162);
lean_dec(x_5);
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
lean_ctor_set(x_166, 0, x_160);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
else
{
lean_object* x_167; uint8_t x_168; lean_object* x_169; 
lean_dec(x_160);
x_167 = lean_ctor_get(x_159, 1);
lean_inc(x_167);
lean_dec(x_159);
x_168 = 0;
x_169 = l___private_Init_Lean_Meta_LevelDefEq_12__processPostponed(x_168, x_5, x_167);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_143, x_144, x_148, x_5, x_172);
lean_dec(x_5);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_170);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_148);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_5);
x_177 = lean_ctor_get(x_169, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_178 = x_169;
} else {
 lean_dec_ref(x_169);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_170);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_169, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_169, 1);
lean_inc(x_181);
lean_dec(x_169);
x_152 = x_180;
x_153 = x_181;
goto block_158;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_159, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_159, 1);
lean_inc(x_183);
lean_dec(x_159);
x_152 = x_182;
x_153 = x_183;
goto block_158;
}
block_158:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = l___private_Init_Lean_Meta_LevelDefEq_13__restore(x_143, x_144, x_148, x_5, x_153);
lean_dec(x_5);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
 lean_ctor_set_tag(x_157, 1);
}
lean_ctor_set(x_157, 0, x_152);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_134);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_184 = lean_ctor_get(x_133, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_185 = x_133;
} else {
 lean_dec_ref(x_133);
 x_185 = lean_box(0);
}
x_186 = 0;
x_187 = lean_box(x_186);
if (lean_is_scalar(x_185)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_185;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_189 = lean_ctor_get(x_133, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_133, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_191 = x_133;
} else {
 lean_dec_ref(x_133);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_193 = !lean_is_exclusive(x_13);
if (x_193 == 0)
{
return x_13;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_13, 0);
x_195 = lean_ctor_get(x_13, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_13);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
uint8_t x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = 0;
x_198 = lean_box(x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_6);
return x_199;
}
}
}
}
lean_object* l_Lean_Meta_isEtaUnassignedMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_Lean_Expr_8__etaExpandedAux___main(x_1, x_4);
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
x_14 = l_Lean_Expr_inhabited;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_9 = l_Lean_Expr_inhabited;
x_10 = lean_array_get(x_9, x_1, x_6);
x_11 = lean_array_get(x_9, x_2, x_6);
x_160 = l_Lean_Meta_ParamInfo_inhabited;
x_161 = lean_array_get(x_160, x_4, x_6);
x_162 = lean_ctor_get_uint8(x_161, sizeof(void*)*1 + 1);
lean_dec(x_161);
if (x_162 == 0)
{
lean_dec(x_5);
x_12 = x_8;
goto block_159;
}
else
{
lean_object* x_163; 
lean_inc(x_5);
lean_inc(x_7);
lean_inc(x_10);
x_163 = lean_apply_3(x_5, x_10, x_7, x_8);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
lean_inc(x_7);
lean_inc(x_11);
x_165 = lean_apply_3(x_5, x_11, x_7, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_12 = x_166;
goto block_159;
}
else
{
uint8_t x_167; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
x_167 = !lean_is_exclusive(x_165);
if (x_167 == 0)
{
return x_165;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_165, 0);
x_169 = lean_ctor_get(x_165, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_165);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_171 = !lean_is_exclusive(x_163);
if (x_171 == 0)
{
return x_163;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_163, 0);
x_173 = lean_ctor_get(x_163, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_163);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
block_159:
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
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
lean_dec(x_31);
x_32 = 0;
x_33 = lean_box(x_32);
lean_ctor_set(x_19, 0, x_33);
return x_19;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_dec(x_19);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 4, x_17);
x_42 = lean_apply_4(x_3, x_10, x_11, x_7, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
lean_dec(x_46);
x_47 = 1;
x_48 = lean_box(x_47);
lean_ctor_set(x_42, 0, x_48);
return x_42;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = 1;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_42);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_42, 0);
lean_dec(x_54);
x_55 = 0;
x_56 = lean_box(x_55);
lean_ctor_set(x_42, 0, x_56);
return x_42;
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_dec(x_42);
x_58 = 0;
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_42);
if (x_61 == 0)
{
return x_42;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_42, 0);
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_42);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; 
x_65 = lean_ctor_get(x_14, 0);
x_66 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_67 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 1);
x_68 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 2);
x_69 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 3);
x_70 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 4);
lean_inc(x_65);
lean_dec(x_14);
x_71 = 1;
x_72 = l_Lean_Meta_TransparencyMode_lt(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_73, 0, x_65);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_66);
lean_ctor_set_uint8(x_73, sizeof(void*)*1 + 1, x_67);
lean_ctor_set_uint8(x_73, sizeof(void*)*1 + 2, x_68);
lean_ctor_set_uint8(x_73, sizeof(void*)*1 + 3, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*1 + 4, x_70);
lean_ctor_set(x_7, 0, x_73);
x_74 = lean_apply_4(x_3, x_10, x_11, x_7, x_12);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
x_79 = 1;
x_80 = lean_box(x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_74, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_83 = x_74;
} else {
 lean_dec_ref(x_74);
 x_83 = lean_box(0);
}
x_84 = 0;
x_85 = lean_box(x_84);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_74, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_74, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_89 = x_74;
} else {
 lean_dec_ref(x_74);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_91, 0, x_65);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_66);
lean_ctor_set_uint8(x_91, sizeof(void*)*1 + 1, x_67);
lean_ctor_set_uint8(x_91, sizeof(void*)*1 + 2, x_68);
lean_ctor_set_uint8(x_91, sizeof(void*)*1 + 3, x_69);
lean_ctor_set_uint8(x_91, sizeof(void*)*1 + 4, x_71);
lean_ctor_set(x_7, 0, x_91);
x_92 = lean_apply_4(x_3, x_10, x_11, x_7, x_12);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
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
x_97 = 1;
x_98 = lean_box(x_97);
if (lean_is_scalar(x_96)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_96;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_95);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_92, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_101 = x_92;
} else {
 lean_dec_ref(x_92);
 x_101 = lean_box(0);
}
x_102 = 0;
x_103 = lean_box(x_102);
if (lean_is_scalar(x_101)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_101;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_100);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_92, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_92, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_107 = x_92;
} else {
 lean_dec_ref(x_92);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; lean_object* x_118; uint8_t x_119; uint8_t x_120; 
x_109 = lean_ctor_get(x_7, 0);
x_110 = lean_ctor_get(x_7, 1);
x_111 = lean_ctor_get(x_7, 2);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_7);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get_uint8(x_109, sizeof(void*)*1);
x_114 = lean_ctor_get_uint8(x_109, sizeof(void*)*1 + 1);
x_115 = lean_ctor_get_uint8(x_109, sizeof(void*)*1 + 2);
x_116 = lean_ctor_get_uint8(x_109, sizeof(void*)*1 + 3);
x_117 = lean_ctor_get_uint8(x_109, sizeof(void*)*1 + 4);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_118 = x_109;
} else {
 lean_dec_ref(x_109);
 x_118 = lean_box(0);
}
x_119 = 1;
x_120 = l_Lean_Meta_TransparencyMode_lt(x_117, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 1, 5);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_112);
lean_ctor_set_uint8(x_121, sizeof(void*)*1, x_113);
lean_ctor_set_uint8(x_121, sizeof(void*)*1 + 1, x_114);
lean_ctor_set_uint8(x_121, sizeof(void*)*1 + 2, x_115);
lean_ctor_set_uint8(x_121, sizeof(void*)*1 + 3, x_116);
lean_ctor_set_uint8(x_121, sizeof(void*)*1 + 4, x_117);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_110);
lean_ctor_set(x_122, 2, x_111);
x_123 = lean_apply_4(x_3, x_10, x_11, x_122, x_12);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_127 = x_123;
} else {
 lean_dec_ref(x_123);
 x_127 = lean_box(0);
}
x_128 = 1;
x_129 = lean_box(x_128);
if (lean_is_scalar(x_127)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_127;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_126);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_123, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_132 = x_123;
} else {
 lean_dec_ref(x_123);
 x_132 = lean_box(0);
}
x_133 = 0;
x_134 = lean_box(x_133);
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_132;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_131);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_123, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_123, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_138 = x_123;
} else {
 lean_dec_ref(x_123);
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
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
if (lean_is_scalar(x_118)) {
 x_140 = lean_alloc_ctor(0, 1, 5);
} else {
 x_140 = x_118;
}
lean_ctor_set(x_140, 0, x_112);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_113);
lean_ctor_set_uint8(x_140, sizeof(void*)*1 + 1, x_114);
lean_ctor_set_uint8(x_140, sizeof(void*)*1 + 2, x_115);
lean_ctor_set_uint8(x_140, sizeof(void*)*1 + 3, x_116);
lean_ctor_set_uint8(x_140, sizeof(void*)*1 + 4, x_119);
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_110);
lean_ctor_set(x_141, 2, x_111);
x_142 = lean_apply_4(x_3, x_10, x_11, x_141, x_12);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_146 = x_142;
} else {
 lean_dec_ref(x_142);
 x_146 = lean_box(0);
}
x_147 = 1;
x_148 = lean_box(x_147);
if (lean_is_scalar(x_146)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_146;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_145);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_142, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_151 = x_142;
} else {
 lean_dec_ref(x_142);
 x_151 = lean_box(0);
}
x_152 = 0;
x_153 = lean_box(x_152);
if (lean_is_scalar(x_151)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_151;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_150);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_142, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_142, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_157 = x_142;
} else {
 lean_dec_ref(x_142);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
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
x_38 = l___private_Init_Lean_Meta_InferType_1__getForallResultType___closed__1;
x_39 = l_Array_anyMAux___main___rarg(x_38, x_36, x_37, x_23);
x_40 = lean_apply_2(x_39, x_7, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = 1;
x_46 = lean_box(x_45);
lean_ctor_set(x_40, 0, x_46);
return x_40;
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_dec(x_40);
x_48 = 1;
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
lean_dec(x_52);
x_53 = 0;
x_54 = lean_box(x_53);
lean_ctor_set(x_40, 0, x_54);
return x_40;
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_dec(x_40);
x_56 = 0;
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_40);
if (x_59 == 0)
{
return x_40;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_40, 0);
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_40);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_25);
if (x_63 == 0)
{
return x_25;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_25, 0);
x_65 = lean_ctor_get(x_25, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_25);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
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
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_21);
if (x_67 == 0)
{
return x_21;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_21, 0);
x_69 = lean_ctor_get(x_21, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_21);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_16);
if (x_71 == 0)
{
return x_16;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_16, 0);
x_73 = lean_ctor_get(x_16, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_16);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
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
x_18 = l_Lean_Expr_inhabited;
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
x_36 = lean_expr_mk_fvar(x_32);
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
x_53 = lean_expr_mk_fvar(x_49);
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
x_5 = lean_expr_hash(x_2);
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
x_7 = lean_expr_hash(x_4);
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
x_16 = lean_expr_hash(x_12);
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
x_8 = lean_expr_hash(x_2);
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
x_23 = lean_expr_hash(x_2);
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
x_28 = lean_expr_has_expr_mvar(x_2);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = lean_expr_has_fvar(x_2);
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
uint8_t l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_expr_eqv(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
return x_8;
}
}
}
}
uint8_t l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_expr_eqv(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
return x_8;
}
}
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(x_2, x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Expr_fvarId_x21(x_2);
lean_dec(x_2);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_3, 3);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2(x_2, x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_Expr_fvarId_x21(x_2);
lean_dec(x_2);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_49; 
lean_dec(x_2);
x_25 = lean_ctor_get(x_17, 4);
lean_inc(x_25);
lean_dec(x_17);
x_49 = lean_expr_has_expr_mvar(x_25);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = lean_expr_has_fvar(x_25);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_3);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_25);
lean_ctor_set(x_51, 1, x_4);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_box(0);
x_26 = x_52;
goto block_48;
}
}
else
{
lean_object* x_53; 
x_53 = lean_box(0);
x_26 = x_53;
goto block_48;
}
block_48:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_26);
x_27 = l_Lean_Meta_CheckAssignment_findCached(x_25, x_3, x_4);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_3);
lean_inc(x_25);
x_30 = lean_apply_3(x_1, x_25, x_3, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_31);
x_33 = l_Lean_Meta_CheckAssignment_cache(x_25, x_31, x_3, x_32);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_25);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_27, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_28, 0);
lean_inc(x_44);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_44);
return x_27;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_ctor_get(x_28, 0);
lean_inc(x_46);
lean_dec(x_28);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_4);
return x_54;
}
}
}
lean_object* l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_checkFVar___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
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
x_17 = lean_expr_mk_mvar(x_11);
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
x_29 = lean_expr_mk_mvar(x_22);
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
x_45 = lean_expr_mk_mvar(x_37);
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
x_9 = lean_name_dec_eq(x_5, x_8);
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
lean_object* x_29; uint8_t x_30; 
lean_dec(x_2);
x_29 = lean_ctor_get(x_14, 2);
lean_inc(x_29);
lean_dec(x_14);
lean_inc(x_29);
lean_inc(x_17);
x_30 = l_Lean_MetavarContext_isWellFormed___main(x_6, x_17, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_3);
x_31 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_31, 0, x_5);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Meta_CheckAssignment_mkAuxMVar(x_17, x_29, x_3, x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_39 = lean_metavar_ctx_assign_expr(x_38, x_5, x_37);
lean_ctor_set(x_35, 0, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
x_43 = lean_ctor_get(x_35, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
lean_inc(x_40);
x_44 = lean_metavar_ctx_assign_expr(x_41, x_5, x_40);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set(x_33, 1, x_45);
return x_33;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_33, 1);
x_47 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
lean_inc(x_47);
lean_dec(x_33);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 2);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
lean_inc(x_47);
x_52 = lean_metavar_ctx_assign_expr(x_48, x_5, x_47);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 3, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_5);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_4);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_4);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_box(1);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_4);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_4);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_86; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_62 = lean_ctor_get(x_7, 0);
lean_inc(x_62);
lean_dec(x_7);
x_86 = lean_expr_has_expr_mvar(x_62);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = lean_expr_has_fvar(x_62);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_3);
lean_dec(x_1);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_62);
lean_ctor_set(x_88, 1, x_4);
return x_88;
}
else
{
lean_object* x_89; 
x_89 = lean_box(0);
x_63 = x_89;
goto block_85;
}
}
else
{
lean_object* x_90; 
x_90 = lean_box(0);
x_63 = x_90;
goto block_85;
}
block_85:
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_63);
x_64 = l_Lean_Meta_CheckAssignment_findCached(x_62, x_3, x_4);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_3);
lean_inc(x_62);
x_67 = lean_apply_3(x_1, x_62, x_3, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_inc(x_68);
x_70 = l_Lean_Meta_CheckAssignment_cache(x_62, x_68, x_3, x_69);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_62);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_67);
if (x_75 == 0)
{
return x_67;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_67, 0);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_67);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_62);
lean_dec(x_3);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_64);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_64, 0);
lean_dec(x_80);
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
lean_dec(x_65);
lean_ctor_set(x_64, 0, x_81);
return x_64;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_64, 1);
lean_inc(x_82);
lean_dec(x_64);
x_83 = lean_ctor_get(x_65, 0);
lean_inc(x_83);
lean_dec(x_65);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
}
}
uint8_t l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_expr_eqv(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
return x_8;
}
}
}
}
uint8_t l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_expr_eqv(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
return x_8;
}
}
}
}
lean_object* l_Lean_Meta_CheckAssignment_check___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_12; lean_object* x_13; lean_object* x_23; lean_object* x_24; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_34; uint8_t x_124; 
x_124 = lean_expr_has_expr_mvar(x_1);
if (x_124 == 0)
{
uint8_t x_125; 
x_125 = lean_expr_has_fvar(x_1);
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec(x_2);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_3);
return x_126;
}
else
{
lean_object* x_127; 
x_127 = lean_box(0);
x_34 = x_127;
goto block_123;
}
}
else
{
lean_object* x_128; 
x_128 = lean_box(0);
x_34 = x_128;
goto block_123;
}
block_123:
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_34);
x_35 = l_Lean_Meta_CheckAssignment_findCached(x_1, x_2, x_3);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_2, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_LocalContext_containsFVar(x_41, x_1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = l_Lean_LocalContext_findFVar(x_43, x_1);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_2, 3);
lean_inc(x_45);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__1(x_1, x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_48 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_49);
return x_35;
}
else
{
lean_free_object(x_35);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_38;
goto block_11;
}
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec(x_44);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_50);
x_51 = lean_ctor_get(x_2, 3);
lean_inc(x_51);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__2(x_1, x_51, x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
x_54 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_55);
return x_35;
}
else
{
lean_free_object(x_35);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_38;
goto block_11;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_73; 
lean_free_object(x_35);
x_56 = lean_ctor_get(x_50, 4);
lean_inc(x_56);
lean_dec(x_50);
x_73 = lean_expr_has_expr_mvar(x_56);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = lean_expr_has_fvar(x_56);
if (x_74 == 0)
{
x_4 = x_56;
x_5 = x_38;
goto block_11;
}
else
{
lean_object* x_75; 
x_75 = lean_box(0);
x_57 = x_75;
goto block_72;
}
}
else
{
lean_object* x_76; 
x_76 = lean_box(0);
x_57 = x_76;
goto block_72;
}
block_72:
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_57);
x_58 = l_Lean_Meta_CheckAssignment_findCached(x_56, x_2, x_38);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_2);
lean_inc(x_56);
x_61 = l_Lean_Meta_CheckAssignment_check___main(x_56, x_2, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_62);
x_64 = l_Lean_Meta_CheckAssignment_cache(x_56, x_62, x_2, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_4 = x_62;
x_5 = x_65;
goto block_11;
}
else
{
uint8_t x_66; 
lean_dec(x_56);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_61, 0);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_61);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_56);
x_70 = lean_ctor_get(x_58, 1);
lean_inc(x_70);
lean_dec(x_58);
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
lean_dec(x_59);
x_4 = x_71;
x_5 = x_70;
goto block_11;
}
}
}
}
}
else
{
lean_free_object(x_35);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_38;
goto block_11;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_35, 1);
lean_inc(x_77);
lean_dec(x_35);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_LocalContext_containsFVar(x_79, x_1);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
x_82 = l_Lean_LocalContext_findFVar(x_81, x_1);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_2, 3);
lean_inc(x_83);
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__1(x_1, x_83, x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_2);
x_86 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
x_87 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_77);
return x_88;
}
else
{
lean_inc(x_1);
x_4 = x_1;
x_5 = x_77;
goto block_11;
}
}
else
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
lean_dec(x_82);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_89);
x_90 = lean_ctor_get(x_2, 3);
lean_inc(x_90);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__2(x_1, x_90, x_91);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_2);
x_93 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_77);
return x_95;
}
else
{
lean_inc(x_1);
x_4 = x_1;
x_5 = x_77;
goto block_11;
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_113; 
x_96 = lean_ctor_get(x_89, 4);
lean_inc(x_96);
lean_dec(x_89);
x_113 = lean_expr_has_expr_mvar(x_96);
if (x_113 == 0)
{
uint8_t x_114; 
x_114 = lean_expr_has_fvar(x_96);
if (x_114 == 0)
{
x_4 = x_96;
x_5 = x_77;
goto block_11;
}
else
{
lean_object* x_115; 
x_115 = lean_box(0);
x_97 = x_115;
goto block_112;
}
}
else
{
lean_object* x_116; 
x_116 = lean_box(0);
x_97 = x_116;
goto block_112;
}
block_112:
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_97);
x_98 = l_Lean_Meta_CheckAssignment_findCached(x_96, x_2, x_77);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_2);
lean_inc(x_96);
x_101 = l_Lean_Meta_CheckAssignment_check___main(x_96, x_2, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_102);
x_104 = l_Lean_Meta_CheckAssignment_cache(x_96, x_102, x_2, x_103);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_4 = x_102;
x_5 = x_105;
goto block_11;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_96);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_108 = x_101;
} else {
 lean_dec_ref(x_101);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_96);
x_110 = lean_ctor_get(x_98, 1);
lean_inc(x_110);
lean_dec(x_98);
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
lean_dec(x_99);
x_4 = x_111;
x_5 = x_110;
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
x_5 = x_77;
goto block_11;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_35);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_35, 0);
lean_dec(x_118);
x_119 = lean_ctor_get(x_36, 0);
lean_inc(x_119);
lean_dec(x_36);
lean_ctor_set(x_35, 0, x_119);
return x_35;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_35, 1);
lean_inc(x_120);
lean_dec(x_35);
x_121 = lean_ctor_get(x_36, 0);
lean_inc(x_121);
lean_dec(x_36);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
}
case 2:
{
lean_object* x_129; uint8_t x_263; 
x_263 = lean_expr_has_expr_mvar(x_1);
if (x_263 == 0)
{
uint8_t x_264; 
x_264 = lean_expr_has_fvar(x_1);
if (x_264 == 0)
{
lean_object* x_265; 
lean_dec(x_2);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_1);
lean_ctor_set(x_265, 1, x_3);
return x_265;
}
else
{
lean_object* x_266; 
x_266 = lean_box(0);
x_129 = x_266;
goto block_262;
}
}
else
{
lean_object* x_267; 
x_267 = lean_box(0);
x_129 = x_267;
goto block_262;
}
block_262:
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_129);
x_130 = l_Lean_Meta_CheckAssignment_findCached(x_1, x_2, x_3);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_130, 1);
x_134 = lean_ctor_get(x_130, 0);
lean_dec(x_134);
x_135 = l_Lean_Expr_mvarId_x21(x_1);
x_136 = lean_ctor_get(x_133, 0);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_136);
x_137 = lean_metavar_ctx_get_expr_assignment(x_136, x_135);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_2, 1);
lean_inc(x_138);
x_139 = lean_name_dec_eq(x_135, x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
lean_inc(x_135);
lean_inc(x_136);
x_140 = lean_metavar_ctx_find_decl(x_136, x_135);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
lean_dec(x_136);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set_tag(x_130, 1);
lean_ctor_set(x_130, 0, x_141);
return x_130;
}
else
{
uint8_t x_142; 
x_142 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 1);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_143 = lean_ctor_get(x_140, 0);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_2, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
lean_inc(x_146);
lean_inc(x_144);
x_147 = l_Lean_LocalContext_isSubPrefixOf(x_144, x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = lean_ctor_get(x_143, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_136, 0);
lean_inc(x_149);
x_150 = lean_nat_dec_eq(x_148, x_149);
lean_dec(x_149);
lean_dec(x_148);
if (x_150 == 0)
{
lean_object* x_151; 
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_136);
lean_dec(x_2);
lean_dec(x_1);
x_151 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_151, 0, x_135);
lean_ctor_set_tag(x_130, 1);
lean_ctor_set(x_130, 0, x_151);
return x_130;
}
else
{
uint8_t x_152; 
x_152 = lean_ctor_get_uint8(x_143, sizeof(void*)*4);
if (x_152 == 0)
{
uint8_t x_153; 
x_153 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_153 == 0)
{
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_136);
lean_dec(x_135);
lean_free_object(x_130);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_133;
goto block_11;
}
else
{
uint8_t x_154; 
lean_inc(x_146);
x_154 = l_Lean_LocalContext_isSubPrefixOf(x_146, x_144);
if (x_154 == 0)
{
lean_dec(x_146);
lean_dec(x_143);
lean_dec(x_136);
lean_dec(x_135);
lean_free_object(x_130);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_133;
goto block_11;
}
else
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_143, 2);
lean_inc(x_155);
lean_dec(x_143);
lean_inc(x_155);
lean_inc(x_146);
x_156 = l_Lean_MetavarContext_isWellFormed___main(x_136, x_146, x_155);
if (x_156 == 0)
{
lean_object* x_157; 
lean_dec(x_155);
lean_dec(x_146);
lean_dec(x_2);
lean_dec(x_1);
x_157 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_157, 0, x_135);
lean_ctor_set_tag(x_130, 1);
lean_ctor_set(x_130, 0, x_157);
return x_130;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_free_object(x_130);
x_158 = l_Lean_Meta_CheckAssignment_mkAuxMVar(x_146, x_155, x_2, x_133);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
lean_dec(x_158);
x_161 = !lean_is_exclusive(x_159);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_163 = lean_metavar_ctx_assign_expr(x_162, x_135, x_160);
lean_ctor_set(x_159, 0, x_163);
x_4 = x_160;
x_5 = x_159;
goto block_11;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_159, 0);
x_165 = lean_ctor_get(x_159, 1);
x_166 = lean_ctor_get(x_159, 2);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_159);
lean_inc(x_160);
x_167 = lean_metavar_ctx_assign_expr(x_164, x_135, x_160);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_165);
lean_ctor_set(x_168, 2, x_166);
x_4 = x_160;
x_5 = x_168;
goto block_11;
}
}
}
}
}
else
{
lean_object* x_169; 
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_136);
lean_dec(x_2);
lean_dec(x_1);
x_169 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_169, 0, x_135);
lean_ctor_set_tag(x_130, 1);
lean_ctor_set(x_130, 0, x_169);
return x_130;
}
}
}
else
{
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_136);
lean_dec(x_135);
lean_free_object(x_130);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_133;
goto block_11;
}
}
else
{
lean_object* x_170; 
lean_dec(x_140);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_box(1);
lean_ctor_set_tag(x_130, 1);
lean_ctor_set(x_130, 0, x_170);
return x_130;
}
}
}
else
{
lean_object* x_171; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_box(0);
lean_ctor_set_tag(x_130, 1);
lean_ctor_set(x_130, 0, x_171);
return x_130;
}
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_189; 
lean_dec(x_136);
lean_dec(x_135);
lean_free_object(x_130);
x_172 = lean_ctor_get(x_137, 0);
lean_inc(x_172);
lean_dec(x_137);
x_189 = lean_expr_has_expr_mvar(x_172);
if (x_189 == 0)
{
uint8_t x_190; 
x_190 = lean_expr_has_fvar(x_172);
if (x_190 == 0)
{
x_4 = x_172;
x_5 = x_133;
goto block_11;
}
else
{
lean_object* x_191; 
x_191 = lean_box(0);
x_173 = x_191;
goto block_188;
}
}
else
{
lean_object* x_192; 
x_192 = lean_box(0);
x_173 = x_192;
goto block_188;
}
block_188:
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_173);
x_174 = l_Lean_Meta_CheckAssignment_findCached(x_172, x_2, x_133);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
lean_inc(x_2);
lean_inc(x_172);
x_177 = l_Lean_Meta_CheckAssignment_check___main(x_172, x_2, x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
lean_inc(x_178);
x_180 = l_Lean_Meta_CheckAssignment_cache(x_172, x_178, x_2, x_179);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_4 = x_178;
x_5 = x_181;
goto block_11;
}
else
{
uint8_t x_182; 
lean_dec(x_172);
lean_dec(x_2);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_177);
if (x_182 == 0)
{
return x_177;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_177, 0);
x_184 = lean_ctor_get(x_177, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_177);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_172);
x_186 = lean_ctor_get(x_174, 1);
lean_inc(x_186);
lean_dec(x_174);
x_187 = lean_ctor_get(x_175, 0);
lean_inc(x_187);
lean_dec(x_175);
x_4 = x_187;
x_5 = x_186;
goto block_11;
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_130, 1);
lean_inc(x_193);
lean_dec(x_130);
x_194 = l_Lean_Expr_mvarId_x21(x_1);
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_195);
x_196 = lean_metavar_ctx_get_expr_assignment(x_195, x_194);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; uint8_t x_198; 
x_197 = lean_ctor_get(x_2, 1);
lean_inc(x_197);
x_198 = lean_name_dec_eq(x_194, x_197);
lean_dec(x_197);
if (x_198 == 0)
{
lean_object* x_199; 
lean_inc(x_194);
lean_inc(x_195);
x_199 = lean_metavar_ctx_find_decl(x_195, x_194);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_195);
lean_dec(x_2);
lean_dec(x_1);
x_200 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_200, 0, x_194);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_193);
return x_201;
}
else
{
uint8_t x_202; 
x_202 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 1);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_203 = lean_ctor_get(x_199, 0);
lean_inc(x_203);
lean_dec(x_199);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_2, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
lean_inc(x_206);
lean_inc(x_204);
x_207 = l_Lean_LocalContext_isSubPrefixOf(x_204, x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_203, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_195, 0);
lean_inc(x_209);
x_210 = lean_nat_dec_eq(x_208, x_209);
lean_dec(x_209);
lean_dec(x_208);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_195);
lean_dec(x_2);
lean_dec(x_1);
x_211 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_211, 0, x_194);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_193);
return x_212;
}
else
{
uint8_t x_213; 
x_213 = lean_ctor_get_uint8(x_203, sizeof(void*)*4);
if (x_213 == 0)
{
uint8_t x_214; 
x_214 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_214 == 0)
{
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_195);
lean_dec(x_194);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_193;
goto block_11;
}
else
{
uint8_t x_215; 
lean_inc(x_206);
x_215 = l_Lean_LocalContext_isSubPrefixOf(x_206, x_204);
if (x_215 == 0)
{
lean_dec(x_206);
lean_dec(x_203);
lean_dec(x_195);
lean_dec(x_194);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_193;
goto block_11;
}
else
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_203, 2);
lean_inc(x_216);
lean_dec(x_203);
lean_inc(x_216);
lean_inc(x_206);
x_217 = l_Lean_MetavarContext_isWellFormed___main(x_195, x_206, x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_216);
lean_dec(x_206);
lean_dec(x_2);
lean_dec(x_1);
x_218 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_218, 0, x_194);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_193);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_220 = l_Lean_Meta_CheckAssignment_mkAuxMVar(x_206, x_216, x_2, x_193);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_221, 2);
lean_inc(x_225);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 lean_ctor_release(x_221, 2);
 x_226 = x_221;
} else {
 lean_dec_ref(x_221);
 x_226 = lean_box(0);
}
lean_inc(x_222);
x_227 = lean_metavar_ctx_assign_expr(x_223, x_194, x_222);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 3, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_224);
lean_ctor_set(x_228, 2, x_225);
x_4 = x_222;
x_5 = x_228;
goto block_11;
}
}
}
}
else
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_195);
lean_dec(x_2);
lean_dec(x_1);
x_229 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_229, 0, x_194);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_193);
return x_230;
}
}
}
else
{
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_195);
lean_dec(x_194);
lean_inc(x_1);
x_4 = x_1;
x_5 = x_193;
goto block_11;
}
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_199);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_2);
lean_dec(x_1);
x_231 = lean_box(1);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_193);
return x_232;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_2);
lean_dec(x_1);
x_233 = lean_box(0);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_193);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; uint8_t x_252; 
lean_dec(x_195);
lean_dec(x_194);
x_235 = lean_ctor_get(x_196, 0);
lean_inc(x_235);
lean_dec(x_196);
x_252 = lean_expr_has_expr_mvar(x_235);
if (x_252 == 0)
{
uint8_t x_253; 
x_253 = lean_expr_has_fvar(x_235);
if (x_253 == 0)
{
x_4 = x_235;
x_5 = x_193;
goto block_11;
}
else
{
lean_object* x_254; 
x_254 = lean_box(0);
x_236 = x_254;
goto block_251;
}
}
else
{
lean_object* x_255; 
x_255 = lean_box(0);
x_236 = x_255;
goto block_251;
}
block_251:
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_236);
x_237 = l_Lean_Meta_CheckAssignment_findCached(x_235, x_2, x_193);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
lean_inc(x_2);
lean_inc(x_235);
x_240 = l_Lean_Meta_CheckAssignment_check___main(x_235, x_2, x_239);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
lean_inc(x_241);
x_243 = l_Lean_Meta_CheckAssignment_cache(x_235, x_241, x_2, x_242);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_4 = x_241;
x_5 = x_244;
goto block_11;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_235);
lean_dec(x_2);
lean_dec(x_1);
x_245 = lean_ctor_get(x_240, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_240, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_247 = x_240;
} else {
 lean_dec_ref(x_240);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_235);
x_249 = lean_ctor_get(x_237, 1);
lean_inc(x_249);
lean_dec(x_237);
x_250 = lean_ctor_get(x_238, 0);
lean_inc(x_250);
lean_dec(x_238);
x_4 = x_250;
x_5 = x_249;
goto block_11;
}
}
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_2);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_130);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_130, 0);
lean_dec(x_257);
x_258 = lean_ctor_get(x_131, 0);
lean_inc(x_258);
lean_dec(x_131);
lean_ctor_set(x_130, 0, x_258);
return x_130;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_130, 1);
lean_inc(x_259);
lean_dec(x_130);
x_260 = lean_ctor_get(x_131, 0);
lean_inc(x_260);
lean_dec(x_131);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
}
}
case 5:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_304; uint8_t x_320; 
x_268 = lean_ctor_get(x_1, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_1, 1);
lean_inc(x_269);
x_320 = lean_expr_has_expr_mvar(x_268);
if (x_320 == 0)
{
uint8_t x_321; 
x_321 = lean_expr_has_fvar(x_268);
if (x_321 == 0)
{
x_270 = x_268;
x_271 = x_3;
goto block_303;
}
else
{
lean_object* x_322; 
x_322 = lean_box(0);
x_304 = x_322;
goto block_319;
}
}
else
{
lean_object* x_323; 
x_323 = lean_box(0);
x_304 = x_323;
goto block_319;
}
block_303:
{
lean_object* x_272; lean_object* x_273; lean_object* x_283; uint8_t x_299; 
x_299 = lean_expr_has_expr_mvar(x_269);
if (x_299 == 0)
{
uint8_t x_300; 
x_300 = lean_expr_has_fvar(x_269);
if (x_300 == 0)
{
lean_dec(x_2);
x_272 = x_269;
x_273 = x_271;
goto block_282;
}
else
{
lean_object* x_301; 
x_301 = lean_box(0);
x_283 = x_301;
goto block_298;
}
}
else
{
lean_object* x_302; 
x_302 = lean_box(0);
x_283 = x_302;
goto block_298;
}
block_282:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_expr_update_app(x_1, x_270, x_272);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_272);
lean_dec(x_270);
lean_dec(x_1);
x_276 = l_Lean_Expr_getRevArg_x21___main___closed__1;
x_277 = lean_unsigned_to_nat(487u);
x_278 = lean_unsigned_to_nat(16u);
x_279 = l_Lean_Expr_appFn_x21___closed__1;
x_280 = l_panicWithPos___at_Lean_Expr_getRevArg_x21___main___spec__1(x_276, x_277, x_278, x_279);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_273);
return x_281;
}
}
block_298:
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_283);
x_284 = l_Lean_Meta_CheckAssignment_findCached(x_269, x_2, x_271);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
lean_inc(x_2);
lean_inc(x_269);
x_287 = l_Lean_Meta_CheckAssignment_check___main(x_269, x_2, x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
lean_inc(x_288);
x_290 = l_Lean_Meta_CheckAssignment_cache(x_269, x_288, x_2, x_289);
lean_dec(x_2);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec(x_290);
x_272 = x_288;
x_273 = x_291;
goto block_282;
}
else
{
uint8_t x_292; 
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_2);
lean_dec(x_1);
x_292 = !lean_is_exclusive(x_287);
if (x_292 == 0)
{
return x_287;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_287, 0);
x_294 = lean_ctor_get(x_287, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_287);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
else
{
lean_object* x_296; lean_object* x_297; 
lean_dec(x_269);
lean_dec(x_2);
x_296 = lean_ctor_get(x_284, 1);
lean_inc(x_296);
lean_dec(x_284);
x_297 = lean_ctor_get(x_285, 0);
lean_inc(x_297);
lean_dec(x_285);
x_272 = x_297;
x_273 = x_296;
goto block_282;
}
}
}
block_319:
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_304);
x_305 = l_Lean_Meta_CheckAssignment_findCached(x_268, x_2, x_3);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
lean_inc(x_2);
lean_inc(x_268);
x_308 = l_Lean_Meta_CheckAssignment_check___main(x_268, x_2, x_307);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
lean_inc(x_309);
x_311 = l_Lean_Meta_CheckAssignment_cache(x_268, x_309, x_2, x_310);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
lean_dec(x_311);
x_270 = x_309;
x_271 = x_312;
goto block_303;
}
else
{
uint8_t x_313; 
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_2);
lean_dec(x_1);
x_313 = !lean_is_exclusive(x_308);
if (x_313 == 0)
{
return x_308;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_308, 0);
x_315 = lean_ctor_get(x_308, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_308);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
else
{
lean_object* x_317; lean_object* x_318; 
lean_dec(x_268);
x_317 = lean_ctor_get(x_305, 1);
lean_inc(x_317);
lean_dec(x_305);
x_318 = lean_ctor_get(x_306, 0);
lean_inc(x_318);
lean_dec(x_306);
x_270 = x_318;
x_271 = x_317;
goto block_303;
}
}
}
case 6:
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_361; uint8_t x_377; 
x_324 = lean_ctor_get(x_1, 1);
lean_inc(x_324);
x_325 = lean_ctor_get(x_1, 2);
lean_inc(x_325);
x_377 = lean_expr_has_expr_mvar(x_324);
if (x_377 == 0)
{
uint8_t x_378; 
x_378 = lean_expr_has_fvar(x_324);
if (x_378 == 0)
{
x_326 = x_324;
x_327 = x_3;
goto block_360;
}
else
{
lean_object* x_379; 
x_379 = lean_box(0);
x_361 = x_379;
goto block_376;
}
}
else
{
lean_object* x_380; 
x_380 = lean_box(0);
x_361 = x_380;
goto block_376;
}
block_360:
{
lean_object* x_328; lean_object* x_329; lean_object* x_340; uint8_t x_356; 
x_356 = lean_expr_has_expr_mvar(x_325);
if (x_356 == 0)
{
uint8_t x_357; 
x_357 = lean_expr_has_fvar(x_325);
if (x_357 == 0)
{
lean_dec(x_2);
x_328 = x_325;
x_329 = x_327;
goto block_339;
}
else
{
lean_object* x_358; 
x_358 = lean_box(0);
x_340 = x_358;
goto block_355;
}
}
else
{
lean_object* x_359; 
x_359 = lean_box(0);
x_340 = x_359;
goto block_355;
}
block_339:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_331 = lean_expr_update_lambda(x_1, x_330, x_326, x_328);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_329);
return x_332;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_328);
lean_dec(x_326);
lean_dec(x_1);
x_333 = l_Lean_Expr_getRevArg_x21___main___closed__1;
x_334 = lean_unsigned_to_nat(555u);
x_335 = lean_unsigned_to_nat(18u);
x_336 = l_Lean_Expr_updateLambda_x21___closed__1;
x_337 = l_panicWithPos___at_Lean_Expr_getRevArg_x21___main___spec__1(x_333, x_334, x_335, x_336);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_329);
return x_338;
}
}
block_355:
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_340);
x_341 = l_Lean_Meta_CheckAssignment_findCached(x_325, x_2, x_327);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
lean_inc(x_2);
lean_inc(x_325);
x_344 = l_Lean_Meta_CheckAssignment_check___main(x_325, x_2, x_343);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
lean_inc(x_345);
x_347 = l_Lean_Meta_CheckAssignment_cache(x_325, x_345, x_2, x_346);
lean_dec(x_2);
x_348 = lean_ctor_get(x_347, 1);
lean_inc(x_348);
lean_dec(x_347);
x_328 = x_345;
x_329 = x_348;
goto block_339;
}
else
{
uint8_t x_349; 
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_2);
lean_dec(x_1);
x_349 = !lean_is_exclusive(x_344);
if (x_349 == 0)
{
return x_344;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_344, 0);
x_351 = lean_ctor_get(x_344, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_344);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
else
{
lean_object* x_353; lean_object* x_354; 
lean_dec(x_325);
lean_dec(x_2);
x_353 = lean_ctor_get(x_341, 1);
lean_inc(x_353);
lean_dec(x_341);
x_354 = lean_ctor_get(x_342, 0);
lean_inc(x_354);
lean_dec(x_342);
x_328 = x_354;
x_329 = x_353;
goto block_339;
}
}
}
block_376:
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_361);
x_362 = l_Lean_Meta_CheckAssignment_findCached(x_324, x_2, x_3);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
lean_inc(x_2);
lean_inc(x_324);
x_365 = l_Lean_Meta_CheckAssignment_check___main(x_324, x_2, x_364);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
lean_inc(x_366);
x_368 = l_Lean_Meta_CheckAssignment_cache(x_324, x_366, x_2, x_367);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_326 = x_366;
x_327 = x_369;
goto block_360;
}
else
{
uint8_t x_370; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_2);
lean_dec(x_1);
x_370 = !lean_is_exclusive(x_365);
if (x_370 == 0)
{
return x_365;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_365, 0);
x_372 = lean_ctor_get(x_365, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_365);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; 
lean_dec(x_324);
x_374 = lean_ctor_get(x_362, 1);
lean_inc(x_374);
lean_dec(x_362);
x_375 = lean_ctor_get(x_363, 0);
lean_inc(x_375);
lean_dec(x_363);
x_326 = x_375;
x_327 = x_374;
goto block_360;
}
}
}
case 7:
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_418; uint8_t x_434; 
x_381 = lean_ctor_get(x_1, 1);
lean_inc(x_381);
x_382 = lean_ctor_get(x_1, 2);
lean_inc(x_382);
x_434 = lean_expr_has_expr_mvar(x_381);
if (x_434 == 0)
{
uint8_t x_435; 
x_435 = lean_expr_has_fvar(x_381);
if (x_435 == 0)
{
x_383 = x_381;
x_384 = x_3;
goto block_417;
}
else
{
lean_object* x_436; 
x_436 = lean_box(0);
x_418 = x_436;
goto block_433;
}
}
else
{
lean_object* x_437; 
x_437 = lean_box(0);
x_418 = x_437;
goto block_433;
}
block_417:
{
lean_object* x_385; lean_object* x_386; lean_object* x_397; uint8_t x_413; 
x_413 = lean_expr_has_expr_mvar(x_382);
if (x_413 == 0)
{
uint8_t x_414; 
x_414 = lean_expr_has_fvar(x_382);
if (x_414 == 0)
{
lean_dec(x_2);
x_385 = x_382;
x_386 = x_384;
goto block_396;
}
else
{
lean_object* x_415; 
x_415 = lean_box(0);
x_397 = x_415;
goto block_412;
}
}
else
{
lean_object* x_416; 
x_416 = lean_box(0);
x_397 = x_416;
goto block_412;
}
block_396:
{
if (lean_obj_tag(x_1) == 7)
{
uint8_t x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_388 = lean_expr_update_forall(x_1, x_387, x_383, x_385);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_386);
return x_389;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_1);
x_390 = l_Lean_Expr_getRevArg_x21___main___closed__1;
x_391 = lean_unsigned_to_nat(541u);
x_392 = lean_unsigned_to_nat(22u);
x_393 = l_Lean_Expr_updateForall_x21___closed__1;
x_394 = l_panicWithPos___at_Lean_Expr_getRevArg_x21___main___spec__1(x_390, x_391, x_392, x_393);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_386);
return x_395;
}
}
block_412:
{
lean_object* x_398; lean_object* x_399; 
lean_dec(x_397);
x_398 = l_Lean_Meta_CheckAssignment_findCached(x_382, x_2, x_384);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; 
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
lean_inc(x_2);
lean_inc(x_382);
x_401 = l_Lean_Meta_CheckAssignment_check___main(x_382, x_2, x_400);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
lean_inc(x_402);
x_404 = l_Lean_Meta_CheckAssignment_cache(x_382, x_402, x_2, x_403);
lean_dec(x_2);
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
lean_dec(x_404);
x_385 = x_402;
x_386 = x_405;
goto block_396;
}
else
{
uint8_t x_406; 
lean_dec(x_383);
lean_dec(x_382);
lean_dec(x_2);
lean_dec(x_1);
x_406 = !lean_is_exclusive(x_401);
if (x_406 == 0)
{
return x_401;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_401, 0);
x_408 = lean_ctor_get(x_401, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_401);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
return x_409;
}
}
}
else
{
lean_object* x_410; lean_object* x_411; 
lean_dec(x_382);
lean_dec(x_2);
x_410 = lean_ctor_get(x_398, 1);
lean_inc(x_410);
lean_dec(x_398);
x_411 = lean_ctor_get(x_399, 0);
lean_inc(x_411);
lean_dec(x_399);
x_385 = x_411;
x_386 = x_410;
goto block_396;
}
}
}
block_433:
{
lean_object* x_419; lean_object* x_420; 
lean_dec(x_418);
x_419 = l_Lean_Meta_CheckAssignment_findCached(x_381, x_2, x_3);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
lean_inc(x_2);
lean_inc(x_381);
x_422 = l_Lean_Meta_CheckAssignment_check___main(x_381, x_2, x_421);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
lean_inc(x_423);
x_425 = l_Lean_Meta_CheckAssignment_cache(x_381, x_423, x_2, x_424);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
lean_dec(x_425);
x_383 = x_423;
x_384 = x_426;
goto block_417;
}
else
{
uint8_t x_427; 
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_2);
lean_dec(x_1);
x_427 = !lean_is_exclusive(x_422);
if (x_427 == 0)
{
return x_422;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_422, 0);
x_429 = lean_ctor_get(x_422, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_422);
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_429);
return x_430;
}
}
}
else
{
lean_object* x_431; lean_object* x_432; 
lean_dec(x_381);
x_431 = lean_ctor_get(x_419, 1);
lean_inc(x_431);
lean_dec(x_419);
x_432 = lean_ctor_get(x_420, 0);
lean_inc(x_432);
lean_dec(x_420);
x_383 = x_432;
x_384 = x_431;
goto block_417;
}
}
}
case 8:
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_498; uint8_t x_514; 
x_438 = lean_ctor_get(x_1, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_1, 2);
lean_inc(x_439);
x_440 = lean_ctor_get(x_1, 3);
lean_inc(x_440);
x_514 = lean_expr_has_expr_mvar(x_438);
if (x_514 == 0)
{
uint8_t x_515; 
x_515 = lean_expr_has_fvar(x_438);
if (x_515 == 0)
{
x_441 = x_438;
x_442 = x_3;
goto block_497;
}
else
{
lean_object* x_516; 
x_516 = lean_box(0);
x_498 = x_516;
goto block_513;
}
}
else
{
lean_object* x_517; 
x_517 = lean_box(0);
x_498 = x_517;
goto block_513;
}
block_497:
{
lean_object* x_443; lean_object* x_444; lean_object* x_477; uint8_t x_493; 
x_493 = lean_expr_has_expr_mvar(x_439);
if (x_493 == 0)
{
uint8_t x_494; 
x_494 = lean_expr_has_fvar(x_439);
if (x_494 == 0)
{
x_443 = x_439;
x_444 = x_442;
goto block_476;
}
else
{
lean_object* x_495; 
x_495 = lean_box(0);
x_477 = x_495;
goto block_492;
}
}
else
{
lean_object* x_496; 
x_496 = lean_box(0);
x_477 = x_496;
goto block_492;
}
block_476:
{
lean_object* x_445; lean_object* x_446; lean_object* x_456; uint8_t x_472; 
x_472 = lean_expr_has_expr_mvar(x_440);
if (x_472 == 0)
{
uint8_t x_473; 
x_473 = lean_expr_has_fvar(x_440);
if (x_473 == 0)
{
lean_dec(x_2);
x_445 = x_440;
x_446 = x_444;
goto block_455;
}
else
{
lean_object* x_474; 
x_474 = lean_box(0);
x_456 = x_474;
goto block_471;
}
}
else
{
lean_object* x_475; 
x_475 = lean_box(0);
x_456 = x_475;
goto block_471;
}
block_455:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_expr_update_let(x_1, x_441, x_443, x_445);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_446);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_445);
lean_dec(x_443);
lean_dec(x_441);
lean_dec(x_1);
x_449 = l_Lean_Expr_getRevArg_x21___main___closed__1;
x_450 = lean_unsigned_to_nat(564u);
x_451 = lean_unsigned_to_nat(18u);
x_452 = l_Lean_Expr_letName_x21___closed__1;
x_453 = l_panicWithPos___at_Lean_Expr_getRevArg_x21___main___spec__1(x_449, x_450, x_451, x_452);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_446);
return x_454;
}
}
block_471:
{
lean_object* x_457; lean_object* x_458; 
lean_dec(x_456);
x_457 = l_Lean_Meta_CheckAssignment_findCached(x_440, x_2, x_444);
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; 
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
lean_dec(x_457);
lean_inc(x_2);
lean_inc(x_440);
x_460 = l_Lean_Meta_CheckAssignment_check___main(x_440, x_2, x_459);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec(x_460);
lean_inc(x_461);
x_463 = l_Lean_Meta_CheckAssignment_cache(x_440, x_461, x_2, x_462);
lean_dec(x_2);
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
lean_dec(x_463);
x_445 = x_461;
x_446 = x_464;
goto block_455;
}
else
{
uint8_t x_465; 
lean_dec(x_443);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_2);
lean_dec(x_1);
x_465 = !lean_is_exclusive(x_460);
if (x_465 == 0)
{
return x_460;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_460, 0);
x_467 = lean_ctor_get(x_460, 1);
lean_inc(x_467);
lean_inc(x_466);
lean_dec(x_460);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
return x_468;
}
}
}
else
{
lean_object* x_469; lean_object* x_470; 
lean_dec(x_440);
lean_dec(x_2);
x_469 = lean_ctor_get(x_457, 1);
lean_inc(x_469);
lean_dec(x_457);
x_470 = lean_ctor_get(x_458, 0);
lean_inc(x_470);
lean_dec(x_458);
x_445 = x_470;
x_446 = x_469;
goto block_455;
}
}
}
block_492:
{
lean_object* x_478; lean_object* x_479; 
lean_dec(x_477);
x_478 = l_Lean_Meta_CheckAssignment_findCached(x_439, x_2, x_442);
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; 
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec(x_478);
lean_inc(x_2);
lean_inc(x_439);
x_481 = l_Lean_Meta_CheckAssignment_check___main(x_439, x_2, x_480);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
lean_inc(x_482);
x_484 = l_Lean_Meta_CheckAssignment_cache(x_439, x_482, x_2, x_483);
x_485 = lean_ctor_get(x_484, 1);
lean_inc(x_485);
lean_dec(x_484);
x_443 = x_482;
x_444 = x_485;
goto block_476;
}
else
{
uint8_t x_486; 
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_2);
lean_dec(x_1);
x_486 = !lean_is_exclusive(x_481);
if (x_486 == 0)
{
return x_481;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_481, 0);
x_488 = lean_ctor_get(x_481, 1);
lean_inc(x_488);
lean_inc(x_487);
lean_dec(x_481);
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
return x_489;
}
}
}
else
{
lean_object* x_490; lean_object* x_491; 
lean_dec(x_439);
x_490 = lean_ctor_get(x_478, 1);
lean_inc(x_490);
lean_dec(x_478);
x_491 = lean_ctor_get(x_479, 0);
lean_inc(x_491);
lean_dec(x_479);
x_443 = x_491;
x_444 = x_490;
goto block_476;
}
}
}
block_513:
{
lean_object* x_499; lean_object* x_500; 
lean_dec(x_498);
x_499 = l_Lean_Meta_CheckAssignment_findCached(x_438, x_2, x_3);
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; 
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec(x_499);
lean_inc(x_2);
lean_inc(x_438);
x_502 = l_Lean_Meta_CheckAssignment_check___main(x_438, x_2, x_501);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
lean_dec(x_502);
lean_inc(x_503);
x_505 = l_Lean_Meta_CheckAssignment_cache(x_438, x_503, x_2, x_504);
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
lean_dec(x_505);
x_441 = x_503;
x_442 = x_506;
goto block_497;
}
else
{
uint8_t x_507; 
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_2);
lean_dec(x_1);
x_507 = !lean_is_exclusive(x_502);
if (x_507 == 0)
{
return x_502;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_502, 0);
x_509 = lean_ctor_get(x_502, 1);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_502);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
return x_510;
}
}
}
else
{
lean_object* x_511; lean_object* x_512; 
lean_dec(x_438);
x_511 = lean_ctor_get(x_499, 1);
lean_inc(x_511);
lean_dec(x_499);
x_512 = lean_ctor_get(x_500, 0);
lean_inc(x_512);
lean_dec(x_500);
x_441 = x_512;
x_442 = x_511;
goto block_497;
}
}
}
case 10:
{
lean_object* x_518; lean_object* x_519; uint8_t x_535; 
x_518 = lean_ctor_get(x_1, 1);
lean_inc(x_518);
x_535 = lean_expr_has_expr_mvar(x_518);
if (x_535 == 0)
{
uint8_t x_536; 
x_536 = lean_expr_has_fvar(x_518);
if (x_536 == 0)
{
lean_dec(x_2);
x_12 = x_518;
x_13 = x_3;
goto block_22;
}
else
{
lean_object* x_537; 
x_537 = lean_box(0);
x_519 = x_537;
goto block_534;
}
}
else
{
lean_object* x_538; 
x_538 = lean_box(0);
x_519 = x_538;
goto block_534;
}
block_534:
{
lean_object* x_520; lean_object* x_521; 
lean_dec(x_519);
x_520 = l_Lean_Meta_CheckAssignment_findCached(x_518, x_2, x_3);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; 
x_522 = lean_ctor_get(x_520, 1);
lean_inc(x_522);
lean_dec(x_520);
lean_inc(x_2);
lean_inc(x_518);
x_523 = l_Lean_Meta_CheckAssignment_check___main(x_518, x_2, x_522);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
lean_dec(x_523);
lean_inc(x_524);
x_526 = l_Lean_Meta_CheckAssignment_cache(x_518, x_524, x_2, x_525);
lean_dec(x_2);
x_527 = lean_ctor_get(x_526, 1);
lean_inc(x_527);
lean_dec(x_526);
x_12 = x_524;
x_13 = x_527;
goto block_22;
}
else
{
uint8_t x_528; 
lean_dec(x_518);
lean_dec(x_2);
lean_dec(x_1);
x_528 = !lean_is_exclusive(x_523);
if (x_528 == 0)
{
return x_523;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_523, 0);
x_530 = lean_ctor_get(x_523, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_523);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
return x_531;
}
}
}
else
{
lean_object* x_532; lean_object* x_533; 
lean_dec(x_518);
lean_dec(x_2);
x_532 = lean_ctor_get(x_520, 1);
lean_inc(x_532);
lean_dec(x_520);
x_533 = lean_ctor_get(x_521, 0);
lean_inc(x_533);
lean_dec(x_521);
x_12 = x_533;
x_13 = x_532;
goto block_22;
}
}
}
case 11:
{
lean_object* x_539; lean_object* x_540; uint8_t x_556; 
x_539 = lean_ctor_get(x_1, 2);
lean_inc(x_539);
x_556 = lean_expr_has_expr_mvar(x_539);
if (x_556 == 0)
{
uint8_t x_557; 
x_557 = lean_expr_has_fvar(x_539);
if (x_557 == 0)
{
lean_dec(x_2);
x_23 = x_539;
x_24 = x_3;
goto block_33;
}
else
{
lean_object* x_558; 
x_558 = lean_box(0);
x_540 = x_558;
goto block_555;
}
}
else
{
lean_object* x_559; 
x_559 = lean_box(0);
x_540 = x_559;
goto block_555;
}
block_555:
{
lean_object* x_541; lean_object* x_542; 
lean_dec(x_540);
x_541 = l_Lean_Meta_CheckAssignment_findCached(x_539, x_2, x_3);
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; 
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
lean_dec(x_541);
lean_inc(x_2);
lean_inc(x_539);
x_544 = l_Lean_Meta_CheckAssignment_check___main(x_539, x_2, x_543);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
lean_inc(x_545);
x_547 = l_Lean_Meta_CheckAssignment_cache(x_539, x_545, x_2, x_546);
lean_dec(x_2);
x_548 = lean_ctor_get(x_547, 1);
lean_inc(x_548);
lean_dec(x_547);
x_23 = x_545;
x_24 = x_548;
goto block_33;
}
else
{
uint8_t x_549; 
lean_dec(x_539);
lean_dec(x_2);
lean_dec(x_1);
x_549 = !lean_is_exclusive(x_544);
if (x_549 == 0)
{
return x_544;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_544, 0);
x_551 = lean_ctor_get(x_544, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_544);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
else
{
lean_object* x_553; lean_object* x_554; 
lean_dec(x_539);
lean_dec(x_2);
x_553 = lean_ctor_get(x_541, 1);
lean_inc(x_553);
lean_dec(x_541);
x_554 = lean_ctor_get(x_542, 0);
lean_inc(x_554);
lean_dec(x_542);
x_23 = x_554;
x_24 = x_553;
goto block_33;
}
}
}
default: 
{
lean_object* x_560; 
lean_dec(x_2);
x_560 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_560, 0, x_1);
lean_ctor_set(x_560, 1, x_3);
return x_560;
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
block_22:
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_1);
x_16 = l_Lean_Expr_getRevArg_x21___main___closed__1;
x_17 = lean_unsigned_to_nat(522u);
x_18 = lean_unsigned_to_nat(15u);
x_19 = l_Lean_Expr_updateMData_x21___closed__1;
x_20 = l_panicWithPos___at_Lean_Expr_getRevArg_x21___main___spec__1(x_16, x_17, x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
}
block_33:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_expr_update_proj(x_1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_1);
x_27 = l_Lean_Expr_getRevArg_x21___main___closed__1;
x_28 = lean_unsigned_to_nat(527u);
x_29 = lean_unsigned_to_nat(16u);
x_30 = l_Lean_Expr_updateProj_x21___closed__1;
x_31 = l_panicWithPos___at_Lean_Expr_getRevArg_x21___main___spec__1(x_27, x_28, x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
}
}
lean_object* l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_Meta_CheckAssignment_check___main___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
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
x_1 = lean_mk_string("checkAssignment");
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
x_22 = lean_expr_mk_mvar(x_1);
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
x_47 = lean_expr_mk_fvar(x_42);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_expr_mk_mvar(x_1);
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
x_84 = lean_expr_mk_mvar(x_79);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15;
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_expr_mk_mvar(x_1);
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
x_121 = lean_expr_mk_mvar(x_116);
x_122 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure___closed__15;
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_expr_mk_mvar(x_1);
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
uint8_t l_Array_anyMAux___main___at_Lean_Meta_checkAssignment___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_LocalContext_containsFVar(x_8, x_7);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_dec(x_3);
return x_9;
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
lean_object* x_6; uint8_t x_66; 
x_66 = lean_expr_has_expr_mvar(x_3);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = lean_expr_has_fvar(x_3);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_3);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_5);
return x_69;
}
else
{
lean_object* x_70; 
x_70 = lean_box(0);
x_6 = x_70;
goto block_65;
}
}
else
{
lean_object* x_71; 
x_71 = lean_box(0);
x_6 = x_71;
goto block_65;
}
block_65:
{
uint8_t x_7; 
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 3);
x_10 = l_Lean_MetavarContext_getDecl(x_8, x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyMAux___main___at_Lean_Meta_checkAssignment___spec__1(x_10, x_2, x_11);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 1);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_13);
x_16 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_10);
lean_ctor_set(x_16, 3, x_2);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*4 + 1, x_12);
x_17 = l_Lean_Meta_checkAssignment___closed__1;
lean_inc(x_8);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_9);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_3);
x_19 = l_Lean_Meta_CheckAssignment_check___main(x_3, x_16, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_5, 3, x_25);
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_5, 3, x_30);
lean_ctor_set(x_5, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_dec(x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_ctor_set(x_5, 3, x_34);
x_35 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure(x_1, x_2, x_3, x_32, x_4, x_5);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get(x_5, 1);
x_38 = lean_ctor_get(x_5, 2);
x_39 = lean_ctor_get(x_5, 3);
x_40 = lean_ctor_get(x_5, 4);
x_41 = lean_ctor_get(x_5, 5);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_5);
x_42 = l_Lean_MetavarContext_getDecl(x_37, x_1);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Array_anyMAux___main___at_Lean_Meta_checkAssignment___spec__1(x_42, x_2, x_43);
x_45 = lean_ctor_get(x_4, 1);
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*1 + 1);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_45);
x_48 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_1);
lean_ctor_set(x_48, 2, x_42);
lean_ctor_set(x_48, 3, x_2);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*4 + 1, x_44);
x_49 = l_Lean_Meta_checkAssignment___closed__1;
lean_inc(x_37);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_37);
lean_ctor_set(x_50, 1, x_39);
lean_ctor_set(x_50, 2, x_49);
lean_inc(x_3);
x_51 = l_Lean_Meta_CheckAssignment_check___main(x_3, x_48, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 2, x_38);
lean_ctor_set(x_58, 3, x_57);
lean_ctor_set(x_58, 4, x_40);
lean_ctor_set(x_58, 5, x_41);
if (lean_is_scalar(x_54)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_54;
}
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_51, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
lean_dec(x_51);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_36);
lean_ctor_set(x_63, 1, x_37);
lean_ctor_set(x_63, 2, x_38);
lean_ctor_set(x_63, 3, x_62);
lean_ctor_set(x_63, 4, x_40);
lean_ctor_set(x_63, 5, x_41);
x_64 = l___private_Init_Lean_Meta_ExprDefEq_8__checkAssignmentFailure(x_1, x_2, x_3, x_60, x_4, x_63);
return x_64;
}
}
}
}
}
lean_object* l_Array_anyMAux___main___at_Lean_Meta_checkAssignment___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_Meta_checkAssignment___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
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
x_13 = l_Lean_Expr_inhabited;
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
x_9 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_8);
x_10 = lean_mk_array(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_8, x_11);
lean_dec(x_8);
lean_inc(x_4);
x_13 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_4, x_10, x_12);
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
x_23 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_22, x_13, x_7, x_21);
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
x_26 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_25, x_3, x_7, x_2);
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

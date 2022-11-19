// Lean compiler output
// Module: Lean.Meta.Tactic.Apply
// Imports: Init Lean.Util.FindMVar Lean.Meta.SynthInstance Lean.Meta.CollectMVars Lean.Meta.Tactic.Util
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
static lean_object* l_Lean_MVarId_exfalso___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_splitAndCore_go___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_exfalso___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_MVarId_exfalso___lambda__1___closed__1;
static lean_object* l_Lean_MVarId_exfalso___lambda__1___closed__2;
static lean_object* l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_splitAndCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___lambda__1(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_exfalso___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_noConfusion(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_ApplyConfig_approx___default;
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitAndCore___closed__1;
static lean_object* l_Lean_Meta_splitAndCore_go___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_apply_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_ApplyConfig_synthAssignedInstances___default;
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_splitAndCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx___boxed(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__8;
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2;
LEAN_EXPORT uint8_t l_Lean_Meta_ApplyConfig_newGoals___default;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__2;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_apply___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_apply___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitAndCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitAndCore___closed__2;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_Lean_instInhabitedBinderInfo;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__3;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitAndCore_go___closed__5;
static lean_object* l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__1;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitAndCore_go___closed__7;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
static lean_object* l_Lean_Meta_getExpectedNumArgsAux___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_exfalso___lambda__1___closed__5;
lean_object* l_Lean_MVarId_headBetaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitAndCore_go___closed__3;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_exfalso___lambda__1___closed__3;
static lean_object* l_Lean_Meta_splitAndCore_go___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx(uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5;
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_MVarId_apply___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_apply___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitAndCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitAndCore_go___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_MVarId_apply___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_appendParentTag___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_appendParentTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_ApplyNewGoals_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_ApplyNewGoals_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Lean_Meta_ApplyConfig_newGoals___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_ApplyConfig_synthAssignedInstances___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_ApplyConfig_approx___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Expr_getAppFn(x_2);
x_10 = l_Lean_Expr_isMVar(x_9);
lean_dec(x_9);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_getExpectedNumArgsAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getExpectedNumArgsAux___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
lean_ctor_set_uint8(x_8, 5, x_10);
x_11 = l_Lean_Meta_getExpectedNumArgsAux___closed__1;
x_12 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_11, x_2, x_3, x_4, x_5, x_6);
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get_uint8(x_8, 0);
x_22 = lean_ctor_get_uint8(x_8, 1);
x_23 = lean_ctor_get_uint8(x_8, 2);
x_24 = lean_ctor_get_uint8(x_8, 3);
x_25 = lean_ctor_get_uint8(x_8, 4);
x_26 = lean_ctor_get_uint8(x_8, 6);
x_27 = lean_ctor_get_uint8(x_8, 7);
x_28 = lean_ctor_get_uint8(x_8, 8);
x_29 = lean_ctor_get_uint8(x_8, 9);
x_30 = lean_ctor_get_uint8(x_8, 10);
x_31 = lean_ctor_get_uint8(x_8, 11);
x_32 = lean_ctor_get_uint8(x_8, 12);
x_33 = lean_ctor_get_uint8(x_8, 13);
lean_dec(x_8);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_35, 0, x_21);
lean_ctor_set_uint8(x_35, 1, x_22);
lean_ctor_set_uint8(x_35, 2, x_23);
lean_ctor_set_uint8(x_35, 3, x_24);
lean_ctor_set_uint8(x_35, 4, x_25);
lean_ctor_set_uint8(x_35, 5, x_34);
lean_ctor_set_uint8(x_35, 6, x_26);
lean_ctor_set_uint8(x_35, 7, x_27);
lean_ctor_set_uint8(x_35, 8, x_28);
lean_ctor_set_uint8(x_35, 9, x_29);
lean_ctor_set_uint8(x_35, 10, x_30);
lean_ctor_set_uint8(x_35, 11, x_31);
lean_ctor_set_uint8(x_35, 12, x_32);
lean_ctor_set_uint8(x_35, 13, x_33);
lean_ctor_set(x_2, 0, x_35);
x_36 = l_Lean_Meta_getExpectedNumArgsAux___closed__1;
x_37 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_36, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
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
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_44 = x_37;
} else {
 lean_dec_ref(x_37);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_2, 2);
x_49 = lean_ctor_get(x_2, 3);
x_50 = lean_ctor_get(x_2, 4);
x_51 = lean_ctor_get(x_2, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
x_52 = lean_ctor_get_uint8(x_46, 0);
x_53 = lean_ctor_get_uint8(x_46, 1);
x_54 = lean_ctor_get_uint8(x_46, 2);
x_55 = lean_ctor_get_uint8(x_46, 3);
x_56 = lean_ctor_get_uint8(x_46, 4);
x_57 = lean_ctor_get_uint8(x_46, 6);
x_58 = lean_ctor_get_uint8(x_46, 7);
x_59 = lean_ctor_get_uint8(x_46, 8);
x_60 = lean_ctor_get_uint8(x_46, 9);
x_61 = lean_ctor_get_uint8(x_46, 10);
x_62 = lean_ctor_get_uint8(x_46, 11);
x_63 = lean_ctor_get_uint8(x_46, 12);
x_64 = lean_ctor_get_uint8(x_46, 13);
if (lean_is_exclusive(x_46)) {
 x_65 = x_46;
} else {
 lean_dec_ref(x_46);
 x_65 = lean_box(0);
}
x_66 = 1;
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 0, 14);
} else {
 x_67 = x_65;
}
lean_ctor_set_uint8(x_67, 0, x_52);
lean_ctor_set_uint8(x_67, 1, x_53);
lean_ctor_set_uint8(x_67, 2, x_54);
lean_ctor_set_uint8(x_67, 3, x_55);
lean_ctor_set_uint8(x_67, 4, x_56);
lean_ctor_set_uint8(x_67, 5, x_66);
lean_ctor_set_uint8(x_67, 6, x_57);
lean_ctor_set_uint8(x_67, 7, x_58);
lean_ctor_set_uint8(x_67, 8, x_59);
lean_ctor_set_uint8(x_67, 9, x_60);
lean_ctor_set_uint8(x_67, 10, x_61);
lean_ctor_set_uint8(x_67, 11, x_62);
lean_ctor_set_uint8(x_67, 12, x_63);
lean_ctor_set_uint8(x_67, 13, x_64);
x_68 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_47);
lean_ctor_set(x_68, 2, x_48);
lean_ctor_set(x_68, 3, x_49);
lean_ctor_set(x_68, 4, x_50);
lean_ctor_set(x_68, 5, x_51);
x_69 = l_Lean_Meta_getExpectedNumArgsAux___closed__1;
x_70 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_69, x_68, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getExpectedNumArgsAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getExpectedNumArgsAux(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
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
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("apply", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to unify", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nwith", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = l_Lean_indentExpr(x_2);
x_10 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__6;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_indentExpr(x_3);
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__8;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2;
x_19 = l_Lean_Meta_throwTacticEx___rarg(x_18, x_1, x_17, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_9;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to assign synthesized instance", 37);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_8, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_63; uint8_t x_64; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_8, x_16);
lean_dec(x_8);
x_18 = lean_nat_sub(x_7, x_17);
x_19 = lean_nat_sub(x_18, x_16);
lean_dec(x_18);
x_63 = lean_array_get_size(x_4);
x_64 = lean_nat_dec_lt(x_19, x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_65 = l_Lean_instInhabitedBinderInfo;
x_66 = lean_box(x_65);
x_67 = l___private_Init_Util_0__outOfBounds___rarg(x_66);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
x_69 = l_Lean_BinderInfo_isInstImplicit(x_68);
if (x_69 == 0)
{
lean_dec(x_19);
x_8 = x_17;
goto _start;
}
else
{
uint8_t x_71; 
x_71 = lean_nat_dec_lt(x_19, x_6);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_19);
x_72 = l_Lean_instInhabitedExpr;
x_73 = l___private_Init_Util_0__outOfBounds___rarg(x_72);
x_20 = x_73;
goto block_62;
}
else
{
lean_object* x_74; 
x_74 = lean_array_fget(x_3, x_19);
lean_dec(x_19);
x_20 = x_74;
goto block_62;
}
}
}
else
{
lean_object* x_75; uint8_t x_76; uint8_t x_77; 
x_75 = lean_array_fget(x_4, x_19);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
x_77 = l_Lean_BinderInfo_isInstImplicit(x_76);
if (x_77 == 0)
{
lean_dec(x_19);
x_8 = x_17;
goto _start;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_lt(x_19, x_6);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_19);
x_80 = l_Lean_instInhabitedExpr;
x_81 = l___private_Init_Util_0__outOfBounds___rarg(x_80);
x_20 = x_81;
goto block_62;
}
else
{
lean_object* x_82; 
x_82 = lean_array_fget(x_3, x_19);
lean_dec(x_19);
x_20 = x_82;
goto block_62;
}
}
}
block_62:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_20);
x_21 = l_Lean_Expr_mvarId_x21(x_20);
x_22 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_21, x_9, x_10, x_11, x_12, x_13);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
if (x_5 == 0)
{
uint8_t x_58; 
x_58 = lean_unbox(x_23);
lean_dec(x_23);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_25 = x_59;
goto block_57;
}
else
{
lean_dec(x_20);
x_8 = x_17;
x_13 = x_24;
goto _start;
}
}
else
{
lean_object* x_61; 
lean_dec(x_23);
x_61 = lean_box(0);
x_25 = x_61;
goto block_57;
}
block_57:
{
lean_object* x_26; 
lean_dec(x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_20);
x_26 = lean_infer_type(x_20, x_9, x_10, x_11, x_12, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_30 = l_Lean_Meta_synthInstance(x_27, x_29, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_33 = l_Lean_Meta_isExprDefEq(x_20, x_31, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_17);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__3;
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_37, x_9, x_10, x_11, x_12, x_36);
lean_dec(x_12);
lean_dec(x_10);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_dec(x_33);
x_8 = x_17;
x_13 = x_43;
goto _start;
}
}
else
{
uint8_t x_45; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_33);
if (x_45 == 0)
{
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
return x_30;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_30, 0);
x_51 = lean_ctor_get(x_30, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_30);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_26);
if (x_53 == 0)
{
return x_26;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_26, 0);
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_26);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_13);
return x_84;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_get_size(x_3);
lean_inc(x_11);
x_12 = l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1(x_1, x_2, x_3, x_4, x_5, x_11, x_11, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_synthAppInstances(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_appendParentTag___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_6, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_61; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_6, x_14);
lean_dec(x_6);
x_16 = lean_nat_sub(x_5, x_15);
x_17 = lean_nat_sub(x_16, x_14);
lean_dec(x_16);
x_61 = lean_nat_dec_lt(x_17, x_4);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Lean_instInhabitedExpr;
x_63 = l___private_Init_Util_0__outOfBounds___rarg(x_62);
x_18 = x_63;
goto block_60;
}
else
{
lean_object* x_64; 
x_64 = lean_array_fget(x_1, x_17);
x_18 = x_64;
goto block_60;
}
block_60:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l_Lean_Expr_mvarId_x21(x_18);
lean_inc(x_19);
x_20 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_19, x_7, x_8, x_9, x_10, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_array_get_size(x_2);
x_25 = lean_nat_dec_lt(x_17, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
lean_dec(x_17);
x_26 = l_Lean_instInhabitedBinderInfo;
x_27 = lean_box(x_26);
x_28 = l___private_Init_Util_0__outOfBounds___rarg(x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
x_30 = l_Lean_BinderInfo_isInstImplicit(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_inc(x_19);
x_31 = l_Lean_MVarId_getTag(x_19, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_3);
x_34 = l_Lean_Meta_appendTag(x_3, x_32);
x_35 = l_Lean_MVarId_setTag(x_19, x_34, x_7, x_8, x_9, x_10, x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_6 = x_15;
x_11 = x_36;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_dec(x_19);
x_6 = x_15;
x_11 = x_23;
goto _start;
}
}
else
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; 
x_43 = lean_array_fget(x_2, x_17);
lean_dec(x_17);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
x_45 = l_Lean_BinderInfo_isInstImplicit(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_inc(x_19);
x_46 = l_Lean_MVarId_getTag(x_19, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_3);
x_49 = l_Lean_Meta_appendTag(x_3, x_47);
x_50 = l_Lean_MVarId_setTag(x_19, x_49, x_7, x_8, x_9, x_10, x_48);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_6 = x_15;
x_11 = x_51;
goto _start;
}
else
{
uint8_t x_53; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_dec(x_19);
x_6 = x_15;
x_11 = x_23;
goto _start;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_19);
lean_dec(x_17);
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
lean_dec(x_20);
x_6 = x_15;
x_11 = x_58;
goto _start;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_6);
lean_dec(x_3);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_11);
return x_66;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_array_get_size(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Name_isAnonymous(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_9);
lean_inc(x_13);
x_17 = l_Nat_forM_loop___at_Lean_Meta_appendParentTag___spec__1(x_2, x_3, x_11, x_13, x_13, x_13, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_box(0);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_free_object(x_9);
lean_dec(x_3);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_13);
lean_dec(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_21 = l_Lean_instInhabitedExpr;
x_22 = l___private_Init_Util_0__outOfBounds___rarg(x_21);
x_23 = l_Lean_Expr_mvarId_x21(x_22);
x_24 = l_Lean_MVarId_setTag(x_23, x_11, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_array_fget(x_2, x_19);
lean_dec(x_2);
x_26 = l_Lean_Expr_mvarId_x21(x_25);
x_27 = l_Lean_MVarId_setTag(x_26, x_11, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_array_get_size(x_2);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_dec_eq(x_30, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Name_isAnonymous(x_28);
if (x_33 == 0)
{
lean_object* x_34; 
lean_inc(x_30);
x_34 = l_Nat_forM_loop___at_Lean_Meta_appendParentTag___spec__1(x_2, x_3, x_28, x_30, x_30, x_30, x_4, x_5, x_6, x_7, x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_2);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
else
{
lean_object* x_37; uint8_t x_38; 
lean_dec(x_3);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_30);
lean_dec(x_30);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
x_39 = l_Lean_instInhabitedExpr;
x_40 = l___private_Init_Util_0__outOfBounds___rarg(x_39);
x_41 = l_Lean_Expr_mvarId_x21(x_40);
x_42 = l_Lean_MVarId_setTag(x_41, x_28, x_4, x_5, x_6, x_7, x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_array_fget(x_2, x_37);
lean_dec(x_2);
x_44 = l_Lean_Expr_mvarId_x21(x_43);
x_45 = l_Lean_MVarId_setTag(x_44, x_28, x_4, x_5, x_6, x_7, x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_9);
if (x_46 == 0)
{
return x_9;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_9, 0);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_9);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_appendParentTag___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_forM_loop___at_Lean_Meta_appendParentTag___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_11 = l_Lean_Meta_synthAppInstances(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Meta_appendParentTag(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_postprocessAppMVars(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Expr_mvarId_x21(x_1);
x_4 = lean_name_eq(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_uget(x_2, x_3);
x_12 = lean_expr_eqv(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = lean_infer_type(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_17, 0, x_1);
x_18 = lean_box(0);
x_19 = l_Lean_FindMVar_main(x_17, x_15, x_18);
if (lean_obj_tag(x_19) == 0)
{
size_t x_20; size_t x_21; 
lean_free_object(x_13);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_1);
x_28 = lean_box(0);
x_29 = l_Lean_FindMVar_main(x_27, x_25, x_28);
if (lean_obj_tag(x_29) == 0)
{
size_t x_30; size_t x_31; 
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
x_9 = x_26;
goto _start;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
size_t x_40; size_t x_41; 
lean_dec(x_11);
x_40 = 1;
x_41 = lean_usize_add(x_3, x_40);
x_3 = x_41;
goto _start;
}
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_9);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_8, x_8);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(x_1, x_2, x_18, x_19, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_16 = l_Lean_Expr_mvarId_x21(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(x_12, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_array_push(x_14, x_16);
lean_ctor_set(x_5, 0, x_21);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_10 = x_20;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_array_push(x_15, x_16);
lean_ctor_set(x_5, 1, x_26);
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_3 = x_28;
x_10 = x_25;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_14);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
lean_inc(x_12);
x_36 = l_Lean_Expr_mvarId_x21(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_37 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(x_12, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_array_push(x_34, x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
x_43 = 1;
x_44 = lean_usize_add(x_3, x_43);
x_3 = x_44;
x_5 = x_42;
x_10 = x_40;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_array_push(x_35, x_36);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set(x_48, 1, x_47);
x_49 = 1;
x_50 = lean_usize_add(x_3, x_49);
x_3 = x_50;
x_5 = x_48;
x_10 = x_46;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_52 = lean_ctor_get(x_37, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_37, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_54 = x_37;
} else {
 lean_dec_ref(x_37);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_5);
lean_ctor_set(x_56, 1, x_10);
return x_56;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_7, x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__2;
x_18 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___spec__1(x_1, x_1, x_15, x_16, x_17, x_2, x_3, x_4, x_5, x_6);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_mvarId_x21(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Expr_mvarId_x21(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (x_2) {
case 0:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(x_1, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_to_list(lean_box(0), x_11);
x_14 = lean_array_to_list(lean_box(0), x_12);
x_15 = l_List_appendTR___rarg(x_13, x_14);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_to_list(lean_box(0), x_18);
x_21 = lean_array_to_list(lean_box(0), x_19);
x_22 = l_List_appendTR___rarg(x_20, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
case 1:
{
lean_object* x_28; 
x_28 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(x_1, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_array_to_list(lean_box(0), x_31);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_array_to_list(lean_box(0), x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
default: 
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_array_to_list(lean_box(0), x_1);
x_43 = lean_box(0);
x_44 = l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___spec__1(x_42, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_7);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, 2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isExprDefEqGuarded(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; uint8_t x_16; 
x_14 = 1;
lean_ctor_set_uint8(x_12, 0, x_14);
lean_ctor_set_uint8(x_12, 1, x_14);
lean_ctor_set_uint8(x_12, 2, x_14);
x_15 = l_Lean_Meta_isExprDefEqGuarded(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get_uint8(x_12, 3);
x_21 = lean_ctor_get_uint8(x_12, 4);
x_22 = lean_ctor_get_uint8(x_12, 5);
x_23 = lean_ctor_get_uint8(x_12, 6);
x_24 = lean_ctor_get_uint8(x_12, 7);
x_25 = lean_ctor_get_uint8(x_12, 8);
x_26 = lean_ctor_get_uint8(x_12, 9);
x_27 = lean_ctor_get_uint8(x_12, 10);
x_28 = lean_ctor_get_uint8(x_12, 11);
x_29 = lean_ctor_get_uint8(x_12, 12);
x_30 = lean_ctor_get_uint8(x_12, 13);
lean_dec(x_12);
x_31 = 1;
x_32 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_32, 0, x_31);
lean_ctor_set_uint8(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, 2, x_31);
lean_ctor_set_uint8(x_32, 3, x_20);
lean_ctor_set_uint8(x_32, 4, x_21);
lean_ctor_set_uint8(x_32, 5, x_22);
lean_ctor_set_uint8(x_32, 6, x_23);
lean_ctor_set_uint8(x_32, 7, x_24);
lean_ctor_set_uint8(x_32, 8, x_25);
lean_ctor_set_uint8(x_32, 9, x_26);
lean_ctor_set_uint8(x_32, 10, x_27);
lean_ctor_set_uint8(x_32, 11, x_28);
lean_ctor_set_uint8(x_32, 12, x_29);
lean_ctor_set_uint8(x_32, 13, x_30);
lean_ctor_set(x_4, 0, x_32);
x_33 = l_Lean_Meta_isExprDefEqGuarded(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_ctor_get(x_4, 1);
x_40 = lean_ctor_get(x_4, 2);
x_41 = lean_ctor_get(x_4, 3);
x_42 = lean_ctor_get(x_4, 4);
x_43 = lean_ctor_get(x_4, 5);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_4);
x_44 = lean_ctor_get_uint8(x_38, 3);
x_45 = lean_ctor_get_uint8(x_38, 4);
x_46 = lean_ctor_get_uint8(x_38, 5);
x_47 = lean_ctor_get_uint8(x_38, 6);
x_48 = lean_ctor_get_uint8(x_38, 7);
x_49 = lean_ctor_get_uint8(x_38, 8);
x_50 = lean_ctor_get_uint8(x_38, 9);
x_51 = lean_ctor_get_uint8(x_38, 10);
x_52 = lean_ctor_get_uint8(x_38, 11);
x_53 = lean_ctor_get_uint8(x_38, 12);
x_54 = lean_ctor_get_uint8(x_38, 13);
if (lean_is_exclusive(x_38)) {
 x_55 = x_38;
} else {
 lean_dec_ref(x_38);
 x_55 = lean_box(0);
}
x_56 = 1;
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 0, 14);
} else {
 x_57 = x_55;
}
lean_ctor_set_uint8(x_57, 0, x_56);
lean_ctor_set_uint8(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, 2, x_56);
lean_ctor_set_uint8(x_57, 3, x_44);
lean_ctor_set_uint8(x_57, 4, x_45);
lean_ctor_set_uint8(x_57, 5, x_46);
lean_ctor_set_uint8(x_57, 6, x_47);
lean_ctor_set_uint8(x_57, 7, x_48);
lean_ctor_set_uint8(x_57, 8, x_49);
lean_ctor_set_uint8(x_57, 9, x_50);
lean_ctor_set_uint8(x_57, 10, x_51);
lean_ctor_set_uint8(x_57, 11, x_52);
lean_ctor_set_uint8(x_57, 12, x_53);
lean_ctor_set_uint8(x_57, 13, x_54);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_39);
lean_ctor_set(x_58, 2, x_40);
lean_ctor_set(x_58, 3, x_41);
lean_ctor_set(x_58, 4, x_42);
lean_ctor_set(x_58, 5, x_43);
x_59 = l_Lean_Meta_isExprDefEqGuarded(x_2, x_3, x_58, x_5, x_6, x_7, x_8);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_nat_dec_lt(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_6);
lean_inc(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_16 = 1;
x_17 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_4, x_16, x_15, x_17, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg(x_1, x_22, x_3, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_8);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_28 = l_Lean_Meta_saveState___rarg(x_8, x_9, x_10, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_6);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_6);
x_32 = 1;
x_33 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_34 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_4, x_32, x_31, x_33, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_42 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(x_2, x_41, x_3, x_7, x_8, x_9, x_10, x_37);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_36);
lean_dec(x_40);
lean_dec(x_38);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l_Lean_Meta_SavedState_restore(x_29, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_29);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_6, x_48);
lean_dec(x_6);
x_6 = x_49;
x_11 = x_47;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_42, 0);
lean_dec(x_52);
lean_ctor_set(x_36, 1, x_40);
lean_ctor_set(x_36, 0, x_38);
lean_ctor_set(x_42, 0, x_36);
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_dec(x_42);
lean_ctor_set(x_36, 1, x_40);
lean_ctor_set(x_36, 0, x_38);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_36, 0);
x_56 = lean_ctor_get(x_36, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_36);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_57 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(x_2, x_56, x_3, x_7, x_8, x_9, x_10, x_37);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_55);
lean_dec(x_38);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l_Lean_Meta_SavedState_restore(x_29, x_7, x_8, x_9, x_10, x_60);
lean_dec(x_29);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_6, x_63);
lean_dec(x_6);
x_6 = x_64;
x_11 = x_62;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_67 = x_57;
} else {
 lean_dec_ref(x_57);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_38);
lean_ctor_set(x_68, 1, x_55);
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
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_34);
if (x_70 == 0)
{
return x_34;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_34, 0);
x_72 = lean_ctor_get(x_34, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_34);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_apply_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lean_MVarId_apply___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_name_eq(x_1, x_4);
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
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_apply___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_MVarId_headBetaType(x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_1 = x_10;
x_6 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_List_elem___at_Lean_MVarId_apply___spec__1(x_7, x_1);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (x_8 == 0)
{
lean_object* x_11; 
x_11 = lean_array_push(x_5, x_7);
x_3 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_11);
x_12 = l_Lean_Expr_mvarId_x21(x_11);
x_13 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_12, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_array_push(x_4, x_11);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_4 = x_17;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_dec(x_11);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = 1;
x_23 = lean_usize_add(x_2, x_22);
x_2 = x_23;
x_9 = x_21;
goto _start;
}
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_9);
return x_25;
}
}
}
static lean_object* _init_l_Lean_MVarId_apply___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
x_2 = lean_array_to_list(lean_box(0), x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_14 = l_Lean_MVarId_apply_go(x_1, x_2, x_3, x_4, x_7, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get_uint8(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_17);
lean_inc(x_1);
x_20 = l_Lean_Meta_postprocessAppMVars(x_5, x_1, x_17, x_18, x_19, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_6, x_8, x_9, x_10, x_11, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_17);
lean_inc(x_23);
x_25 = l_Lean_mkAppN(x_23, x_17);
x_26 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_25, x_8, x_9, x_10, x_11, x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_get_size(x_17);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
if (x_30 == 0)
{
lean_object* x_85; 
lean_dec(x_28);
lean_dec(x_17);
x_85 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
x_31 = x_85;
x_32 = x_27;
goto block_84;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_28, x_28);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_28);
lean_dec(x_17);
x_87 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
x_31 = x_87;
x_32 = x_27;
goto block_84;
}
else
{
size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = 0;
x_89 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_90 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
x_91 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__4(x_17, x_88, x_89, x_90, x_8, x_9, x_10, x_11, x_27);
lean_dec(x_17);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_31 = x_92;
x_32 = x_93;
goto block_84;
}
}
block_84:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_33 = l_Lean_Meta_getMVarsNoDelayed(x_23, x_8, x_9, x_10, x_11, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get_uint8(x_2, 0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_37 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(x_31, x_36, x_8, x_9, x_10, x_11, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_array_get_size(x_34);
x_41 = lean_nat_dec_lt(x_29, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_34);
x_42 = l_Lean_MVarId_apply___lambda__1___closed__1;
x_43 = l_List_appendTR___rarg(x_38, x_42);
lean_inc(x_43);
x_44 = l_List_forM___at_Lean_MVarId_apply___spec__2(x_43, x_8, x_9, x_10, x_11, x_39);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_43);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_40, x_40);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_40);
lean_dec(x_34);
x_54 = l_Lean_MVarId_apply___lambda__1___closed__1;
x_55 = l_List_appendTR___rarg(x_38, x_54);
lean_inc(x_55);
x_56 = l_List_forM___at_Lean_MVarId_apply___spec__2(x_55, x_8, x_9, x_10, x_11, x_39);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_55);
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
size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = 0;
x_66 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_67 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
x_68 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__3(x_38, x_34, x_65, x_66, x_67);
lean_dec(x_34);
x_69 = lean_array_to_list(lean_box(0), x_68);
x_70 = l_List_appendTR___rarg(x_38, x_69);
lean_inc(x_70);
x_71 = l_List_forM___at_Lean_MVarId_apply___spec__2(x_70, x_8, x_9, x_10, x_11, x_39);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_70);
x_76 = !lean_is_exclusive(x_71);
if (x_76 == 0)
{
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_71, 0);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_71);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_80 = !lean_is_exclusive(x_37);
if (x_80 == 0)
{
return x_37;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_37, 0);
x_82 = lean_ctor_get(x_37, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_37);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_20);
if (x_94 == 0)
{
return x_20;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_20, 0);
x_96 = lean_ctor_get(x_20, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_20);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_14);
if (x_98 == 0)
{
return x_14;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_14, 0);
x_100 = lean_ctor_get(x_14, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_14);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_1);
x_12 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_15 = lean_infer_type(x_3, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_18 = l_Lean_Meta_getExpectedNumArgsAux(x_16, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_24 = l_Lean_Meta_getExpectedNumArgs(x_13, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_sub(x_23, x_25);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_23, x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_28);
x_31 = l_Lean_MVarId_apply___lambda__1(x_1, x_4, x_13, x_16, x_2, x_3, x_30, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_4);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_dec(x_18);
x_37 = lean_ctor_get(x_19, 0);
lean_inc(x_37);
lean_dec(x_19);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_37, x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_38);
x_41 = l_Lean_MVarId_apply___lambda__1(x_1, x_4, x_13, x_16, x_2, x_3, x_40, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_4);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
return x_15;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_15, 0);
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_15);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_12);
if (x_50 == 0)
{
return x_12;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_12, 0);
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_12);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_10);
if (x_54 == 0)
{
return x_10;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_10, 0);
x_56 = lean_ctor_get(x_10, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_10);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lambda__2), 9, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_MVarId_apply___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_MVarId_apply___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_apply___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forM___at_Lean_MVarId_apply___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_apply___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_apply(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_apply(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_splitAndCore_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("And", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitAndCore_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_splitAndCore_go___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_splitAndCore_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("h", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitAndCore_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_splitAndCore_go___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_splitAndCore_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("intro", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitAndCore_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_splitAndCore_go___closed__1;
x_2 = l_Lean_Meta_splitAndCore_go___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_splitAndCore_go___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_splitAndCore_go___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitAndCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_whnf(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_splitAndCore_go___closed__2;
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Expr_isAppOfArity(x_10, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_15 = lean_st_ref_get(x_7, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_3, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_18);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_20, x_21);
lean_dec(x_20);
x_23 = l_Lean_Meta_splitAndCore_go___closed__4;
x_24 = lean_name_append_index_after(x_23, x_22);
x_25 = l_Lean_Name_append(x_1, x_24);
x_26 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_10, x_25, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_6);
lean_dec(x_5);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_7, x_28);
lean_dec(x_7);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_take(x_3, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_27);
x_34 = l_Lean_Expr_mvarId_x21(x_27);
x_35 = lean_array_push(x_32, x_34);
x_36 = lean_st_ref_set(x_3, x_35, x_33);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_27);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = l_Lean_Expr_appFn_x21(x_10);
x_42 = l_Lean_Expr_appArg_x21(x_41);
lean_dec(x_41);
x_43 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_42);
x_44 = l_Lean_Meta_splitAndCore_go(x_1, x_42, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_43);
x_47 = l_Lean_Meta_splitAndCore_go(x_1, x_43, x_3, x_4, x_5, x_6, x_7, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = l_Lean_Meta_splitAndCore_go___closed__7;
x_51 = l_Lean_mkApp4(x_50, x_42, x_43, x_45, x_49);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = l_Lean_Meta_splitAndCore_go___closed__7;
x_55 = l_Lean_mkApp4(x_54, x_42, x_43, x_45, x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_42);
x_57 = !lean_is_exclusive(x_47);
if (x_57 == 0)
{
return x_47;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_47, 0);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_47);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_44);
if (x_61 == 0)
{
return x_44;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_44, 0);
x_63 = lean_ctor_get(x_44, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_44);
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
uint8_t x_65; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_9);
if (x_65 == 0)
{
return x_9;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_9, 0);
x_67 = lean_ctor_get(x_9, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_9);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitAndCore_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_splitAndCore_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitAndCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_MVarId_getType_x27(x_1, x_3, x_4, x_5, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Meta_splitAndCore_go___closed__2;
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Expr_isAppOfArity(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_19; 
lean_free_object(x_10);
lean_inc(x_1);
x_19 = l_Lean_MVarId_getTag(x_1, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_6, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
x_25 = lean_st_mk_ref(x_24, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l_Lean_Meta_splitAndCore_go(x_20, x_12, x_26, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_6, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_26, x_32);
lean_dec(x_26);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_29, x_3, x_4, x_5, x_6, x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_array_to_list(lean_box(0), x_34);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_array_to_list(lean_box(0), x_34);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_10, 0);
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_10);
x_53 = l_Lean_Meta_splitAndCore_go___closed__2;
x_54 = lean_unsigned_to_nat(2u);
x_55 = l_Lean_Expr_isAppOfArity(x_51, x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_52);
return x_58;
}
else
{
lean_object* x_59; 
lean_inc(x_1);
x_59 = l_Lean_MVarId_getTag(x_1, x_3, x_4, x_5, x_6, x_52);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_st_ref_get(x_6, x_61);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
x_65 = lean_st_mk_ref(x_64, x_63);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_68 = l_Lean_Meta_splitAndCore_go(x_60, x_51, x_66, x_3, x_4, x_5, x_6, x_67);
lean_dec(x_60);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_st_ref_get(x_6, x_70);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_st_ref_get(x_66, x_72);
lean_dec(x_66);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_69, x_3, x_4, x_5, x_6, x_75);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_79 = lean_array_to_list(lean_box(0), x_74);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_66);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_81 = lean_ctor_get(x_68, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_68, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_83 = x_68;
} else {
 lean_dec_ref(x_68);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_85 = lean_ctor_get(x_59, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_59, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_87 = x_59;
} else {
 lean_dec_ref(x_59);
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
uint8_t x_89; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_10);
if (x_89 == 0)
{
return x_10;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_10, 0);
x_91 = lean_ctor_get(x_10, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_10);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_8);
if (x_93 == 0)
{
return x_8;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_8, 0);
x_95 = lean_ctor_get(x_8, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_8);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
static lean_object* _init_l_Lean_Meta_splitAndCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("splitAnd", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitAndCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_splitAndCore___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitAndCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Meta_splitAndCore___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_splitAndCore___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_splitAndCore(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_splitAndCore(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_exfalso___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_exfalso___lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elim", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_exfalso___lambda__1___closed__1;
x_2 = l_Lean_MVarId_exfalso___lambda__1___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_1);
x_10 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_11, x_3, x_4, x_5, x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_14);
x_16 = l_Lean_Meta_getLevel(x_14, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = l_Lean_MVarId_getTag(x_1, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l_Lean_MVarId_exfalso___lambda__1___closed__3;
lean_inc(x_3);
x_24 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_23, x_20, x_3, x_4, x_5, x_6, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_22);
x_28 = l_Lean_MVarId_exfalso___lambda__1___closed__5;
x_29 = l_Lean_Expr_const___override(x_28, x_27);
lean_inc(x_25);
x_30 = l_Lean_mkAppB(x_29, x_14, x_25);
x_31 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_30, x_3, x_4, x_5, x_6, x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Lean_Expr_mvarId_x21(x_25);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lean_Expr_mvarId_x21(x_25);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
uint8_t x_42; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_16);
if (x_42 == 0)
{
return x_16;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_16, 0);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_16);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_10);
if (x_46 == 0)
{
return x_10;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_10, 0);
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_10);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
static lean_object* _init_l_Lean_MVarId_exfalso___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("exfalso", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_exfalso___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_MVarId_exfalso___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FindMVar(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CollectMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindMVar(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___closed__1 = _init_l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_ApplyNewGoals_noConfusion___rarg___closed__1);
l_Lean_Meta_ApplyConfig_newGoals___default = _init_l_Lean_Meta_ApplyConfig_newGoals___default();
l_Lean_Meta_ApplyConfig_synthAssignedInstances___default = _init_l_Lean_Meta_ApplyConfig_synthAssignedInstances___default();
l_Lean_Meta_ApplyConfig_approx___default = _init_l_Lean_Meta_ApplyConfig_approx___default();
l_Lean_Meta_getExpectedNumArgsAux___closed__1 = _init_l_Lean_Meta_getExpectedNumArgsAux___closed__1();
lean_mark_persistent(l_Lean_Meta_getExpectedNumArgsAux___closed__1);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__6 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__6);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__7 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__7);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__8 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__8);
l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__1 = _init_l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__1);
l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__2 = _init_l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__2);
l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__3 = _init_l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__3();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_synthAppInstances___spec__1___closed__3);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__2 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__2);
l_Lean_MVarId_apply___lambda__1___closed__1 = _init_l_Lean_MVarId_apply___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_apply___lambda__1___closed__1);
l_Lean_Meta_splitAndCore_go___closed__1 = _init_l_Lean_Meta_splitAndCore_go___closed__1();
lean_mark_persistent(l_Lean_Meta_splitAndCore_go___closed__1);
l_Lean_Meta_splitAndCore_go___closed__2 = _init_l_Lean_Meta_splitAndCore_go___closed__2();
lean_mark_persistent(l_Lean_Meta_splitAndCore_go___closed__2);
l_Lean_Meta_splitAndCore_go___closed__3 = _init_l_Lean_Meta_splitAndCore_go___closed__3();
lean_mark_persistent(l_Lean_Meta_splitAndCore_go___closed__3);
l_Lean_Meta_splitAndCore_go___closed__4 = _init_l_Lean_Meta_splitAndCore_go___closed__4();
lean_mark_persistent(l_Lean_Meta_splitAndCore_go___closed__4);
l_Lean_Meta_splitAndCore_go___closed__5 = _init_l_Lean_Meta_splitAndCore_go___closed__5();
lean_mark_persistent(l_Lean_Meta_splitAndCore_go___closed__5);
l_Lean_Meta_splitAndCore_go___closed__6 = _init_l_Lean_Meta_splitAndCore_go___closed__6();
lean_mark_persistent(l_Lean_Meta_splitAndCore_go___closed__6);
l_Lean_Meta_splitAndCore_go___closed__7 = _init_l_Lean_Meta_splitAndCore_go___closed__7();
lean_mark_persistent(l_Lean_Meta_splitAndCore_go___closed__7);
l_Lean_Meta_splitAndCore___closed__1 = _init_l_Lean_Meta_splitAndCore___closed__1();
lean_mark_persistent(l_Lean_Meta_splitAndCore___closed__1);
l_Lean_Meta_splitAndCore___closed__2 = _init_l_Lean_Meta_splitAndCore___closed__2();
lean_mark_persistent(l_Lean_Meta_splitAndCore___closed__2);
l_Lean_MVarId_exfalso___lambda__1___closed__1 = _init_l_Lean_MVarId_exfalso___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_exfalso___lambda__1___closed__1);
l_Lean_MVarId_exfalso___lambda__1___closed__2 = _init_l_Lean_MVarId_exfalso___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_exfalso___lambda__1___closed__2);
l_Lean_MVarId_exfalso___lambda__1___closed__3 = _init_l_Lean_MVarId_exfalso___lambda__1___closed__3();
lean_mark_persistent(l_Lean_MVarId_exfalso___lambda__1___closed__3);
l_Lean_MVarId_exfalso___lambda__1___closed__4 = _init_l_Lean_MVarId_exfalso___lambda__1___closed__4();
lean_mark_persistent(l_Lean_MVarId_exfalso___lambda__1___closed__4);
l_Lean_MVarId_exfalso___lambda__1___closed__5 = _init_l_Lean_MVarId_exfalso___lambda__1___closed__5();
lean_mark_persistent(l_Lean_MVarId_exfalso___lambda__1___closed__5);
l_Lean_MVarId_exfalso___closed__1 = _init_l_Lean_MVarId_exfalso___closed__1();
lean_mark_persistent(l_Lean_MVarId_exfalso___closed__1);
l_Lean_MVarId_exfalso___closed__2 = _init_l_Lean_MVarId_exfalso___closed__2();
lean_mark_persistent(l_Lean_MVarId_exfalso___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

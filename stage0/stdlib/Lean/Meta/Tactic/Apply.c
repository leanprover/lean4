// Lean compiler output
// Module: Lean.Meta.Tactic.Apply
// Imports: Lean.Util.FindMVar Lean.Meta.SynthInstance Lean.Meta.CollectMVars Lean.Meta.Tactic.Util Lean.PrettyPrinter
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__4;
static lean_object* l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_exfalso___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_exfalso___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_MVarId_getMVarDependencies_addMVars___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_nthConstructor___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_synthAppInstances___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_splitAndCore_go___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__1;
static lean_object* l_Lean_MVarId_nthConstructor___lambda__2___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_MVarId_headBetaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4;
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_propext___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_iffOfEq___closed__1;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances_step(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_nthConstructor___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_nthConstructor___lambda__2___closed__5;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_exfalso___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1;
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_splitAndCore___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___spec__1(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3;
static lean_object* l_Lean_MVarId_exfalso___lambda__1___closed__3;
static lean_object* l_Lean_Meta_synthAppInstances_step___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_splitAndCore_go___closed__6;
static lean_object* l_Lean_MVarId_propext___lambda__1___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_appendParentTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2;
lean_object* l_Lean_throwError___at_Lean_Meta_exactlyOne___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthAppInstances_step___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_synthAppInstances_step___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_MVarId_splitAndCore_go___closed__4;
extern uint8_t l_Lean_instInhabitedBinderInfo;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__2;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_proofIrrelHeq___closed__2;
static lean_object* l_Lean_MVarId_splitAndCore___closed__2;
static lean_object* l_Lean_MVarId_nthConstructor___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__4;
static lean_object* l_Lean_MVarId_subsingletonElim___lambda__1___closed__1;
static lean_object* l_Lean_MVarId_subsingletonElim___closed__2;
static lean_object* l_Lean_MVarId_splitAndCore_go___closed__3;
static lean_object* l_Lean_MVarId_subsingletonElim___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_proofIrrelHeq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_apply___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_nthConstructor___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_nthConstructor___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_apply___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_splitAndCore_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_synthAppInstances___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_nthConstructor___lambda__1___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_proofIrrelHeq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_MVarId_iffOfEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_MVarId_exfalso___lambda__1___closed__4;
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getExpectedNumArgsAux___closed__1;
static lean_object* l_Lean_MVarId_splitAndCore_go___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_iffOfEq___lambda__1___closed__1;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_exfalso___lambda__1___closed__5;
static lean_object* l_Lean_MVarId_nthConstructor___lambda__2___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_propext___lambda__1___closed__4;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_MVarId_iffOfEq___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_Meta_appendParentTag___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__3;
static lean_object* l_Lean_MVarId_apply___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_MVarId_propext___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_iffOfEq___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__3;
lean_object* l_Lean_MVarId_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_exfalso___lambda__1___closed__1;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances_step___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_MVarId_subsingletonElim___closed__1;
static lean_object* l_Lean_MVarId_splitAndCore_go___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances___spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_MVarId_proofIrrelHeq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_Lean_MVarId_proofIrrelHeq___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_propext___lambda__1___closed__5;
lean_object* l_List_length___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
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
uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = 1;
lean_ctor_set_uint8(x_8, 9, x_10);
x_11 = l_Lean_Meta_getExpectedNumArgsAux___closed__1;
x_12 = 0;
x_13 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_11, x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_22 = lean_ctor_get_uint8(x_8, 0);
x_23 = lean_ctor_get_uint8(x_8, 1);
x_24 = lean_ctor_get_uint8(x_8, 2);
x_25 = lean_ctor_get_uint8(x_8, 3);
x_26 = lean_ctor_get_uint8(x_8, 4);
x_27 = lean_ctor_get_uint8(x_8, 5);
x_28 = lean_ctor_get_uint8(x_8, 6);
x_29 = lean_ctor_get_uint8(x_8, 7);
x_30 = lean_ctor_get_uint8(x_8, 8);
x_31 = lean_ctor_get_uint8(x_8, 10);
x_32 = lean_ctor_get_uint8(x_8, 11);
x_33 = lean_ctor_get_uint8(x_8, 12);
lean_dec(x_8);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_35, 0, x_22);
lean_ctor_set_uint8(x_35, 1, x_23);
lean_ctor_set_uint8(x_35, 2, x_24);
lean_ctor_set_uint8(x_35, 3, x_25);
lean_ctor_set_uint8(x_35, 4, x_26);
lean_ctor_set_uint8(x_35, 5, x_27);
lean_ctor_set_uint8(x_35, 6, x_28);
lean_ctor_set_uint8(x_35, 7, x_29);
lean_ctor_set_uint8(x_35, 8, x_30);
lean_ctor_set_uint8(x_35, 9, x_34);
lean_ctor_set_uint8(x_35, 10, x_31);
lean_ctor_set_uint8(x_35, 11, x_32);
lean_ctor_set_uint8(x_35, 12, x_33);
lean_ctor_set(x_2, 0, x_35);
x_36 = l_Lean_Meta_getExpectedNumArgsAux___closed__1;
x_37 = 0;
x_38 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_36, x_37, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_45 = x_38;
} else {
 lean_dec_ref(x_38);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_ctor_get(x_2, 1);
x_49 = lean_ctor_get(x_2, 2);
x_50 = lean_ctor_get(x_2, 3);
x_51 = lean_ctor_get(x_2, 4);
x_52 = lean_ctor_get(x_2, 5);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_2);
x_55 = lean_ctor_get_uint8(x_47, 0);
x_56 = lean_ctor_get_uint8(x_47, 1);
x_57 = lean_ctor_get_uint8(x_47, 2);
x_58 = lean_ctor_get_uint8(x_47, 3);
x_59 = lean_ctor_get_uint8(x_47, 4);
x_60 = lean_ctor_get_uint8(x_47, 5);
x_61 = lean_ctor_get_uint8(x_47, 6);
x_62 = lean_ctor_get_uint8(x_47, 7);
x_63 = lean_ctor_get_uint8(x_47, 8);
x_64 = lean_ctor_get_uint8(x_47, 10);
x_65 = lean_ctor_get_uint8(x_47, 11);
x_66 = lean_ctor_get_uint8(x_47, 12);
if (lean_is_exclusive(x_47)) {
 x_67 = x_47;
} else {
 lean_dec_ref(x_47);
 x_67 = lean_box(0);
}
x_68 = 1;
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 0, 13);
} else {
 x_69 = x_67;
}
lean_ctor_set_uint8(x_69, 0, x_55);
lean_ctor_set_uint8(x_69, 1, x_56);
lean_ctor_set_uint8(x_69, 2, x_57);
lean_ctor_set_uint8(x_69, 3, x_58);
lean_ctor_set_uint8(x_69, 4, x_59);
lean_ctor_set_uint8(x_69, 5, x_60);
lean_ctor_set_uint8(x_69, 6, x_61);
lean_ctor_set_uint8(x_69, 7, x_62);
lean_ctor_set_uint8(x_69, 8, x_63);
lean_ctor_set_uint8(x_69, 9, x_68);
lean_ctor_set_uint8(x_69, 10, x_64);
lean_ctor_set_uint8(x_69, 11, x_65);
lean_ctor_set_uint8(x_69, 12, x_66);
x_70 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_48);
lean_ctor_set(x_70, 2, x_49);
lean_ctor_set(x_70, 3, x_50);
lean_ctor_set(x_70, 4, x_51);
lean_ctor_set(x_70, 5, x_52);
lean_ctor_set_uint8(x_70, sizeof(void*)*6, x_53);
lean_ctor_set_uint8(x_70, sizeof(void*)*6 + 1, x_54);
x_71 = l_Lean_Meta_getExpectedNumArgsAux___closed__1;
x_72 = 0;
x_73 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_71, x_72, x_70, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
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
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_80 = x_73;
} else {
 lean_dec_ref(x_73);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nwith", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_addPPExplicitToExposeDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_indentExpr(x_12);
x_15 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__2;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_15);
x_16 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__4;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_indentExpr(x_13);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_8, 0, x_20);
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = l_Lean_indentExpr(x_21);
x_24 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__2;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__4;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_indentExpr(x_22);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_8, 0, x_30);
return x_8;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
x_36 = l_Lean_indentExpr(x_33);
x_37 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__2;
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(7, 2, 0);
} else {
 x_38 = x_35;
 lean_ctor_set_tag(x_38, 7);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__4;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_indentExpr(x_34);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_32);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_8);
if (x_45 == 0)
{
return x_8;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_8, 0);
x_47 = lean_ctor_get(x_8, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_8);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("apply", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to unify", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_3);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1), 7, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1;
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_array_push(x_11, x_3);
x_13 = l_Lean_MessageData_ofLazyM(x_9, x_12);
x_14 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3;
x_20 = l_Lean_Meta_throwTacticEx___rarg(x_19, x_1, x_18, x_4, x_5, x_6, x_7, x_8);
return x_20;
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to assign synthesized instance", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_box(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_21 = l_Lean_Meta_isExprDefEq(x_1, x_20, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
if (x_2 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__4;
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_4, x_25, x_9, x_10, x_11, x_12, x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_21, 0);
lean_dec(x_32);
x_33 = lean_box(x_7);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_8, 0, x_35);
lean_ctor_set(x_21, 0, x_8);
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_dec(x_21);
x_37 = lean_box(x_7);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_8, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_8);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_21, 0);
lean_dec(x_42);
x_43 = lean_box(x_7);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_6);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_8, 0, x_45);
lean_ctor_set(x_21, 0, x_8);
return x_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = lean_box(x_7);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_6);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_8, 0, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_8);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_free_object(x_8);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_21);
if (x_51 == 0)
{
return x_21;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_21, 0);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_21);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_8, 0);
lean_inc(x_55);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_56 = l_Lean_Meta_isExprDefEq(x_1, x_55, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
if (x_2 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_6);
lean_dec(x_5);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__4;
x_61 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_4, x_60, x_9, x_10, x_11, x_12, x_59);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_67 = x_56;
} else {
 lean_dec_ref(x_56);
 x_67 = lean_box(0);
}
x_68 = lean_box(x_7);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_6);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_5);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_73 = lean_ctor_get(x_56, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_74 = x_56;
} else {
 lean_dec_ref(x_56);
 x_74 = lean_box(0);
}
x_75 = lean_box(x_7);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_6);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_5);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_74;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_80 = lean_ctor_get(x_56, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_56, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_82 = x_56;
} else {
 lean_dec_ref(x_56);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_box(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_15 = lean_array_uget(x_4, x_6);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
lean_dec(x_7);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_15);
x_29 = lean_infer_type(x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_51; lean_object* x_52; 
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
x_51 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_52 = l_Lean_Meta_synthInstance(x_30, x_51, x_8, x_9, x_10, x_11, x_31);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_32);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Array_isEmpty___rarg(x_27);
if (x_55 == 0)
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
lean_dec(x_28);
x_56 = 1;
x_57 = lean_box(0);
x_58 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__2(x_53, x_27, x_26, x_56, x_57, x_8, x_9, x_10, x_11, x_54);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
lean_dec(x_59);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_68 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1(x_15, x_3, x_1, x_2, x_63, x_64, x_67, x_66, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_16 = x_69;
x_17 = x_70;
goto block_24;
}
else
{
uint8_t x_71; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_68);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_75 = lean_box(0);
x_76 = lean_unbox(x_28);
lean_dec(x_28);
x_77 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__2(x_53, x_27, x_26, x_76, x_75, x_8, x_9, x_10, x_11, x_54);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_ctor_get(x_78, 0);
lean_inc(x_85);
lean_dec(x_78);
x_86 = lean_unbox(x_84);
lean_dec(x_84);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1(x_15, x_3, x_1, x_2, x_82, x_83, x_86, x_85, x_8, x_9, x_10, x_11, x_81);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_16 = x_88;
x_17 = x_89;
goto block_24;
}
else
{
uint8_t x_90; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 0);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_87);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_26);
x_94 = lean_ctor_get(x_52, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_52, 1);
lean_inc(x_95);
lean_dec(x_52);
x_33 = x_94;
x_34 = x_95;
goto block_50;
}
block_50:
{
uint8_t x_35; 
x_35 = l_Lean_Exception_isInterrupt(x_33);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Exception_isRuntime(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
lean_dec(x_32);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_33);
lean_inc(x_15);
x_38 = lean_array_push(x_27, x_15);
x_39 = lean_box(0);
x_40 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_41 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1(x_15, x_3, x_1, x_2, x_37, x_38, x_40, x_39, x_8, x_9, x_10, x_11, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_16 = x_42;
x_17 = x_43;
goto block_24;
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_32)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_32;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_34);
return x_48;
}
}
else
{
lean_object* x_49; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_32)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_32;
 lean_ctor_set_tag(x_49, 1);
}
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_34);
return x_49;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_29);
if (x_96 == 0)
{
return x_29;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_29, 0);
x_98 = lean_ctor_get(x_29, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_29);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
block_24:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = 1;
x_22 = lean_usize_add(x_6, x_21);
x_6 = x_22;
x_7 = x_20;
x_12 = x_17;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_synthAppInstances_step___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_synthAppInstances_step___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_synthAppInstances_step___closed__1;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_synthAppInstances_step___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_synthAppInstances_step___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances_step(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_Lean_Meta_synthAppInstances_step___closed__3;
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1(x_1, x_2, x_3, x_4, x_11, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_16);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = l_Lean_Meta_synthAppInstances_step___closed__1;
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Lean_Meta_synthAppInstances_step___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_dec(x_16);
if (x_3 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_14, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_17);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_14, 0);
lean_dec(x_33);
x_34 = l_Lean_Meta_synthAppInstances_step___closed__1;
lean_ctor_set(x_14, 0, x_34);
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_dec(x_14);
x_36 = l_Lean_Meta_synthAppInstances_step___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_17);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_14, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_40);
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_dec(x_14);
x_42 = lean_ctor_get(x_16, 0);
lean_inc(x_42);
lean_dec(x_16);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
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
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_7);
lean_dec(x_7);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1(x_1, x_14, x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1(x_1, x_2, x_13, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances_step___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_synthAppInstances_step(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances___spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_23; 
x_13 = lean_array_uget(x_2, x_4);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_5);
x_14 = x_30;
x_15 = x_10;
goto block_22;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_32 = lean_ctor_get(x_24, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_24, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = lean_array_fget(x_26, x_27);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_27, x_37);
lean_dec(x_27);
lean_ctor_set(x_24, 1, x_38);
x_39 = l_Lean_BinderInfo_isInstImplicit(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_13);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_5);
x_14 = x_40;
x_15 = x_10;
goto block_22;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Expr_mvarId_x21(x_13);
x_42 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_41, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_41);
if (x_1 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_array_push(x_25, x_13);
lean_ctor_set(x_5, 1, x_46);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_5);
x_14 = x_47;
x_15 = x_45;
goto block_22;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_13);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_5);
x_14 = x_49;
x_15 = x_48;
goto block_22;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_dec(x_42);
x_51 = lean_array_push(x_25, x_13);
lean_ctor_set(x_5, 1, x_51);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_5);
x_14 = x_52;
x_15 = x_50;
goto block_22;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_24);
x_53 = lean_array_fget(x_26, x_27);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_27, x_55);
lean_dec(x_27);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_26);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_28);
x_58 = l_Lean_BinderInfo_isInstImplicit(x_54);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_13);
lean_ctor_set(x_5, 0, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_5);
x_14 = x_59;
x_15 = x_10;
goto block_22;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Expr_mvarId_x21(x_13);
x_61 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_60, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_60);
if (x_1 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_array_push(x_25, x_13);
lean_ctor_set(x_5, 1, x_65);
lean_ctor_set(x_5, 0, x_57);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_5);
x_14 = x_66;
x_15 = x_64;
goto block_22;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_13);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
lean_ctor_set(x_5, 0, x_57);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_5);
x_14 = x_68;
x_15 = x_67;
goto block_22;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
lean_dec(x_61);
x_70 = lean_array_push(x_25, x_13);
lean_ctor_set(x_5, 1, x_70);
lean_ctor_set(x_5, 0, x_57);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_5);
x_14 = x_71;
x_15 = x_69;
goto block_22;
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_72 = lean_ctor_get(x_5, 0);
x_73 = lean_ctor_get(x_5, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_5);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 2);
lean_inc(x_76);
x_77 = lean_nat_dec_lt(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_13);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_73);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_14 = x_79;
x_15 = x_10;
goto block_22;
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
x_81 = lean_array_fget(x_74, x_75);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_add(x_75, x_83);
lean_dec(x_75);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 3, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_74);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_76);
x_86 = l_Lean_BinderInfo_isInstImplicit(x_82);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_13);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_73);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_14 = x_88;
x_15 = x_10;
goto block_22;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_Expr_mvarId_x21(x_13);
x_90 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_89, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_89);
if (x_1 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_array_push(x_73, x_13);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_14 = x_96;
x_15 = x_93;
goto block_22;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_13);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
lean_dec(x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_85);
lean_ctor_set(x_98, 1, x_73);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_14 = x_99;
x_15 = x_97;
goto block_22;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_90, 1);
lean_inc(x_100);
lean_dec(x_90);
x_101 = lean_array_push(x_73, x_13);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_85);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_14 = x_103;
x_15 = x_100;
goto block_22;
}
}
}
}
block_22:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_4 = x_20;
x_5 = x_18;
x_10 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_synthAppInstances___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Meta_synthAppInstances_step(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_4 = x_12;
x_9 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_toSubarray___rarg(x_4, x_13, x_12);
x_15 = l_Lean_Meta_synthAppInstances_step___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_array_get_size(x_3);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances___spec__1(x_5, x_3, x_18, x_19, x_16, x_7, x_8, x_9, x_10, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Loop_forIn_loop___at_Lean_Meta_synthAppInstances___spec__2(x_1, x_2, x_6, x_23, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
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
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances___spec__1(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_synthAppInstances___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Loop_forIn_loop___at_Lean_Meta_synthAppInstances___spec__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Meta_synthAppInstances(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
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
x_63 = l_outOfBounds___rarg(x_62);
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
lean_dec(x_18);
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
x_28 = l_outOfBounds___rarg(x_27);
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
lean_dec(x_13);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_11);
x_18 = lean_box(0);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_free_object(x_9);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_13);
lean_dec(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_instInhabitedExpr;
x_22 = l_outOfBounds___rarg(x_21);
x_23 = l_Lean_Expr_mvarId_x21(x_22);
lean_dec(x_22);
x_24 = l_Lean_MVarId_setTag(x_23, x_11, x_4, x_5, x_6, x_7, x_12);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_array_fget(x_2, x_19);
x_26 = l_Lean_Expr_mvarId_x21(x_25);
lean_dec(x_25);
x_27 = l_Lean_MVarId_setTag(x_26, x_11, x_4, x_5, x_6, x_7, x_12);
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
lean_dec(x_30);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
lean_dec(x_28);
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
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_30);
lean_dec(x_30);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = l_Lean_instInhabitedExpr;
x_40 = l_outOfBounds___rarg(x_39);
x_41 = l_Lean_Expr_mvarId_x21(x_40);
lean_dec(x_40);
x_42 = l_Lean_MVarId_setTag(x_41, x_28, x_4, x_5, x_6, x_7, x_29);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_array_fget(x_2, x_37);
x_44 = l_Lean_Expr_mvarId_x21(x_43);
lean_dec(x_43);
x_45 = l_Lean_MVarId_setTag(x_44, x_28, x_4, x_5, x_6, x_7, x_29);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_appendParentTag(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_2);
x_12 = l_Lean_Meta_synthAppInstances(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_appendParentTag(x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Meta_postprocessAppMVars(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
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
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(x_1, x_2, x_14, x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
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
x_1 = l_Lean_Meta_synthAppInstances_step___closed__1;
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
x_10 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
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
x_13 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
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
x_17 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
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
LEAN_EXPORT lean_object* l_List_map___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Expr_mvarId_x21(x_4);
lean_dec(x_4);
x_7 = l_List_map___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_Expr_mvarId_x21(x_8);
lean_dec(x_8);
x_11 = l_List_map___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_array_to_list(lean_box(0), x_1);
x_43 = l_List_map___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___spec__1(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
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
x_9 = lean_ctor_get_uint8(x_1, 3);
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
uint8_t x_14; lean_object* x_15; 
x_14 = 1;
lean_ctor_set_uint8(x_12, 0, x_14);
lean_ctor_set_uint8(x_12, 1, x_14);
lean_ctor_set_uint8(x_12, 2, x_14);
x_15 = l_Lean_Meta_isExprDefEqGuarded(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
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
uint8_t x_20; 
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
else
{
uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get_uint8(x_12, 3);
x_25 = lean_ctor_get_uint8(x_12, 4);
x_26 = lean_ctor_get_uint8(x_12, 5);
x_27 = lean_ctor_get_uint8(x_12, 6);
x_28 = lean_ctor_get_uint8(x_12, 7);
x_29 = lean_ctor_get_uint8(x_12, 8);
x_30 = lean_ctor_get_uint8(x_12, 9);
x_31 = lean_ctor_get_uint8(x_12, 10);
x_32 = lean_ctor_get_uint8(x_12, 11);
x_33 = lean_ctor_get_uint8(x_12, 12);
lean_dec(x_12);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, 1, x_34);
lean_ctor_set_uint8(x_35, 2, x_34);
lean_ctor_set_uint8(x_35, 3, x_24);
lean_ctor_set_uint8(x_35, 4, x_25);
lean_ctor_set_uint8(x_35, 5, x_26);
lean_ctor_set_uint8(x_35, 6, x_27);
lean_ctor_set_uint8(x_35, 7, x_28);
lean_ctor_set_uint8(x_35, 8, x_29);
lean_ctor_set_uint8(x_35, 9, x_30);
lean_ctor_set_uint8(x_35, 10, x_31);
lean_ctor_set_uint8(x_35, 11, x_32);
lean_ctor_set_uint8(x_35, 12, x_33);
lean_ctor_set(x_4, 0, x_35);
x_36 = l_Lean_Meta_isExprDefEqGuarded(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_45 = lean_ctor_get(x_4, 0);
x_46 = lean_ctor_get(x_4, 1);
x_47 = lean_ctor_get(x_4, 2);
x_48 = lean_ctor_get(x_4, 3);
x_49 = lean_ctor_get(x_4, 4);
x_50 = lean_ctor_get(x_4, 5);
x_51 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_52 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_4);
x_53 = lean_ctor_get_uint8(x_45, 3);
x_54 = lean_ctor_get_uint8(x_45, 4);
x_55 = lean_ctor_get_uint8(x_45, 5);
x_56 = lean_ctor_get_uint8(x_45, 6);
x_57 = lean_ctor_get_uint8(x_45, 7);
x_58 = lean_ctor_get_uint8(x_45, 8);
x_59 = lean_ctor_get_uint8(x_45, 9);
x_60 = lean_ctor_get_uint8(x_45, 10);
x_61 = lean_ctor_get_uint8(x_45, 11);
x_62 = lean_ctor_get_uint8(x_45, 12);
if (lean_is_exclusive(x_45)) {
 x_63 = x_45;
} else {
 lean_dec_ref(x_45);
 x_63 = lean_box(0);
}
x_64 = 1;
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 0, 13);
} else {
 x_65 = x_63;
}
lean_ctor_set_uint8(x_65, 0, x_64);
lean_ctor_set_uint8(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, 2, x_64);
lean_ctor_set_uint8(x_65, 3, x_53);
lean_ctor_set_uint8(x_65, 4, x_54);
lean_ctor_set_uint8(x_65, 5, x_55);
lean_ctor_set_uint8(x_65, 6, x_56);
lean_ctor_set_uint8(x_65, 7, x_57);
lean_ctor_set_uint8(x_65, 8, x_58);
lean_ctor_set_uint8(x_65, 9, x_59);
lean_ctor_set_uint8(x_65, 10, x_60);
lean_ctor_set_uint8(x_65, 11, x_61);
lean_ctor_set_uint8(x_65, 12, x_62);
x_66 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_46);
lean_ctor_set(x_66, 2, x_47);
lean_ctor_set(x_66, 3, x_48);
lean_ctor_set(x_66, 4, x_49);
lean_ctor_set(x_66, 5, x_50);
lean_ctor_set_uint8(x_66, sizeof(void*)*6, x_51);
lean_ctor_set_uint8(x_66, sizeof(void*)*6 + 1, x_52);
x_67 = l_Lean_Meta_isExprDefEqGuarded(x_2, x_3, x_66, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_42 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(x_2, x_41, x_3, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
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
uint8_t x_55; 
lean_free_object(x_36);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
return x_42;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_42);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_36, 0);
x_60 = lean_ctor_get(x_36, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_36);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_61 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(x_2, x_60, x_3, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_59);
lean_dec(x_38);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l_Lean_Meta_SavedState_restore(x_29, x_7, x_8, x_9, x_10, x_64);
lean_dec(x_29);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_6, x_67);
lean_dec(x_6);
x_6 = x_68;
x_11 = x_66;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_71 = x_61;
} else {
 lean_dec_ref(x_61);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_38);
lean_ctor_set(x_72, 1, x_59);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_59);
lean_dec(x_38);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_76 = x_61;
} else {
 lean_dec_ref(x_61);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
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
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_apply___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_List_elem___at_Lean_MVarId_getMVarDependencies_addMVars___spec__3(x_7, x_1);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_Expr_mvarId_x21(x_11);
x_13 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
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
x_1 = l_Lean_Meta_synthAppInstances_step___closed__1;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
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
x_20 = lean_ctor_get_uint8(x_2, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_21 = l_Lean_Meta_postprocessAppMVars(x_5, x_1, x_17, x_18, x_19, x_20, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_6, x_8, x_9, x_10, x_11, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
x_26 = l_Lean_mkAppN(x_24, x_17);
x_27 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_26, x_8, x_9, x_10, x_11, x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_array_get_size(x_17);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_86; 
lean_dec(x_29);
lean_dec(x_17);
x_86 = l_Lean_Meta_synthAppInstances_step___closed__1;
x_32 = x_86;
x_33 = x_28;
goto block_85;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_29, x_29);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_29);
lean_dec(x_17);
x_88 = l_Lean_Meta_synthAppInstances_step___closed__1;
x_32 = x_88;
x_33 = x_28;
goto block_85;
}
else
{
size_t x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = 0;
x_90 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_91 = l_Lean_Meta_synthAppInstances_step___closed__1;
x_92 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__3(x_17, x_89, x_90, x_91, x_8, x_9, x_10, x_11, x_28);
lean_dec(x_17);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_32 = x_93;
x_33 = x_94;
goto block_85;
}
}
block_85:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_34 = l_Lean_Meta_getMVarsNoDelayed(x_24, x_8, x_9, x_10, x_11, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get_uint8(x_2, 0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_38 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(x_32, x_37, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_array_get_size(x_35);
x_42 = lean_nat_dec_lt(x_30, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_35);
x_43 = l_Lean_MVarId_apply___lambda__1___closed__1;
x_44 = l_List_appendTR___rarg(x_39, x_43);
lean_inc(x_44);
x_45 = l_List_forM___at_Lean_MVarId_apply___spec__1(x_44, x_8, x_9, x_10, x_11, x_40);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_44);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
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
x_54 = lean_nat_dec_le(x_41, x_41);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_41);
lean_dec(x_35);
x_55 = l_Lean_MVarId_apply___lambda__1___closed__1;
x_56 = l_List_appendTR___rarg(x_39, x_55);
lean_inc(x_56);
x_57 = l_List_forM___at_Lean_MVarId_apply___spec__1(x_56, x_8, x_9, x_10, x_11, x_40);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_56);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_68 = l_Lean_Meta_synthAppInstances_step___closed__1;
x_69 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__2(x_39, x_35, x_66, x_67, x_68);
lean_dec(x_35);
x_70 = lean_array_to_list(lean_box(0), x_69);
x_71 = l_List_appendTR___rarg(x_39, x_70);
lean_inc(x_71);
x_72 = l_List_forM___at_Lean_MVarId_apply___spec__1(x_71, x_8, x_9, x_10, x_11, x_40);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_71);
x_77 = !lean_is_exclusive(x_72);
if (x_77 == 0)
{
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_72, 0);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_72);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_81 = !lean_is_exclusive(x_38);
if (x_81 == 0)
{
return x_38;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_38, 0);
x_83 = lean_ctor_get(x_38, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_38);
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
uint8_t x_95; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_21);
if (x_95 == 0)
{
return x_21;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_21, 0);
x_97 = lean_ctor_get(x_21, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_21);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_14);
if (x_99 == 0)
{
return x_14;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_14, 0);
x_101 = lean_ctor_get(x_14, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_14);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
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
x_9 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lambda__2___boxed), 9, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_MVarId_apply___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forM___at_Lean_MVarId_apply___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_apply___spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_apply___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_MVarId_apply(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
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
lean_dec(x_1);
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
static lean_object* _init_l_Lean_MVarId_splitAndCore_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_splitAndCore_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_splitAndCore_go___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_splitAndCore_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_splitAndCore_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_splitAndCore_go___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_splitAndCore_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_splitAndCore_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_splitAndCore_go___closed__1;
x_2 = l_Lean_MVarId_splitAndCore_go___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_splitAndCore_go___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_splitAndCore_go___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = l_Lean_MVarId_splitAndCore_go___closed__2;
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Expr_isAppOfArity(x_10, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_15 = lean_st_ref_get(x_3, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_16);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_18);
x_21 = l_Lean_MVarId_splitAndCore_go___closed__4;
x_22 = lean_name_append_index_after(x_21, x_20);
x_23 = l_Lean_Name_append(x_1, x_22);
x_24 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_10, x_23, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_take(x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_mvarId_x21(x_25);
x_31 = lean_array_push(x_28, x_30);
x_32 = lean_st_ref_set(x_3, x_31, x_29);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_25);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = l_Lean_Expr_appFn_x21(x_10);
x_38 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_39 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_38);
lean_inc(x_1);
x_40 = l_Lean_MVarId_splitAndCore_go(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_39);
x_43 = l_Lean_MVarId_splitAndCore_go(x_1, x_39, x_3, x_4, x_5, x_6, x_7, x_42);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = l_Lean_MVarId_splitAndCore_go___closed__7;
x_47 = l_Lean_mkApp4(x_46, x_38, x_39, x_41, x_45);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = l_Lean_MVarId_splitAndCore_go___closed__7;
x_51 = l_Lean_mkApp4(x_50, x_38, x_39, x_41, x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_38);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
return x_43;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_43, 0);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_43);
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
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
else
{
uint8_t x_61; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_9);
if (x_61 == 0)
{
return x_9;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_9, 0);
x_63 = lean_ctor_get(x_9, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_9);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_splitAndCore_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
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
x_14 = l_Lean_MVarId_splitAndCore_go___closed__2;
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_synthAppInstances_step___closed__1;
x_23 = lean_st_mk_ref(x_22, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_MVarId_splitAndCore_go(x_20, x_12, x_24, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_24, x_28);
lean_dec(x_24);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_27, x_3, x_4, x_5, x_6, x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_array_to_list(lean_box(0), x_30);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_array_to_list(lean_box(0), x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_10, 0);
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_10);
x_49 = l_Lean_MVarId_splitAndCore_go___closed__2;
x_50 = lean_unsigned_to_nat(2u);
x_51 = l_Lean_Expr_isAppOfArity(x_47, x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
else
{
lean_object* x_55; 
lean_inc(x_1);
x_55 = l_Lean_MVarId_getTag(x_1, x_3, x_4, x_5, x_6, x_48);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Meta_synthAppInstances_step___closed__1;
x_59 = lean_st_mk_ref(x_58, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_62 = l_Lean_MVarId_splitAndCore_go(x_56, x_47, x_60, x_3, x_4, x_5, x_6, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_st_ref_get(x_60, x_64);
lean_dec(x_60);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_63, x_3, x_4, x_5, x_6, x_67);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_71 = lean_array_to_list(lean_box(0), x_66);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_73 = lean_ctor_get(x_62, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_75 = x_62;
} else {
 lean_dec_ref(x_62);
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
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_77 = lean_ctor_get(x_55, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_55, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_79 = x_55;
} else {
 lean_dec_ref(x_55);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_10);
if (x_81 == 0)
{
return x_10;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_10, 0);
x_83 = lean_ctor_get(x_10, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_10);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_8);
if (x_85 == 0)
{
return x_8;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_8, 0);
x_87 = lean_ctor_get(x_8, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_8);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_splitAndCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("splitAnd", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_splitAndCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_splitAndCore___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_MVarId_splitAndCore___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lambda__1), 7, 2);
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
x_7 = l_Lean_MVarId_splitAndCore(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_splitAndCore(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
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
x_1 = lean_mk_string_unchecked("elim", 4, 4);
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
x_13 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_11, x_3, x_4, x_5, x_6, x_12);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l_Lean_MVarId_exfalso___lambda__1___closed__3;
lean_inc(x_3);
x_24 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_23, x_20, x_3, x_4, x_5, x_6, x_21);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 0, x_17);
x_28 = l_Lean_MVarId_exfalso___lambda__1___closed__5;
x_29 = l_Lean_Expr_const___override(x_28, x_24);
lean_inc(x_26);
x_30 = l_Lean_mkAppB(x_29, x_14, x_26);
x_31 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_30, x_3, x_4, x_5, x_6, x_27);
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
x_34 = l_Lean_Expr_mvarId_x21(x_26);
lean_dec(x_26);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lean_Expr_mvarId_x21(x_26);
lean_dec(x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_22);
x_41 = l_Lean_MVarId_exfalso___lambda__1___closed__5;
x_42 = l_Lean_Expr_const___override(x_41, x_40);
lean_inc(x_38);
x_43 = l_Lean_mkAppB(x_42, x_14, x_38);
x_44 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_43, x_3, x_4, x_5, x_6, x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_47 = l_Lean_Expr_mvarId_x21(x_38);
lean_dec(x_38);
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
uint8_t x_49; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_19);
if (x_49 == 0)
{
return x_19;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
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
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_16);
if (x_53 == 0)
{
return x_16;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_16, 0);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_16);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_10);
if (x_57 == 0)
{
return x_10;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_10, 0);
x_59 = lean_ctor_get(x_10, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_10);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_8);
if (x_61 == 0)
{
return x_8;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_8, 0);
x_63 = lean_ctor_get(x_8, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_8);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exfalso", 7, 7);
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
static lean_object* _init_l_Lean_MVarId_nthConstructor___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("index ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" out of bounds, only ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" constructors", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lambda__1___closed__4() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, 2, x_3);
lean_ctor_set_uint8(x_4, 3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 4);
x_13 = l_List_length___rarg(x_12);
x_14 = lean_nat_dec_lt(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_16 = l_Lean_MVarId_nthConstructor___lambda__1___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_MVarId_nthConstructor___lambda__1___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_13);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = l_Lean_MVarId_nthConstructor___lambda__1___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_4, x_26, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
lean_dec(x_3);
x_28 = l_List_get___rarg(x_12, x_2);
x_29 = l_Lean_Expr_const___override(x_28, x_5);
x_30 = l_Lean_MVarId_nthConstructor___lambda__1___closed__4;
x_31 = l_Lean_MVarId_apply(x_4, x_29, x_30, x_7, x_8, x_9, x_10, x_11);
return x_31;
}
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("target is not an inductive datatype", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_nthConstructor___lambda__2___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_nthConstructor___lambda__2___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_nthConstructor___lambda__2___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" tactic works for inductive types with exactly ", 47, 47);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_12 = l_Lean_MVarId_getType_x27(x_1, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_getAppFn(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_8, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_environment_find(x_21, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
x_23 = l_Lean_MVarId_nthConstructor___lambda__2___closed__4;
x_24 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_23, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 5)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = l_Lean_MVarId_nthConstructor___lambda__1(x_26, x_3, x_2, x_1, x_17, x_27, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_26);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_31, 4);
lean_inc(x_33);
x_34 = l_List_length___rarg(x_33);
lean_dec(x_33);
x_35 = lean_nat_dec_eq(x_34, x_32);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_3);
x_36 = 1;
lean_inc(x_2);
x_37 = l_Lean_Name_toString(x_2, x_36);
x_38 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lean_MVarId_nthConstructor___lambda__2___closed__5;
x_41 = lean_string_append(x_39, x_40);
x_42 = l___private_Init_Data_Repr_0__Nat_reprFast(x_32);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = l_Lean_MVarId_nthConstructor___lambda__1___closed__3;
x_45 = lean_string_append(x_43, x_44);
lean_ctor_set_tag(x_25, 3);
lean_ctor_set(x_25, 0, x_45);
x_46 = l_Lean_MessageData_ofFormat(x_25);
lean_ctor_set(x_4, 0, x_46);
x_47 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_4, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_4);
lean_dec(x_32);
lean_free_object(x_25);
x_52 = lean_box(0);
x_53 = l_Lean_MVarId_nthConstructor___lambda__1(x_31, x_3, x_2, x_1, x_17, x_52, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_31);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_25, 0);
x_55 = lean_ctor_get(x_4, 0);
lean_inc(x_55);
lean_dec(x_4);
x_56 = lean_ctor_get(x_54, 4);
lean_inc(x_56);
x_57 = l_List_length___rarg(x_56);
lean_dec(x_56);
x_58 = lean_nat_dec_eq(x_57, x_55);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_54);
lean_dec(x_17);
lean_dec(x_3);
x_59 = 1;
lean_inc(x_2);
x_60 = l_Lean_Name_toString(x_2, x_59);
x_61 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__1;
x_62 = lean_string_append(x_61, x_60);
lean_dec(x_60);
x_63 = l_Lean_MVarId_nthConstructor___lambda__2___closed__5;
x_64 = lean_string_append(x_62, x_63);
x_65 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_66 = lean_string_append(x_64, x_65);
lean_dec(x_65);
x_67 = l_Lean_MVarId_nthConstructor___lambda__1___closed__3;
x_68 = lean_string_append(x_66, x_67);
lean_ctor_set_tag(x_25, 3);
lean_ctor_set(x_25, 0, x_68);
x_69 = l_Lean_MessageData_ofFormat(x_25);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_70, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_55);
lean_free_object(x_25);
x_76 = lean_box(0);
x_77 = l_Lean_MVarId_nthConstructor___lambda__1(x_54, x_3, x_2, x_1, x_17, x_76, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_54);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_78 = lean_ctor_get(x_25, 0);
lean_inc(x_78);
lean_dec(x_25);
x_79 = lean_ctor_get(x_4, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_80 = x_4;
} else {
 lean_dec_ref(x_4);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_78, 4);
lean_inc(x_81);
x_82 = l_List_length___rarg(x_81);
lean_dec(x_81);
x_83 = lean_nat_dec_eq(x_82, x_79);
lean_dec(x_82);
if (x_83 == 0)
{
uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_78);
lean_dec(x_17);
lean_dec(x_3);
x_84 = 1;
lean_inc(x_2);
x_85 = l_Lean_Name_toString(x_2, x_84);
x_86 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__1;
x_87 = lean_string_append(x_86, x_85);
lean_dec(x_85);
x_88 = l_Lean_MVarId_nthConstructor___lambda__2___closed__5;
x_89 = lean_string_append(x_87, x_88);
x_90 = l___private_Init_Data_Repr_0__Nat_reprFast(x_79);
x_91 = lean_string_append(x_89, x_90);
lean_dec(x_90);
x_92 = l_Lean_MVarId_nthConstructor___lambda__1___closed__3;
x_93 = lean_string_append(x_91, x_92);
x_94 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = l_Lean_MessageData_ofFormat(x_94);
if (lean_is_scalar(x_80)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_80;
}
lean_ctor_set(x_96, 0, x_95);
x_97 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_96, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
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
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_80);
lean_dec(x_79);
x_102 = lean_box(0);
x_103 = l_Lean_MVarId_nthConstructor___lambda__1(x_78, x_3, x_2, x_1, x_17, x_102, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_78);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
x_104 = l_Lean_MVarId_nthConstructor___lambda__2___closed__4;
x_105 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_104, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
x_106 = l_Lean_MVarId_nthConstructor___lambda__2___closed__4;
x_107 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_106, x_5, x_6, x_7, x_8, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_12);
if (x_108 == 0)
{
return x_12;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_12, 0);
x_110 = lean_ctor_get(x_12, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_12);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_10);
if (x_112 == 0)
{
return x_10;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_10, 0);
x_114 = lean_ctor_get(x_10, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_10);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lambda__2), 9, 4);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_4, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_nthConstructor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_MVarId_iffOfEq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
x_21 = l_Lean_Exception_isInterrupt(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_free_object(x_10);
lean_dec(x_19);
x_23 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
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
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = l_Lean_Exception_isInterrupt(x_30);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Exception_isRuntime(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_30);
x_34 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_31);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
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
else
{
lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_31);
return x_40;
}
}
}
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_iffOfEq___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_MVarId_apply(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_13 = l_Lean_throwError___at_Lean_Meta_exactlyOne___spec__1(x_12, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_10);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_23 = l_Lean_throwError___at_Lean_Meta_exactlyOne___spec__1(x_22, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("iff_of_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_iffOfEq___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_iffOfEq___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_MVarId_iffOfEq___closed__3;
x_8 = l_Lean_MVarId_nthConstructor___lambda__1___closed__4;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_observing_x3f___at_Lean_MVarId_iffOfEq___spec__1(x_9, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
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
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_propext___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_propext___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("propext", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_propext___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_propext___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_16 = 2;
lean_ctor_set_uint8(x_7, 9, x_16);
x_17 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_10);
lean_ctor_set(x_17, 4, x_11);
lean_ctor_set(x_17, 5, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*6, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*6 + 1, x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l_Lean_MVarId_getType_x27(x_1, x_17, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_MVarId_propext___lambda__1___closed__2;
x_22 = lean_unsigned_to_nat(3u);
x_23 = l_Lean_Expr_isAppOfArity(x_19, x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_1);
x_24 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_25 = l_Lean_throwError___at_Lean_Meta_exactlyOne___spec__1(x_24, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Lean_Expr_appFn_x21(x_19);
lean_dec(x_19);
x_27 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_Lean_Meta_isProp(x_27, x_2, x_3, x_4, x_5, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_54; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_54 = lean_unbox(x_29);
lean_dec(x_29);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_1);
x_55 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_56 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_55, x_2, x_3, x_4, x_5, x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
x_31 = x_30;
goto block_53;
}
block_53:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Lean_MVarId_propext___lambda__1___closed__5;
x_33 = l_Lean_MVarId_nthConstructor___lambda__1___closed__4;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_MVarId_apply(x_1, x_32, x_33, x_2, x_3, x_4, x_5, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_38 = l_Lean_throwError___at_Lean_Meta_exactlyOne___spec__1(x_37, x_2, x_3, x_4, x_5, x_36);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_34, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
lean_dec(x_35);
lean_ctor_set(x_34, 0, x_42);
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_39);
lean_dec(x_35);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_dec(x_34);
x_47 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_48 = l_Lean_throwError___at_Lean_Meta_exactlyOne___spec__1(x_47, x_2, x_3, x_4, x_5, x_46);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_34);
if (x_49 == 0)
{
return x_34;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_34, 0);
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_34);
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
uint8_t x_61; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_28);
if (x_61 == 0)
{
return x_28;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_28, 0);
x_63 = lean_ctor_get(x_28, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_28);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_18);
if (x_65 == 0)
{
return x_18;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_18, 0);
x_67 = lean_ctor_get(x_18, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_18);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_69 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_70 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_71 = lean_ctor_get_uint8(x_7, 0);
x_72 = lean_ctor_get_uint8(x_7, 1);
x_73 = lean_ctor_get_uint8(x_7, 2);
x_74 = lean_ctor_get_uint8(x_7, 3);
x_75 = lean_ctor_get_uint8(x_7, 4);
x_76 = lean_ctor_get_uint8(x_7, 5);
x_77 = lean_ctor_get_uint8(x_7, 6);
x_78 = lean_ctor_get_uint8(x_7, 7);
x_79 = lean_ctor_get_uint8(x_7, 8);
x_80 = lean_ctor_get_uint8(x_7, 10);
x_81 = lean_ctor_get_uint8(x_7, 11);
x_82 = lean_ctor_get_uint8(x_7, 12);
lean_dec(x_7);
x_83 = 2;
x_84 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_84, 0, x_71);
lean_ctor_set_uint8(x_84, 1, x_72);
lean_ctor_set_uint8(x_84, 2, x_73);
lean_ctor_set_uint8(x_84, 3, x_74);
lean_ctor_set_uint8(x_84, 4, x_75);
lean_ctor_set_uint8(x_84, 5, x_76);
lean_ctor_set_uint8(x_84, 6, x_77);
lean_ctor_set_uint8(x_84, 7, x_78);
lean_ctor_set_uint8(x_84, 8, x_79);
lean_ctor_set_uint8(x_84, 9, x_83);
lean_ctor_set_uint8(x_84, 10, x_80);
lean_ctor_set_uint8(x_84, 11, x_81);
lean_ctor_set_uint8(x_84, 12, x_82);
x_85 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_8);
lean_ctor_set(x_85, 2, x_9);
lean_ctor_set(x_85, 3, x_10);
lean_ctor_set(x_85, 4, x_11);
lean_ctor_set(x_85, 5, x_12);
lean_ctor_set_uint8(x_85, sizeof(void*)*6, x_69);
lean_ctor_set_uint8(x_85, sizeof(void*)*6 + 1, x_70);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_86 = l_Lean_MVarId_getType_x27(x_1, x_85, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_MVarId_propext___lambda__1___closed__2;
x_90 = lean_unsigned_to_nat(3u);
x_91 = l_Lean_Expr_isAppOfArity(x_87, x_89, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_87);
lean_dec(x_1);
x_92 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_93 = l_Lean_throwError___at_Lean_Meta_exactlyOne___spec__1(x_92, x_2, x_3, x_4, x_5, x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = l_Lean_Expr_appFn_x21(x_87);
lean_dec(x_87);
x_95 = l_Lean_Expr_appArg_x21(x_94);
lean_dec(x_94);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_96 = l_Lean_Meta_isProp(x_95, x_2, x_3, x_4, x_5, x_88);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_120; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_120 = lean_unbox(x_97);
lean_dec(x_97);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_1);
x_121 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_122 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_121, x_2, x_3, x_4, x_5, x_98);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
else
{
x_99 = x_98;
goto block_119;
}
block_119:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = l_Lean_MVarId_propext___lambda__1___closed__5;
x_101 = l_Lean_MVarId_nthConstructor___lambda__1___closed__4;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_102 = l_Lean_MVarId_apply(x_1, x_100, x_101, x_2, x_3, x_4, x_5, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_106 = l_Lean_throwError___at_Lean_Meta_exactlyOne___spec__1(x_105, x_2, x_3, x_4, x_5, x_104);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_106;
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_109 = x_102;
} else {
 lean_dec_ref(x_102);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
lean_dec(x_103);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_107);
lean_dec(x_103);
x_112 = lean_ctor_get(x_102, 1);
lean_inc(x_112);
lean_dec(x_102);
x_113 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_114 = l_Lean_throwError___at_Lean_Meta_exactlyOne___spec__1(x_113, x_2, x_3, x_4, x_5, x_112);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_115 = lean_ctor_get(x_102, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_102, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_117 = x_102;
} else {
 lean_dec_ref(x_102);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_ctor_get(x_96, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_96, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_129 = x_96;
} else {
 lean_dec_ref(x_96);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_ctor_get(x_86, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_86, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_133 = x_86;
} else {
 lean_dec_ref(x_86);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lambda__1), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_observing_x3f___at_Lean_MVarId_iffOfEq___spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_proofIrrelHeq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
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
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_MVarId_proofIrrelHeq___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
x_21 = l_Lean_Exception_isInterrupt(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_free_object(x_10);
lean_dec(x_19);
x_23 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
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
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = l_Lean_Exception_isInterrupt(x_30);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Exception_isRuntime(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_30);
x_34 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_31);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
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
else
{
lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_31);
return x_40;
}
}
}
}
}
static lean_object* _init_l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proof_irrel_heq", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 5);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_19 = 2;
lean_ctor_set_uint8(x_9, 9, x_19);
x_20 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_11);
lean_ctor_set(x_20, 2, x_12);
lean_ctor_set(x_20, 3, x_13);
lean_ctor_set(x_20, 4, x_14);
lean_ctor_set(x_20, 5, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*6, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*6 + 1, x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_21 = l_Lean_MVarId_getType_x27(x_1, x_20, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__2;
x_25 = lean_unsigned_to_nat(4u);
x_26 = l_Lean_Expr_isAppOfArity(x_22, x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_1);
x_27 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_28 = l_Lean_throwError___at_Lean_MVarId_proofIrrelHeq___spec__1(x_27, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = l_Lean_Expr_appFn_x21(x_22);
x_30 = l_Lean_Expr_appFn_x21(x_29);
lean_dec(x_29);
x_31 = l_Lean_Expr_appArg_x21(x_30);
lean_dec(x_30);
x_32 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_33 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1;
x_34 = lean_array_push(x_33, x_31);
x_35 = lean_array_push(x_34, x_32);
x_36 = l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__4;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_37 = l_Lean_Meta_mkAppM(x_36, x_35, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_38, x_3, x_4, x_5, x_6, x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = 1;
x_44 = lean_box(x_43);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = 1;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_37);
if (x_49 == 0)
{
return x_37;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_37, 0);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_37);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_21);
if (x_53 == 0)
{
return x_21;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_21, 0);
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_21);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_57 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_58 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_59 = lean_ctor_get_uint8(x_9, 0);
x_60 = lean_ctor_get_uint8(x_9, 1);
x_61 = lean_ctor_get_uint8(x_9, 2);
x_62 = lean_ctor_get_uint8(x_9, 3);
x_63 = lean_ctor_get_uint8(x_9, 4);
x_64 = lean_ctor_get_uint8(x_9, 5);
x_65 = lean_ctor_get_uint8(x_9, 6);
x_66 = lean_ctor_get_uint8(x_9, 7);
x_67 = lean_ctor_get_uint8(x_9, 8);
x_68 = lean_ctor_get_uint8(x_9, 10);
x_69 = lean_ctor_get_uint8(x_9, 11);
x_70 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_71 = 2;
x_72 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_72, 0, x_59);
lean_ctor_set_uint8(x_72, 1, x_60);
lean_ctor_set_uint8(x_72, 2, x_61);
lean_ctor_set_uint8(x_72, 3, x_62);
lean_ctor_set_uint8(x_72, 4, x_63);
lean_ctor_set_uint8(x_72, 5, x_64);
lean_ctor_set_uint8(x_72, 6, x_65);
lean_ctor_set_uint8(x_72, 7, x_66);
lean_ctor_set_uint8(x_72, 8, x_67);
lean_ctor_set_uint8(x_72, 9, x_71);
lean_ctor_set_uint8(x_72, 10, x_68);
lean_ctor_set_uint8(x_72, 11, x_69);
lean_ctor_set_uint8(x_72, 12, x_70);
x_73 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_11);
lean_ctor_set(x_73, 2, x_12);
lean_ctor_set(x_73, 3, x_13);
lean_ctor_set(x_73, 4, x_14);
lean_ctor_set(x_73, 5, x_15);
lean_ctor_set_uint8(x_73, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_73, sizeof(void*)*6 + 1, x_58);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_74 = l_Lean_MVarId_getType_x27(x_1, x_73, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__2;
x_78 = lean_unsigned_to_nat(4u);
x_79 = l_Lean_Expr_isAppOfArity(x_75, x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_75);
lean_dec(x_1);
x_80 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_81 = l_Lean_throwError___at_Lean_MVarId_proofIrrelHeq___spec__1(x_80, x_3, x_4, x_5, x_6, x_76);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = l_Lean_Expr_appFn_x21(x_75);
x_83 = l_Lean_Expr_appFn_x21(x_82);
lean_dec(x_82);
x_84 = l_Lean_Expr_appArg_x21(x_83);
lean_dec(x_83);
x_85 = l_Lean_Expr_appArg_x21(x_75);
lean_dec(x_75);
x_86 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1;
x_87 = lean_array_push(x_86, x_84);
x_88 = lean_array_push(x_87, x_85);
x_89 = l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__4;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_90 = l_Lean_Meta_mkAppM(x_89, x_88, x_3, x_4, x_5, x_6, x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_91, x_3, x_4, x_5, x_6, x_92);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_96 = 1;
x_97 = lean_box(x_96);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_95;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_99 = lean_ctor_get(x_90, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_90, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_101 = x_90;
} else {
 lean_dec_ref(x_90);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_103 = lean_ctor_get(x_74, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_74, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_105 = x_74;
} else {
 lean_dec_ref(x_74);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_8);
if (x_107 == 0)
{
return x_8;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_8, 0);
x_109 = lean_ctor_get(x_8, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_8);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_observing_x3f___at_Lean_MVarId_proofIrrelHeq___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_proofIrrelHeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proofIrrelHeq", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_proofIrrelHeq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_proofIrrelHeq___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_MVarId_proofIrrelHeq___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lambda__2), 6, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_proofIrrelHeq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_MVarId_proofIrrelHeq___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_subsingletonElim___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Subsingleton", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_subsingletonElim___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_subsingletonElim___lambda__1___closed__1;
x_2 = l_Lean_MVarId_exfalso___lambda__1___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 5);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_19 = 2;
lean_ctor_set_uint8(x_9, 9, x_19);
x_20 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_11);
lean_ctor_set(x_20, 2, x_12);
lean_ctor_set(x_20, 3, x_13);
lean_ctor_set(x_20, 4, x_14);
lean_ctor_set(x_20, 5, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*6, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*6 + 1, x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_21 = l_Lean_MVarId_getType_x27(x_1, x_20, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_MVarId_propext___lambda__1___closed__2;
x_25 = lean_unsigned_to_nat(3u);
x_26 = l_Lean_Expr_isAppOfArity(x_22, x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_1);
x_27 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_28 = l_Lean_throwError___at_Lean_MVarId_proofIrrelHeq___spec__1(x_27, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = l_Lean_Expr_appFn_x21(x_22);
x_30 = l_Lean_Expr_appArg_x21(x_29);
lean_dec(x_29);
x_31 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_32 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1;
x_33 = lean_array_push(x_32, x_30);
x_34 = lean_array_push(x_33, x_31);
x_35 = l_Lean_MVarId_subsingletonElim___lambda__1___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Lean_Meta_mkAppM(x_35, x_34, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_37, x_3, x_4, x_5, x_6, x_38);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = 1;
x_43 = lean_box(x_42);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = 1;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_36);
if (x_48 == 0)
{
return x_36;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_36, 0);
x_50 = lean_ctor_get(x_36, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_36);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
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
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_21);
if (x_52 == 0)
{
return x_21;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_21, 0);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_21);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_56 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_57 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_58 = lean_ctor_get_uint8(x_9, 0);
x_59 = lean_ctor_get_uint8(x_9, 1);
x_60 = lean_ctor_get_uint8(x_9, 2);
x_61 = lean_ctor_get_uint8(x_9, 3);
x_62 = lean_ctor_get_uint8(x_9, 4);
x_63 = lean_ctor_get_uint8(x_9, 5);
x_64 = lean_ctor_get_uint8(x_9, 6);
x_65 = lean_ctor_get_uint8(x_9, 7);
x_66 = lean_ctor_get_uint8(x_9, 8);
x_67 = lean_ctor_get_uint8(x_9, 10);
x_68 = lean_ctor_get_uint8(x_9, 11);
x_69 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_70 = 2;
x_71 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_71, 0, x_58);
lean_ctor_set_uint8(x_71, 1, x_59);
lean_ctor_set_uint8(x_71, 2, x_60);
lean_ctor_set_uint8(x_71, 3, x_61);
lean_ctor_set_uint8(x_71, 4, x_62);
lean_ctor_set_uint8(x_71, 5, x_63);
lean_ctor_set_uint8(x_71, 6, x_64);
lean_ctor_set_uint8(x_71, 7, x_65);
lean_ctor_set_uint8(x_71, 8, x_66);
lean_ctor_set_uint8(x_71, 9, x_70);
lean_ctor_set_uint8(x_71, 10, x_67);
lean_ctor_set_uint8(x_71, 11, x_68);
lean_ctor_set_uint8(x_71, 12, x_69);
x_72 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_11);
lean_ctor_set(x_72, 2, x_12);
lean_ctor_set(x_72, 3, x_13);
lean_ctor_set(x_72, 4, x_14);
lean_ctor_set(x_72, 5, x_15);
lean_ctor_set_uint8(x_72, sizeof(void*)*6, x_56);
lean_ctor_set_uint8(x_72, sizeof(void*)*6 + 1, x_57);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_73 = l_Lean_MVarId_getType_x27(x_1, x_72, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_MVarId_propext___lambda__1___closed__2;
x_77 = lean_unsigned_to_nat(3u);
x_78 = l_Lean_Expr_isAppOfArity(x_74, x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_74);
lean_dec(x_1);
x_79 = l_Lean_MVarId_iffOfEq___lambda__1___closed__2;
x_80 = l_Lean_throwError___at_Lean_MVarId_proofIrrelHeq___spec__1(x_79, x_3, x_4, x_5, x_6, x_75);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = l_Lean_Expr_appFn_x21(x_74);
x_82 = l_Lean_Expr_appArg_x21(x_81);
lean_dec(x_81);
x_83 = l_Lean_Expr_appArg_x21(x_74);
lean_dec(x_74);
x_84 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1;
x_85 = lean_array_push(x_84, x_82);
x_86 = lean_array_push(x_85, x_83);
x_87 = l_Lean_MVarId_subsingletonElim___lambda__1___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_88 = l_Lean_Meta_mkAppM(x_87, x_86, x_3, x_4, x_5, x_6, x_75);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_89, x_3, x_4, x_5, x_6, x_90);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_94 = 1;
x_95 = lean_box(x_94);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_93;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = lean_ctor_get(x_88, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_99 = x_88;
} else {
 lean_dec_ref(x_88);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = lean_ctor_get(x_73, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_73, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_103 = x_73;
} else {
 lean_dec_ref(x_73);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_8);
if (x_105 == 0)
{
return x_8;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_8, 0);
x_107 = lean_ctor_get(x_8, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_8);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_subsingletonElim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subsingletonElim", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_subsingletonElim___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_subsingletonElim___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_MVarId_subsingletonElim___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lambda__2), 6, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* initialize_Lean_Util_FindMVar(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CollectMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
res = initialize_Lean_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_getExpectedNumArgsAux___closed__1 = _init_l_Lean_Meta_getExpectedNumArgsAux___closed__1();
lean_mark_persistent(l_Lean_Meta_getExpectedNumArgsAux___closed__1);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__4 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___lambda__1___closed__4);
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
l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_synthAppInstances_step___spec__1___lambda__1___closed__4);
l_Lean_Meta_synthAppInstances_step___closed__1 = _init_l_Lean_Meta_synthAppInstances_step___closed__1();
lean_mark_persistent(l_Lean_Meta_synthAppInstances_step___closed__1);
l_Lean_Meta_synthAppInstances_step___closed__2 = _init_l_Lean_Meta_synthAppInstances_step___closed__2();
lean_mark_persistent(l_Lean_Meta_synthAppInstances_step___closed__2);
l_Lean_Meta_synthAppInstances_step___closed__3 = _init_l_Lean_Meta_synthAppInstances_step___closed__3();
lean_mark_persistent(l_Lean_Meta_synthAppInstances_step___closed__3);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1);
l_Lean_MVarId_apply___lambda__1___closed__1 = _init_l_Lean_MVarId_apply___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_apply___lambda__1___closed__1);
l_Lean_MVarId_splitAndCore_go___closed__1 = _init_l_Lean_MVarId_splitAndCore_go___closed__1();
lean_mark_persistent(l_Lean_MVarId_splitAndCore_go___closed__1);
l_Lean_MVarId_splitAndCore_go___closed__2 = _init_l_Lean_MVarId_splitAndCore_go___closed__2();
lean_mark_persistent(l_Lean_MVarId_splitAndCore_go___closed__2);
l_Lean_MVarId_splitAndCore_go___closed__3 = _init_l_Lean_MVarId_splitAndCore_go___closed__3();
lean_mark_persistent(l_Lean_MVarId_splitAndCore_go___closed__3);
l_Lean_MVarId_splitAndCore_go___closed__4 = _init_l_Lean_MVarId_splitAndCore_go___closed__4();
lean_mark_persistent(l_Lean_MVarId_splitAndCore_go___closed__4);
l_Lean_MVarId_splitAndCore_go___closed__5 = _init_l_Lean_MVarId_splitAndCore_go___closed__5();
lean_mark_persistent(l_Lean_MVarId_splitAndCore_go___closed__5);
l_Lean_MVarId_splitAndCore_go___closed__6 = _init_l_Lean_MVarId_splitAndCore_go___closed__6();
lean_mark_persistent(l_Lean_MVarId_splitAndCore_go___closed__6);
l_Lean_MVarId_splitAndCore_go___closed__7 = _init_l_Lean_MVarId_splitAndCore_go___closed__7();
lean_mark_persistent(l_Lean_MVarId_splitAndCore_go___closed__7);
l_Lean_MVarId_splitAndCore___closed__1 = _init_l_Lean_MVarId_splitAndCore___closed__1();
lean_mark_persistent(l_Lean_MVarId_splitAndCore___closed__1);
l_Lean_MVarId_splitAndCore___closed__2 = _init_l_Lean_MVarId_splitAndCore___closed__2();
lean_mark_persistent(l_Lean_MVarId_splitAndCore___closed__2);
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
l_Lean_MVarId_nthConstructor___lambda__1___closed__1 = _init_l_Lean_MVarId_nthConstructor___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_nthConstructor___lambda__1___closed__1);
l_Lean_MVarId_nthConstructor___lambda__1___closed__2 = _init_l_Lean_MVarId_nthConstructor___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_nthConstructor___lambda__1___closed__2);
l_Lean_MVarId_nthConstructor___lambda__1___closed__3 = _init_l_Lean_MVarId_nthConstructor___lambda__1___closed__3();
lean_mark_persistent(l_Lean_MVarId_nthConstructor___lambda__1___closed__3);
l_Lean_MVarId_nthConstructor___lambda__1___closed__4 = _init_l_Lean_MVarId_nthConstructor___lambda__1___closed__4();
lean_mark_persistent(l_Lean_MVarId_nthConstructor___lambda__1___closed__4);
l_Lean_MVarId_nthConstructor___lambda__2___closed__1 = _init_l_Lean_MVarId_nthConstructor___lambda__2___closed__1();
lean_mark_persistent(l_Lean_MVarId_nthConstructor___lambda__2___closed__1);
l_Lean_MVarId_nthConstructor___lambda__2___closed__2 = _init_l_Lean_MVarId_nthConstructor___lambda__2___closed__2();
lean_mark_persistent(l_Lean_MVarId_nthConstructor___lambda__2___closed__2);
l_Lean_MVarId_nthConstructor___lambda__2___closed__3 = _init_l_Lean_MVarId_nthConstructor___lambda__2___closed__3();
lean_mark_persistent(l_Lean_MVarId_nthConstructor___lambda__2___closed__3);
l_Lean_MVarId_nthConstructor___lambda__2___closed__4 = _init_l_Lean_MVarId_nthConstructor___lambda__2___closed__4();
lean_mark_persistent(l_Lean_MVarId_nthConstructor___lambda__2___closed__4);
l_Lean_MVarId_nthConstructor___lambda__2___closed__5 = _init_l_Lean_MVarId_nthConstructor___lambda__2___closed__5();
lean_mark_persistent(l_Lean_MVarId_nthConstructor___lambda__2___closed__5);
l_Lean_MVarId_iffOfEq___lambda__1___closed__1 = _init_l_Lean_MVarId_iffOfEq___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_iffOfEq___lambda__1___closed__1);
l_Lean_MVarId_iffOfEq___lambda__1___closed__2 = _init_l_Lean_MVarId_iffOfEq___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_iffOfEq___lambda__1___closed__2);
l_Lean_MVarId_iffOfEq___closed__1 = _init_l_Lean_MVarId_iffOfEq___closed__1();
lean_mark_persistent(l_Lean_MVarId_iffOfEq___closed__1);
l_Lean_MVarId_iffOfEq___closed__2 = _init_l_Lean_MVarId_iffOfEq___closed__2();
lean_mark_persistent(l_Lean_MVarId_iffOfEq___closed__2);
l_Lean_MVarId_iffOfEq___closed__3 = _init_l_Lean_MVarId_iffOfEq___closed__3();
lean_mark_persistent(l_Lean_MVarId_iffOfEq___closed__3);
l_Lean_MVarId_propext___lambda__1___closed__1 = _init_l_Lean_MVarId_propext___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_propext___lambda__1___closed__1);
l_Lean_MVarId_propext___lambda__1___closed__2 = _init_l_Lean_MVarId_propext___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_propext___lambda__1___closed__2);
l_Lean_MVarId_propext___lambda__1___closed__3 = _init_l_Lean_MVarId_propext___lambda__1___closed__3();
lean_mark_persistent(l_Lean_MVarId_propext___lambda__1___closed__3);
l_Lean_MVarId_propext___lambda__1___closed__4 = _init_l_Lean_MVarId_propext___lambda__1___closed__4();
lean_mark_persistent(l_Lean_MVarId_propext___lambda__1___closed__4);
l_Lean_MVarId_propext___lambda__1___closed__5 = _init_l_Lean_MVarId_propext___lambda__1___closed__5();
lean_mark_persistent(l_Lean_MVarId_propext___lambda__1___closed__5);
l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__1 = _init_l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__1);
l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__2 = _init_l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__2);
l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__3 = _init_l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__3();
lean_mark_persistent(l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__3);
l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__4 = _init_l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__4();
lean_mark_persistent(l_Lean_MVarId_proofIrrelHeq___lambda__1___closed__4);
l_Lean_MVarId_proofIrrelHeq___closed__1 = _init_l_Lean_MVarId_proofIrrelHeq___closed__1();
lean_mark_persistent(l_Lean_MVarId_proofIrrelHeq___closed__1);
l_Lean_MVarId_proofIrrelHeq___closed__2 = _init_l_Lean_MVarId_proofIrrelHeq___closed__2();
lean_mark_persistent(l_Lean_MVarId_proofIrrelHeq___closed__2);
l_Lean_MVarId_subsingletonElim___lambda__1___closed__1 = _init_l_Lean_MVarId_subsingletonElim___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_subsingletonElim___lambda__1___closed__1);
l_Lean_MVarId_subsingletonElim___lambda__1___closed__2 = _init_l_Lean_MVarId_subsingletonElim___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_subsingletonElim___lambda__1___closed__2);
l_Lean_MVarId_subsingletonElim___closed__1 = _init_l_Lean_MVarId_subsingletonElim___closed__1();
lean_mark_persistent(l_Lean_MVarId_subsingletonElim___closed__1);
l_Lean_MVarId_subsingletonElim___closed__2 = _init_l_Lean_MVarId_subsingletonElim___closed__2();
lean_mark_persistent(l_Lean_MVarId_subsingletonElim___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

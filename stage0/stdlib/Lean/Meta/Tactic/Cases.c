// Lean compiler output
// Module: Lean.Meta.Tactic.Cases
// Imports: Lean.Meta.AppBuilder Lean.Meta.Tactic.Induction Lean.Meta.Tactic.Injection Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Subst Lean.Meta.Tactic.Acyclic Lean.Meta.Tactic.UnifyEq
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
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1;
static lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__4;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byCasesDec___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withNewEqs___redArg___closed__0;
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byCasesDec___closed__0;
static lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0;
static lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__2;
static lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__2;
static lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0___closed__0;
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unifyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___closed__0;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__3;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__10;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6;
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3955_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
static lean_object* l_Lean_Meta_generalizeTargetsEq___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0;
static lean_object* l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__7;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_withIncRecDepth___at___Lean_Meta_transformWithCache_visit___at___Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0_spec__0_spec__9_spec__9___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_casesAnd___closed__0;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at___Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byCases___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_MVarId_casesRec_spec__0(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at___Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
static lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__1;
lean_object* l_Lean_MVarId_acyclic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__3;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MVarId_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed(lean_object**);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___closed__0;
lean_object* l_Array_ofSubarray___redArg(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3;
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1;
static lean_object* l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byCasesDec___closed__4;
lean_object* l_Lean_mkNot(lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1___closed__0;
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withNewEqs_loop___redArg___closed__0;
static lean_object* l_Lean_MVarId_byCasesDec___closed__2;
static lean_object* l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
static lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0;
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__9;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2;
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__9(uint8_t, lean_object*, size_t, size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__6;
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0___closed__1;
lean_object* l_Lean_Meta_exactlyOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___closed__1;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__2;
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ensureAtMostOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at___Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getInductiveUniverseAndParams___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_casesAnd___lam__0___closed__0;
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byCasesDec___closed__1;
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__0;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byCases___closed__2;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_casesAnd___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_saturate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkEM(lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at___Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Simp_Arith_withAbstractAtoms_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AssocList_erase___at___Lean_Meta_FVarSubst_erase_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__4;
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___closed__0;
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_casesRec___lam__0___closed__0;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_casesAnd___closed__2;
static lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l_Lean_MVarId_byCases___closed__0;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byCases___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withNewEqs_loop___redArg___closed__1;
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_MVarId_byCases___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0;
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_casesAnd___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___closed__0;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to compile pattern matching, inductive type expected", 59, 59);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1;
x_8 = l_Lean_indentExpr(x_1);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__3;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_whnfD(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Expr_getAppFn(x_8);
if (lean_obj_tag(x_10) == 4)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Environment_find_x3f(x_17, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_free_object(x_13);
lean_dec(x_12);
x_21 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(x_8, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Meta_getInductiveUniverseAndParams___closed__0;
x_26 = l_Lean_Expr_getAppNumArgs(x_8);
lean_inc(x_26);
x_27 = lean_mk_array(x_26, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_26, x_28);
lean_dec(x_26);
x_30 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_8, x_27, x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Array_extract___redArg(x_30, x_31, x_24);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_13, 0, x_33);
return x_13;
}
else
{
lean_object* x_34; 
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_12);
x_34 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(x_8, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_box(0);
x_39 = lean_unbox(x_38);
x_40 = l_Lean_Environment_find_x3f(x_37, x_11, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_12);
x_41 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(x_8, x_2, x_3, x_4, x_5, x_36);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
if (lean_obj_tag(x_42) == 5)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Meta_getInductiveUniverseAndParams___closed__0;
x_46 = l_Lean_Expr_getAppNumArgs(x_8);
lean_inc(x_46);
x_47 = lean_mk_array(x_46, x_45);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_46, x_48);
lean_dec(x_46);
x_50 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_8, x_47, x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Array_extract___redArg(x_50, x_51, x_44);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_36);
return x_54;
}
else
{
lean_object* x_55; 
lean_dec(x_42);
lean_dec(x_12);
x_55 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(x_8, x_2, x_3, x_4, x_5, x_36);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_55;
}
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_10);
x_56 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(x_8, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_7);
if (x_57 == 0)
{
return x_7;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_7, 0);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_7);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refl", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_14 = l_Lean_Meta_getLevel(x_9, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_9);
x_17 = l_Lean_Meta_isExprDefEq(x_9, x_12, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1;
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_24);
x_25 = l_Lean_Expr_const___override(x_22, x_24);
lean_inc(x_1);
lean_inc(x_9);
x_26 = l_Lean_mkApp4(x_25, x_9, x_1, x_12, x_2);
x_27 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3;
x_28 = l_Lean_Expr_const___override(x_27, x_24);
x_29 = l_Lean_mkAppB(x_28, x_9, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_17, 0, x_30);
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_dec(x_17);
x_32 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1;
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_34);
x_35 = l_Lean_Expr_const___override(x_32, x_34);
lean_inc(x_1);
lean_inc(x_9);
x_36 = l_Lean_mkApp4(x_35, x_9, x_1, x_12, x_2);
x_37 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3;
x_38 = l_Lean_Expr_const___override(x_37, x_34);
x_39 = l_Lean_mkAppB(x_38, x_9, x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_31);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_12);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_17, 0);
lean_dec(x_43);
x_44 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5;
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_15);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_46);
x_47 = l_Lean_Expr_const___override(x_44, x_46);
lean_inc(x_1);
lean_inc(x_9);
x_48 = l_Lean_mkApp3(x_47, x_9, x_1, x_2);
x_49 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6;
x_50 = l_Lean_Expr_const___override(x_49, x_46);
x_51 = l_Lean_mkAppB(x_50, x_9, x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_17, 0, x_52);
return x_17;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_dec(x_17);
x_54 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5;
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_15);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_56);
x_57 = l_Lean_Expr_const___override(x_54, x_56);
lean_inc(x_1);
lean_inc(x_9);
x_58 = l_Lean_mkApp3(x_57, x_9, x_1, x_2);
x_59 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6;
x_60 = l_Lean_Expr_const___override(x_59, x_56);
x_61 = l_Lean_mkAppB(x_60, x_9, x_1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_53);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_17);
if (x_64 == 0)
{
return x_17;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_17, 0);
x_66 = lean_ctor_get(x_17, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_17);
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
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_14);
if (x_68 == 0)
{
return x_14;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_14, 0);
x_70 = lean_ctor_get(x_14, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_11);
if (x_72 == 0)
{
return x_11;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_11, 0);
x_74 = lean_ctor_get(x_11, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_8);
if (x_76 == 0)
{
return x_8;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_8, 0);
x_78 = lean_ctor_get(x_8, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_8);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs_loop___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
x_16 = lean_array_push(x_2, x_8);
x_17 = lean_array_push(x_3, x_4);
x_18 = l_Lean_Meta_withNewEqs_loop___redArg(x_5, x_6, x_7, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
static lean_object* _init_l_Lean_Meta_withNewEqs_loop___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_withNewEqs_loop___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_withNewEqs_loop___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_array_get(x_15, x_1, x_4);
x_17 = lean_array_get(x_15, x_2, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(x_16, x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed), 13, 7);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_5);
lean_closure_set(x_23, 2, x_6);
lean_closure_set(x_23, 3, x_22);
lean_closure_set(x_23, 4, x_1);
lean_closure_set(x_23, 5, x_2);
lean_closure_set(x_23, 6, x_3);
x_24 = l_Lean_Meta_withNewEqs_loop___redArg___closed__1;
x_25 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Simp_Arith_withAbstractAtoms_go_spec__0___redArg(x_24, x_21, x_23, x_7, x_8, x_9, x_10, x_20);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withNewEqs_loop___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_withNewEqs_loop___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_withNewEqs___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Meta_withNewEqs___redArg___closed__0;
x_11 = l_Lean_Meta_withNewEqs_loop___redArg(x_1, x_2, x_3, x_9, x_10, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withNewEqs___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_box(1);
x_15 = lean_box(1);
x_16 = lean_unbox(x_13);
x_17 = lean_unbox(x_14);
x_18 = lean_unbox(x_14);
x_19 = lean_unbox(x_15);
x_20 = l_Lean_Meta_mkForallFVars(x_3, x_11, x_16, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unbox(x_13);
x_24 = lean_unbox(x_14);
x_25 = lean_unbox(x_14);
x_26 = lean_unbox(x_15);
x_27 = l_Lean_Meta_mkForallFVars(x_2, x_21, x_23, x_24, x_25, x_26, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_4);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_20);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_10);
if (x_43 == 0)
{
return x_10;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_10, 0);
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_10);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid number of targets #", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", motive only takes #", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_le(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1;
x_14 = l_Nat_reprFast(x_10);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Nat_reprFast(x_11);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_MessageData_ofFormat(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__3;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_25, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Array_toSubarray___redArg(x_3, x_31, x_10);
x_33 = l_Array_ofSubarray___redArg(x_32);
lean_dec(x_32);
lean_inc(x_33);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__0___boxed), 9, 2);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_33);
x_35 = l_Lean_Meta_withNewEqs___redArg(x_1, x_33, x_34, x_5, x_6, x_7, x_8, x_9);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = lean_unbox(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_3, x_4, x_14, x_15, x_6, x_7, x_8, x_9, x_12);
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
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_1);
x_21 = l_Lean_MVarId_getTag(x_1, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_19, x_22, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_9);
lean_dec(x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = l_Lean_mkAppN(x_25, x_5);
x_28 = l_Lean_mkAppN(x_27, x_20);
lean_dec(x_20);
x_29 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_28, x_7, x_26);
lean_dec(x_7);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = l_Lean_Expr_mvarId_x21(x_25);
lean_dec(x_25);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l_Lean_Expr_mvarId_x21(x_25);
lean_dec(x_25);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("generalizeTargets", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_generalizeTargetsEq___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
lean_inc(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__1___boxed), 9, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
x_10 = l_Lean_Meta_generalizeTargetsEq___closed__1;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__2___boxed), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_9);
lean_closure_set(x_11, 4, x_3);
x_12 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_generalizeTargetsEq___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_generalizeTargetsEq___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_generalizeTargetsEq___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_1);
x_18 = l_Lean_MVarId_getType(x_1, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = l_Lean_MVarId_getTag(x_1, x_13, x_14, x_15, x_16, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_push(x_2, x_12);
x_25 = lean_box(1);
x_26 = lean_box(1);
x_27 = lean_unbox(x_25);
x_28 = lean_unbox(x_25);
x_29 = lean_unbox(x_26);
lean_inc(x_24);
x_30 = l_Lean_Meta_mkForallFVars(x_24, x_19, x_3, x_27, x_28, x_29, x_13, x_14, x_15, x_16, x_23);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__0___closed__0;
x_34 = lean_array_push(x_33, x_4);
x_35 = lean_unbox(x_25);
x_36 = lean_unbox(x_25);
x_37 = lean_unbox(x_26);
x_38 = l_Lean_Meta_mkForallFVars(x_34, x_31, x_3, x_35, x_36, x_37, x_13, x_14, x_15, x_16, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unbox(x_25);
x_42 = lean_unbox(x_25);
x_43 = lean_unbox(x_26);
lean_inc(x_5);
x_44 = l_Lean_Meta_mkForallFVars(x_5, x_39, x_3, x_41, x_42, x_43, x_13, x_14, x_15, x_16, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(2);
x_48 = lean_unbox(x_47);
x_49 = l_Lean_Meta_mkFreshExprMVarAt(x_6, x_7, x_45, x_48, x_22, x_8, x_13, x_14, x_15, x_16, x_46);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_50);
x_52 = l_Lean_mkAppN(x_50, x_9);
x_53 = l_Lean_Expr_app___override(x_52, x_10);
x_54 = l_Lean_mkAppN(x_53, x_11);
x_55 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_54, x_14, x_51);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Expr_mvarId_x21(x_50);
lean_dec(x_50);
x_58 = lean_array_get_size(x_5);
lean_dec(x_5);
x_59 = lean_box(0);
x_60 = lean_unbox(x_25);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_61 = l_Lean_Meta_introNCore(x_57, x_58, x_59, x_3, x_60, x_13, x_14, x_15, x_16, x_56);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_unbox(x_25);
x_67 = l_Lean_Meta_intro1Core(x_65, x_66, x_13, x_14, x_15, x_16, x_63);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_array_get_size(x_24);
lean_dec(x_24);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_64);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_67, 0, x_73);
return x_67;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_67, 0);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_67);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_array_get_size(x_24);
lean_dec(x_24);
x_79 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_64);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_64);
lean_dec(x_24);
x_81 = !lean_is_exclusive(x_67);
if (x_81 == 0)
{
return x_67;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_67, 0);
x_83 = lean_ctor_get(x_67, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_67);
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
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_85 = !lean_is_exclusive(x_61);
if (x_85 == 0)
{
return x_61;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_61, 0);
x_87 = lean_ctor_get(x_61, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_61);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_44);
if (x_89 == 0)
{
return x_44;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_44, 0);
x_91 = lean_ctor_get(x_44, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_44);
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
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_38);
if (x_93 == 0)
{
return x_38;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_38, 0);
x_95 = lean_ctor_get(x_38, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_38);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_30);
if (x_97 == 0)
{
return x_30;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_30, 0);
x_99 = lean_ctor_get(x_30, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_30);
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
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_21);
if (x_101 == 0)
{
return x_21;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_21, 0);
x_103 = lean_ctor_get(x_21, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_21);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_18);
if (x_105 == 0)
{
return x_18;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_18, 0);
x_107 = lean_ctor_get(x_18, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_18);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(x_1, x_2, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_array_push(x_11, x_21);
x_23 = lean_box(x_4);
x_24 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed), 17, 11);
lean_closure_set(x_24, 0, x_3);
lean_closure_set(x_24, 1, x_10);
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, x_2);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_6);
lean_closure_set(x_24, 6, x_7);
lean_closure_set(x_24, 7, x_8);
lean_closure_set(x_24, 8, x_9);
lean_closure_set(x_24, 9, x_1);
lean_closure_set(x_24, 10, x_22);
x_25 = l_Lean_Meta_withNewEqs_loop___redArg___closed__1;
x_26 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Simp_Arith_withAbstractAtoms_go_spec__0___redArg(x_25, x_20, x_24, x_12, x_13, x_14, x_15, x_19);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed), 16, 9);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_9);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_6);
lean_closure_set(x_16, 7, x_7);
lean_closure_set(x_16, 8, x_8);
x_17 = l_Lean_Meta_withNewEqs___redArg(x_8, x_4, x_16, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_box(x_3);
lean_inc(x_10);
x_18 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed), 14, 8);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_10);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_5);
lean_closure_set(x_18, 6, x_6);
lean_closure_set(x_18, 7, x_7);
x_19 = l_Lean_mkAppN(x_8, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1;
x_21 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_20, x_15, x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Simp_Arith_withAbstractAtoms_go_spec__0___redArg(x_22, x_19, x_18, x_12, x_13, x_14, x_15, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_9, 0);
lean_inc(x_25);
lean_dec(x_9);
x_26 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Simp_Arith_withAbstractAtoms_go_spec__0___redArg(x_25, x_19, x_18, x_12, x_13, x_14, x_15, x_16);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inductive type expected", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed inductive datatype", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__5;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("indexed inductive type expected", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__9;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__10;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_dec(x_7);
x_25 = lean_array_set(x_8, x_9, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_9, x_26);
lean_dec(x_9);
x_7 = x_23;
x_8 = x_25;
x_9 = x_27;
goto _start;
}
else
{
lean_dec(x_9);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
x_30 = lean_st_ref_get(x_13, x_14);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = lean_unbox(x_34);
x_36 = l_Lean_Environment_find_x3f(x_33, x_29, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = x_10;
x_16 = x_11;
x_17 = x_12;
x_18 = x_13;
x_19 = x_32;
goto block_22;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 5)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_79; uint8_t x_80; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 2);
lean_inc(x_40);
lean_dec(x_38);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_lt(x_79, x_40);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__11;
x_82 = l_Lean_Meta_throwTacticEx___redArg(x_1, x_2, x_81, x_10, x_11, x_12, x_13, x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_82);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
x_64 = x_10;
x_65 = x_11;
x_66 = x_12;
x_67 = x_13;
x_68 = x_32;
goto block_78;
}
block_63:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Array_extract___redArg(x_8, x_46, x_39);
x_48 = l_Lean_mkAppN(x_7, x_47);
lean_dec(x_47);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_48);
x_49 = lean_infer_type(x_48, x_41, x_42, x_43, x_44, x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_array_get_size(x_8);
x_53 = lean_nat_sub(x_52, x_40);
lean_dec(x_40);
x_54 = l_Array_extract___redArg(x_8, x_53, x_52);
lean_dec(x_8);
x_55 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed), 16, 9);
lean_closure_set(x_55, 0, x_3);
lean_closure_set(x_55, 1, x_2);
lean_closure_set(x_55, 2, x_34);
lean_closure_set(x_55, 3, x_4);
lean_closure_set(x_55, 4, x_5);
lean_closure_set(x_55, 5, x_46);
lean_closure_set(x_55, 6, x_54);
lean_closure_set(x_55, 7, x_48);
lean_closure_set(x_55, 8, x_6);
x_56 = lean_unbox(x_34);
x_57 = lean_unbox(x_34);
x_58 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_50, x_55, x_56, x_57, x_41, x_42, x_43, x_44, x_51);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_49);
if (x_59 == 0)
{
return x_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_49, 0);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
block_78:
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_array_get_size(x_8);
x_70 = lean_nat_add(x_40, x_39);
x_71 = lean_nat_dec_eq(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__7;
x_73 = l_Lean_Meta_throwTacticEx___redArg(x_1, x_2, x_72, x_64, x_65, x_66, x_67, x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
return x_73;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
lean_dec(x_1);
x_41 = x_64;
x_42 = x_65;
x_43 = x_66;
x_44 = x_67;
x_45 = x_68;
goto block_63;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = x_10;
x_16 = x_11;
x_17 = x_12;
x_18 = x_13;
x_19 = x_32;
goto block_22;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = x_10;
x_16 = x_11;
x_17 = x_12;
x_18 = x_13;
x_19 = x_14;
goto block_22;
}
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__3;
x_21 = l_Lean_Meta_throwTacticEx___redArg(x_1, x_2, x_20, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Meta_generalizeIndices_x27___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("generalizeIndices", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generalizeIndices_x27___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_generalizeIndices_x27___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Meta_getLocalInstances___redArg(x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_generalizeIndices_x27___lam__0___closed__1;
lean_inc(x_1);
x_13 = l_Lean_MVarId_checkNotAssigned(x_1, x_12, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_15 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Meta_whnfD(x_16, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_4, 2);
lean_inc(x_21);
x_22 = l_Lean_Meta_getInductiveUniverseAndParams___closed__0;
x_23 = l_Lean_Expr_getAppNumArgs(x_19);
lean_inc(x_23);
x_24 = lean_mk_array(x_23, x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_23, x_25);
lean_dec(x_23);
x_27 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0(x_12, x_1, x_2, x_21, x_10, x_3, x_19, x_24, x_26, x_4, x_5, x_6, x_7, x_20);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices_x27___lam__0), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__0(x_1, x_2, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_11);
lean_dec(x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__1(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__2(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3(x_1, x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_3);
x_8 = l_Lean_FVarId_getDecl___redArg(x_1, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Lean_LocalDecl_toExpr(x_9);
x_16 = lean_ctor_get(x_9, 2);
lean_inc(x_16);
lean_dec(x_9);
x_12 = x_16;
goto block_15;
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_Meta_generalizeIndices_x27(x_2, x_11, x_13, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
}
else
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("casesOn", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; 
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_array_set(x_5, x_6, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_6, x_20);
lean_dec(x_6);
x_4 = x_17;
x_5 = x_19;
x_6 = x_21;
goto _start;
}
else
{
lean_dec(x_6);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
x_24 = lean_st_ref_get(x_7, x_8);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Environment_find_x3f(x_28, x_23, x_1);
if (lean_obj_tag(x_29) == 0)
{
lean_free_object(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = x_27;
goto block_12;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 5)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 4);
lean_inc(x_35);
x_36 = lean_array_get_size(x_5);
x_37 = lean_nat_add(x_34, x_33);
lean_dec(x_33);
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_box(0);
lean_ctor_set(x_24, 0, x_39);
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0;
x_42 = l_Lean_Name_str___override(x_40, x_41);
x_43 = l_Lean_Environment_find_x3f(x_2, x_42, x_1);
if (lean_obj_tag(x_43) == 0)
{
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = x_27;
goto block_16;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_List_lengthTR___redArg(x_35);
lean_dec(x_35);
x_48 = lean_nat_sub(x_36, x_34);
lean_dec(x_34);
x_49 = l_Array_extract___redArg(x_5, x_48, x_36);
x_50 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_50, 0, x_31);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_50, 3, x_3);
lean_ctor_set(x_50, 4, x_4);
lean_ctor_set(x_50, 5, x_5);
lean_ctor_set(x_50, 6, x_49);
lean_ctor_set(x_43, 0, x_50);
lean_ctor_set(x_24, 0, x_43);
return x_24;
}
else
{
lean_free_object(x_43);
lean_dec(x_45);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = x_27;
goto block_16;
}
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
if (lean_obj_tag(x_51) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_List_lengthTR___redArg(x_35);
lean_dec(x_35);
x_54 = lean_nat_sub(x_36, x_34);
lean_dec(x_34);
x_55 = l_Array_extract___redArg(x_5, x_54, x_36);
x_56 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_56, 0, x_31);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_53);
lean_ctor_set(x_56, 3, x_3);
lean_ctor_set(x_56, 4, x_4);
lean_ctor_set(x_56, 5, x_5);
lean_ctor_set(x_56, 6, x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_24, 0, x_57);
return x_24;
}
else
{
lean_dec(x_51);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = x_27;
goto block_16;
}
}
}
}
}
else
{
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = x_27;
goto block_12;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_24, 0);
x_59 = lean_ctor_get(x_24, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_24);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Environment_find_x3f(x_60, x_23, x_1);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = x_59;
goto block_12;
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 5)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 4);
lean_inc(x_67);
x_68 = lean_array_get_size(x_5);
x_69 = lean_nat_add(x_66, x_65);
lean_dec(x_65);
x_70 = lean_nat_dec_eq(x_68, x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_59);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
lean_dec(x_64);
x_74 = l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0;
x_75 = l_Lean_Name_str___override(x_73, x_74);
x_76 = l_Lean_Environment_find_x3f(x_2, x_75, x_1);
if (lean_obj_tag(x_76) == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = x_59;
goto block_16;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_obj_tag(x_77) == 1)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_List_lengthTR___redArg(x_67);
lean_dec(x_67);
x_81 = lean_nat_sub(x_68, x_66);
lean_dec(x_66);
x_82 = l_Array_extract___redArg(x_5, x_81, x_68);
x_83 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_83, 0, x_63);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_3);
lean_ctor_set(x_83, 4, x_4);
lean_ctor_set(x_83, 5, x_5);
lean_ctor_set(x_83, 6, x_82);
if (lean_is_scalar(x_78)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_78;
}
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_59);
return x_85;
}
else
{
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = x_59;
goto block_16;
}
}
}
}
else
{
lean_dec(x_62);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = x_59;
goto block_12;
}
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = x_8;
goto block_12;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5;
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
lean_inc(x_14);
x_18 = l_Lean_Environment_contains(x_14, x_15, x_17);
if (x_18 == 0)
{
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_13;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1;
lean_inc(x_14);
x_20 = l_Lean_Environment_contains(x_14, x_19, x_18);
if (x_20 == 0)
{
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_13;
}
else
{
lean_object* x_21; 
lean_dec(x_10);
lean_inc(x_2);
x_21 = l_Lean_FVarId_getDecl___redArg(x_1, x_2, x_4, x_5, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_41; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_41 = lean_ctor_get(x_22, 3);
lean_inc(x_41);
x_25 = x_41;
goto block_40;
block_40:
{
lean_object* x_26; 
lean_inc(x_5);
x_26 = lean_whnf(x_25, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_getInductiveUniverseAndParams___closed__0;
x_30 = l_Lean_Expr_getAppNumArgs(x_27);
lean_inc(x_30);
x_31 = lean_mk_array(x_30, x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_30, x_32);
lean_dec(x_30);
x_34 = lean_unbox(x_24);
x_35 = l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(x_34, x_14, x_22, x_27, x_31, x_33, x_5, x_28);
lean_dec(x_5);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_10;
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_nat_sub(x_3, x_4);
x_10 = lean_array_fget(x_1, x_2);
x_11 = lean_array_fget(x_1, x_9);
lean_dec(x_9);
x_12 = lean_expr_eqv(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_4 = x_14;
goto _start;
}
else
{
lean_dec(x_4);
return x_12;
}
}
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at___Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_nat_sub(x_2, x_3);
lean_inc(x_8);
x_9 = l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(x_1, x_8, x_8, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
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
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at___Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Nat_anyTR_loop___at___Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_spec__1___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_nat_sub(x_2, x_3);
lean_inc(x_8);
x_9 = l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(x_1, x_8, x_8, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = l_Nat_anyTR_loop___at___Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_spec__1___redArg(x_1, x_2, x_11);
return x_12;
}
else
{
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_box(1);
x_14 = lean_array_uget(x_3, x_4);
x_15 = l_Lean_Expr_fvarId_x21(x_14);
lean_dec(x_14);
x_16 = lean_name_eq(x_15, x_1);
lean_dec(x_15);
if (x_16 == 0)
{
x_8 = x_2;
goto block_13;
}
else
{
x_8 = x_16;
goto block_13;
}
block_13:
{
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = lean_unbox(x_7);
return x_12;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_8 = lean_name_eq(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_7, x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_uget(x_6, x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_15, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; 
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = 1;
x_21 = lean_usize_add(x_7, x_20);
x_7 = x_21;
x_13 = x_19;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_13);
return x_28;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_1, x_2);
if (x_13 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_5);
x_15 = lean_nat_dec_le(x_2, x_14);
if (x_15 == 0)
{
lean_dec(x_2);
x_7 = x_14;
goto block_12;
}
else
{
lean_dec(x_14);
x_7 = x_2;
goto block_12;
}
}
block_12:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_1, x_7);
if (x_8 == 0)
{
lean_dec(x_7);
return x_3;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_11 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(x_6, x_4, x_5, x_9, x_10);
if (x_11 == 0)
{
return x_3;
}
else
{
return x_4;
}
}
}
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_7, x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_20; lean_object* x_21; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_42; lean_object* x_43; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_68; lean_object* x_69; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_112; lean_object* x_113; lean_object* x_119; 
x_12 = lean_box(1);
x_119 = lean_array_uget(x_6, x_7);
if (lean_obj_tag(x_119) == 0)
{
x_13 = x_1;
x_14 = x_10;
goto block_19;
}
else
{
lean_object* x_120; uint8_t x_121; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_197; lean_object* x_198; lean_object* x_204; lean_object* x_208; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec(x_119);
x_208 = lean_ctor_get(x_120, 1);
lean_inc(x_208);
x_204 = x_208;
goto block_207;
block_188:
{
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_box(x_121);
x_123 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_123, 0, x_122);
x_124 = lean_box(x_121);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_125 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___lam__1___boxed), 6, 5);
lean_closure_set(x_125, 0, x_2);
lean_closure_set(x_125, 1, x_4);
lean_closure_set(x_125, 2, x_12);
lean_closure_set(x_125, 3, x_124);
lean_closure_set(x_125, 4, x_3);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_ctor_get(x_120, 3);
lean_inc(x_126);
lean_dec(x_120);
x_127 = lean_st_ref_get(x_9, x_10);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_ctor_get(x_127, 1);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__4;
lean_inc(x_131);
lean_ctor_set(x_127, 1, x_131);
lean_ctor_set(x_127, 0, x_132);
x_133 = l_Lean_Expr_hasFVar(x_126);
if (x_133 == 0)
{
uint8_t x_134; 
x_134 = l_Lean_Expr_hasMVar(x_126);
if (x_134 == 0)
{
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_123);
x_94 = x_130;
x_95 = x_134;
x_96 = x_131;
goto block_111;
}
else
{
lean_object* x_135; 
lean_dec(x_131);
x_135 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_125, x_123, x_126, x_127);
x_112 = x_130;
x_113 = x_135;
goto block_118;
}
}
else
{
lean_object* x_136; 
lean_dec(x_131);
x_136 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_125, x_123, x_126, x_127);
x_112 = x_130;
x_113 = x_136;
goto block_118;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_137 = lean_ctor_get(x_127, 0);
x_138 = lean_ctor_get(x_127, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_127);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__4;
lean_inc(x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_Expr_hasFVar(x_126);
if (x_142 == 0)
{
uint8_t x_143; 
x_143 = l_Lean_Expr_hasMVar(x_126);
if (x_143 == 0)
{
lean_dec(x_141);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_123);
x_94 = x_138;
x_95 = x_143;
x_96 = x_139;
goto block_111;
}
else
{
lean_object* x_144; 
lean_dec(x_139);
x_144 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_125, x_123, x_126, x_141);
x_112 = x_138;
x_113 = x_144;
goto block_118;
}
}
else
{
lean_object* x_145; 
lean_dec(x_139);
x_145 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_125, x_123, x_126, x_141);
x_112 = x_138;
x_113 = x_145;
goto block_118;
}
}
}
else
{
uint8_t x_146; 
x_146 = lean_ctor_get_uint8(x_120, sizeof(void*)*5);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_147 = lean_ctor_get(x_120, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_120, 4);
lean_inc(x_148);
lean_dec(x_120);
x_149 = lean_st_ref_get(x_9, x_10);
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_151 = lean_ctor_get(x_149, 0);
x_152 = lean_ctor_get(x_149, 1);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__4;
lean_ctor_set(x_149, 1, x_153);
lean_ctor_set(x_149, 0, x_154);
x_155 = l_Lean_Expr_hasFVar(x_147);
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = l_Lean_Expr_hasMVar(x_147);
if (x_156 == 0)
{
lean_dec(x_147);
x_74 = x_123;
x_75 = x_148;
x_76 = x_125;
x_77 = x_152;
x_78 = x_156;
x_79 = x_149;
goto block_84;
}
else
{
lean_object* x_157; 
lean_inc(x_123);
lean_inc(x_125);
x_157 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_125, x_123, x_147, x_149);
x_85 = x_123;
x_86 = x_148;
x_87 = x_152;
x_88 = x_125;
x_89 = x_157;
goto block_93;
}
}
else
{
lean_object* x_158; 
lean_inc(x_123);
lean_inc(x_125);
x_158 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_125, x_123, x_147, x_149);
x_85 = x_123;
x_86 = x_148;
x_87 = x_152;
x_88 = x_125;
x_89 = x_158;
goto block_93;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_159 = lean_ctor_get(x_149, 0);
x_160 = lean_ctor_get(x_149, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_149);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
lean_dec(x_159);
x_162 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__4;
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = l_Lean_Expr_hasFVar(x_147);
if (x_164 == 0)
{
uint8_t x_165; 
x_165 = l_Lean_Expr_hasMVar(x_147);
if (x_165 == 0)
{
lean_dec(x_147);
x_74 = x_123;
x_75 = x_148;
x_76 = x_125;
x_77 = x_160;
x_78 = x_165;
x_79 = x_163;
goto block_84;
}
else
{
lean_object* x_166; 
lean_inc(x_123);
lean_inc(x_125);
x_166 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_125, x_123, x_147, x_163);
x_85 = x_123;
x_86 = x_148;
x_87 = x_160;
x_88 = x_125;
x_89 = x_166;
goto block_93;
}
}
else
{
lean_object* x_167; 
lean_inc(x_123);
lean_inc(x_125);
x_167 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_125, x_123, x_147, x_163);
x_85 = x_123;
x_86 = x_148;
x_87 = x_160;
x_88 = x_125;
x_89 = x_167;
goto block_93;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_120, 3);
lean_inc(x_168);
lean_dec(x_120);
x_169 = lean_st_ref_get(x_9, x_10);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = lean_ctor_get(x_169, 1);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__4;
lean_inc(x_173);
lean_ctor_set(x_169, 1, x_173);
lean_ctor_set(x_169, 0, x_174);
x_175 = l_Lean_Expr_hasFVar(x_168);
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = l_Lean_Expr_hasMVar(x_168);
if (x_176 == 0)
{
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_125);
lean_dec(x_123);
x_24 = x_172;
x_25 = x_176;
x_26 = x_173;
goto block_41;
}
else
{
lean_object* x_177; 
lean_dec(x_173);
x_177 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_125, x_123, x_168, x_169);
x_42 = x_172;
x_43 = x_177;
goto block_48;
}
}
else
{
lean_object* x_178; 
lean_dec(x_173);
x_178 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_125, x_123, x_168, x_169);
x_42 = x_172;
x_43 = x_178;
goto block_48;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_179 = lean_ctor_get(x_169, 0);
x_180 = lean_ctor_get(x_169, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_169);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__4;
lean_inc(x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = l_Lean_Expr_hasFVar(x_168);
if (x_184 == 0)
{
uint8_t x_185; 
x_185 = l_Lean_Expr_hasMVar(x_168);
if (x_185 == 0)
{
lean_dec(x_183);
lean_dec(x_168);
lean_dec(x_125);
lean_dec(x_123);
x_24 = x_180;
x_25 = x_185;
x_26 = x_181;
goto block_41;
}
else
{
lean_object* x_186; 
lean_dec(x_181);
x_186 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_125, x_123, x_168, x_183);
x_42 = x_180;
x_43 = x_186;
goto block_48;
}
}
else
{
lean_object* x_187; 
lean_dec(x_181);
x_187 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_125, x_123, x_168, x_183);
x_42 = x_180;
x_43 = x_187;
goto block_48;
}
}
}
}
}
else
{
lean_dec(x_120);
x_13 = x_1;
x_14 = x_10;
goto block_19;
}
}
block_196:
{
uint8_t x_192; 
x_192 = lean_nat_dec_lt(x_2, x_191);
if (x_192 == 0)
{
lean_dec(x_191);
lean_dec(x_190);
x_121 = x_189;
goto block_188;
}
else
{
size_t x_193; size_t x_194; uint8_t x_195; 
x_193 = 0;
x_194 = lean_usize_of_nat(x_191);
lean_dec(x_191);
x_195 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(x_190, x_3, x_193, x_194);
lean_dec(x_190);
x_121 = x_195;
goto block_188;
}
}
block_203:
{
uint8_t x_199; 
x_199 = lean_name_eq(x_197, x_198);
if (x_199 == 0)
{
uint8_t x_200; 
x_200 = lean_nat_dec_lt(x_2, x_4);
if (x_200 == 0)
{
lean_dec(x_197);
x_121 = x_199;
goto block_188;
}
else
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_array_get_size(x_3);
x_202 = lean_nat_dec_le(x_4, x_201);
if (x_202 == 0)
{
x_189 = x_199;
x_190 = x_197;
x_191 = x_201;
goto block_196;
}
else
{
lean_dec(x_201);
lean_inc(x_4);
x_189 = x_199;
x_190 = x_197;
x_191 = x_4;
goto block_196;
}
}
}
else
{
lean_dec(x_197);
lean_dec(x_120);
x_20 = x_199;
x_21 = x_10;
goto block_23;
}
}
block_207:
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_5, 3);
x_206 = lean_ctor_get(x_205, 1);
x_197 = x_204;
x_198 = x_206;
goto block_203;
}
}
block_19:
{
if (x_13 == 0)
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_7, x_15);
x_7 = x_16;
x_10 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
block_23:
{
if (x_20 == 0)
{
lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
x_13 = x_1;
x_14 = x_21;
goto block_19;
}
}
block_41:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_st_ref_take(x_9, x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
lean_ctor_set(x_28, 0, x_26);
x_32 = lean_st_ref_set(x_9, x_28, x_29);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_20 = x_25;
x_21 = x_33;
goto block_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_28, 1);
x_35 = lean_ctor_get(x_28, 2);
x_36 = lean_ctor_get(x_28, 3);
x_37 = lean_ctor_get(x_28, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 4, x_37);
x_39 = lean_st_ref_set(x_9, x_38, x_29);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_20 = x_25;
x_21 = x_40;
goto block_23;
}
}
block_48:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unbox(x_45);
lean_dec(x_45);
x_24 = x_42;
x_25 = x_47;
x_26 = x_46;
goto block_41;
}
block_67:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_take(x_9, x_49);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
lean_ctor_set(x_54, 0, x_52);
x_58 = lean_st_ref_set(x_9, x_54, x_55);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_20 = x_50;
x_21 = x_59;
goto block_23;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_54, 1);
x_61 = lean_ctor_get(x_54, 2);
x_62 = lean_ctor_get(x_54, 3);
x_63 = lean_ctor_get(x_54, 4);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_54);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_61);
lean_ctor_set(x_64, 3, x_62);
lean_ctor_set(x_64, 4, x_63);
x_65 = lean_st_ref_set(x_9, x_64, x_55);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_20 = x_50;
x_21 = x_66;
goto block_23;
}
}
block_73:
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_49 = x_68;
x_50 = x_72;
x_51 = x_71;
goto block_67;
}
block_84:
{
if (x_78 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Expr_hasFVar(x_75);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = l_Lean_Expr_hasMVar(x_75);
if (x_81 == 0)
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
x_49 = x_77;
x_50 = x_81;
x_51 = x_79;
goto block_67;
}
else
{
lean_object* x_82; 
x_82 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_76, x_74, x_75, x_79);
x_68 = x_77;
x_69 = x_82;
goto block_73;
}
}
else
{
lean_object* x_83; 
x_83 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_76, x_74, x_75, x_79);
x_68 = x_77;
x_69 = x_83;
goto block_73;
}
}
else
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
x_49 = x_77;
x_50 = x_78;
x_51 = x_79;
goto block_67;
}
}
block_93:
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_unbox(x_90);
lean_dec(x_90);
x_74 = x_85;
x_75 = x_86;
x_76 = x_88;
x_77 = x_87;
x_78 = x_92;
x_79 = x_91;
goto block_84;
}
block_111:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_st_ref_take(x_9, x_94);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 0);
lean_dec(x_101);
lean_ctor_set(x_98, 0, x_96);
x_102 = lean_st_ref_set(x_9, x_98, x_99);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_20 = x_95;
x_21 = x_103;
goto block_23;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_98, 1);
x_105 = lean_ctor_get(x_98, 2);
x_106 = lean_ctor_get(x_98, 3);
x_107 = lean_ctor_get(x_98, 4);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_98);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_96);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 2, x_105);
lean_ctor_set(x_108, 3, x_106);
lean_ctor_set(x_108, 4, x_107);
x_109 = lean_st_ref_set(x_9, x_108, x_99);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_20 = x_95;
x_21 = x_110;
goto block_23;
}
}
block_118:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_unbox(x_115);
lean_dec(x_115);
x_94 = x_112;
x_95 = x_117;
x_96 = x_116;
goto block_111;
}
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_209 = lean_box(0);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_10);
return x_210;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_12);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
if (x_15 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_box(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_12, x_20, x_21, x_7, x_8, x_9, x_10, x_11);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_23);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_11);
return x_28;
}
else
{
if (x_26 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_11);
return x_30;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_33 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_23, x_31, x_32, x_8, x_11);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get_size(x_13);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
else
{
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
lean_dec(x_14);
x_21 = 0;
x_22 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_23 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_13, x_21, x_22, x_8, x_17);
return x_23;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__9(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_box(1);
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_Expr_isFVar(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
return x_9;
}
else
{
if (x_1 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_6);
return x_13;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 6);
lean_inc(x_7);
x_8 = l_Array_isEmpty___redArg(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_35; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_7);
x_35 = lean_nat_dec_lt(x_9, x_10);
if (x_35 == 0)
{
x_11 = x_8;
goto block_34;
}
else
{
if (x_35 == 0)
{
x_11 = x_8;
goto block_34;
}
else
{
size_t x_36; size_t x_37; uint8_t x_38; 
x_36 = 0;
x_37 = lean_usize_of_nat(x_10);
x_38 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__9(x_8, x_7, x_36, x_37);
x_11 = x_38;
goto block_34;
}
}
block_34:
{
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(x_7, x_10, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_13, 1);
x_15 = l_Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(x_12, x_9, x_7, x_10, x_1, x_14, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(1);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_box(x_12);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_box(x_12);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_30 = lean_box(x_11);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_32 = lean_box(x_8);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
return x_33;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_7);
lean_dec(x_1);
x_39 = lean_box(x_8);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_6);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at___Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyTR_loop___at___Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at___Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyTR_loop___at___Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyTR_loop___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(x_1, x_6, x_3, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__5(x_14, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___lam__1(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_14 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg(x_11, x_2, x_3, x_4, x_5, x_6, x_12, x_13, x_9, x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6(x_14, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__9(x_5, x_2, x_6, x_7);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 2);
x_23 = lean_array_uget(x_1, x_2);
lean_inc(x_23);
x_24 = l_Lean_Meta_FVarSubst_get(x_22, x_23);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Meta_saveState___redArg(x_6, x_8, x_9);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Lean_MVarId_clear(x_20, x_25, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_4, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = l_Lean_AssocList_erase___at___Lean_Meta_FVarSubst_erase_spec__0___redArg(x_23, x_22);
lean_dec(x_23);
lean_ctor_set(x_17, 2, x_35);
lean_ctor_set(x_17, 0, x_33);
x_10 = x_4;
x_11 = x_34;
goto block_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_4);
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_dec(x_29);
x_38 = l_Lean_AssocList_erase___at___Lean_Meta_FVarSubst_erase_spec__0___redArg(x_23, x_22);
lean_dec(x_23);
lean_ctor_set(x_17, 2, x_38);
lean_ctor_set(x_17, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_18);
x_10 = x_39;
x_11 = x_37;
goto block_15;
}
}
else
{
uint8_t x_40; 
lean_dec(x_23);
lean_free_object(x_17);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
x_40 = !lean_is_exclusive(x_29);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_47; 
x_41 = lean_ctor_get(x_29, 0);
x_42 = lean_ctor_get(x_29, 1);
lean_inc(x_42);
lean_inc(x_41);
x_47 = l_Lean_Exception_isInterrupt(x_41);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Exception_isRuntime(x_41);
lean_dec(x_41);
x_43 = x_48;
goto block_46;
}
else
{
lean_dec(x_41);
x_43 = x_47;
goto block_46;
}
block_46:
{
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_29);
x_44 = l_Lean_Meta_SavedState_restore___redArg(x_27, x_6, x_8, x_42);
lean_dec(x_27);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_10 = x_4;
x_11 = x_45;
goto block_15;
}
else
{
lean_dec(x_42);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_56; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_29);
lean_inc(x_50);
lean_inc(x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_56 = l_Lean_Exception_isInterrupt(x_49);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Exception_isRuntime(x_49);
lean_dec(x_49);
x_52 = x_57;
goto block_55;
}
else
{
lean_dec(x_49);
x_52 = x_56;
goto block_55;
}
block_55:
{
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
x_53 = l_Lean_Meta_SavedState_restore___redArg(x_27, x_6, x_8, x_50);
lean_dec(x_27);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_10 = x_4;
x_11 = x_54;
goto block_15;
}
else
{
lean_dec(x_50);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_51;
}
}
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_17);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
x_10 = x_4;
x_11 = x_9;
goto block_15;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_17, 0);
x_59 = lean_ctor_get(x_17, 1);
x_60 = lean_ctor_get(x_17, 2);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_17);
x_61 = lean_array_uget(x_1, x_2);
lean_inc(x_61);
x_62 = l_Lean_Meta_FVarSubst_get(x_60, x_61);
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_Meta_saveState___redArg(x_6, x_8, x_9);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_67 = l_Lean_MVarId_clear(x_58, x_63, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_65);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_68 = x_4;
} else {
 lean_dec_ref(x_4);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = l_Lean_AssocList_erase___at___Lean_Meta_FVarSubst_erase_spec__0___redArg(x_61, x_60);
lean_dec(x_61);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_59);
lean_ctor_set(x_72, 2, x_71);
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_18);
x_10 = x_73;
x_11 = x_70;
goto block_15;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_82; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_18);
x_74 = lean_ctor_get(x_67, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_76 = x_67;
} else {
 lean_dec_ref(x_67);
 x_76 = lean_box(0);
}
lean_inc(x_75);
lean_inc(x_74);
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
x_82 = l_Lean_Exception_isInterrupt(x_74);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = l_Lean_Exception_isRuntime(x_74);
lean_dec(x_74);
x_78 = x_83;
goto block_81;
}
else
{
lean_dec(x_74);
x_78 = x_82;
goto block_81;
}
block_81:
{
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = l_Lean_Meta_SavedState_restore___redArg(x_65, x_6, x_8, x_75);
lean_dec(x_65);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_10 = x_4;
x_11 = x_80;
goto block_15;
}
else
{
lean_dec(x_75);
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_77;
}
}
}
}
else
{
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_18);
x_10 = x_4;
x_11 = x_9;
goto block_15;
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_4);
lean_ctor_set(x_84, 1, x_9);
return x_84;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_box(0);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_1);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_23);
x_15 = x_12;
x_16 = x_9;
goto block_21;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_23, x_23);
if (x_25 == 0)
{
lean_dec(x_23);
x_15 = x_12;
x_16 = x_9;
goto block_21;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_23);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(x_1, x_26, x_27, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_15 = x_29;
x_16 = x_30;
goto block_21;
}
else
{
uint8_t x_31; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
block_21:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_14, x_3, x_15);
x_3 = x_18;
x_4 = x_19;
x_9 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_array_size(x_2);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(x_8, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_7, x_10);
if (x_11 == 1)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget(x_6, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 2);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
lean_inc(x_1);
x_18 = lean_array_get(x_1, x_2, x_8);
lean_inc(x_3);
lean_inc(x_18);
x_19 = l_Lean_Expr_const___override(x_18, x_3);
x_20 = l_Lean_mkAppN(x_19, x_4);
x_21 = l_Lean_mkAppN(x_20, x_14);
lean_inc(x_5);
x_22 = l_Lean_Meta_FVarSubst_insert(x_15, x_5, x_21);
lean_ctor_set(x_12, 2, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_18);
x_24 = lean_nat_add(x_8, x_16);
lean_dec(x_8);
x_25 = lean_array_push(x_9, x_23);
x_7 = x_17;
x_8 = x_24;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
x_29 = lean_ctor_get(x_12, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_7, x_30);
lean_dec(x_7);
lean_inc(x_1);
x_32 = lean_array_get(x_1, x_2, x_8);
lean_inc(x_3);
lean_inc(x_32);
x_33 = l_Lean_Expr_const___override(x_32, x_3);
x_34 = l_Lean_mkAppN(x_33, x_4);
x_35 = l_Lean_mkAppN(x_34, x_28);
lean_inc(x_5);
x_36 = l_Lean_Meta_FVarSubst_insert(x_29, x_5, x_35);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
x_39 = lean_nat_add(x_8, x_30);
lean_dec(x_8);
x_40 = lean_array_push(x_9, x_38);
x_7 = x_31;
x_8 = x_39;
x_9 = x_40;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapFinIdxM_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_box(0);
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_7);
x_10 = l_Array_mapFinIdxM_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(x_6, x_2, x_4, x_5, x_3, x_1, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapFinIdxM_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapFinIdxM_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Cases_unifyEqs_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 2);
x_14 = lean_ctor_get(x_7, 3);
x_15 = lean_ctor_get(x_7, 4);
x_16 = lean_ctor_get(x_7, 5);
x_17 = lean_ctor_get(x_7, 6);
x_18 = lean_ctor_get(x_7, 7);
x_19 = lean_ctor_get(x_7, 8);
x_20 = lean_ctor_get(x_7, 9);
x_21 = lean_ctor_get(x_7, 10);
x_22 = lean_ctor_get(x_7, 11);
x_23 = lean_ctor_get(x_7, 12);
x_24 = lean_nat_dec_eq(x_14, x_15);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_1, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_14, x_27);
lean_dec(x_14);
lean_ctor_set(x_7, 3, x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Lean_Meta_intro1Core(x_2, x_24, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Lean_Meta_Cases_unifyEqs_x3f___closed__0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_35 = l_Lean_Meta_unifyEq_x3f(x_33, x_32, x_3, x_34, x_4, x_5, x_6, x_7, x_8, x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 2);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_nat_sub(x_1, x_27);
lean_dec(x_1);
x_49 = lean_nat_add(x_48, x_47);
lean_dec(x_47);
lean_dec(x_48);
x_1 = x_49;
x_2 = x_45;
x_3 = x_46;
x_9 = x_44;
goto _start;
}
}
else
{
uint8_t x_51; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_35);
if (x_51 == 0)
{
return x_35;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_29);
if (x_55 == 0)
{
return x_29;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_29, 0);
x_57 = lean_ctor_get(x_29, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_29);
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
lean_free_object(x_7);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_2);
lean_ctor_set(x_59, 1, x_3);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_9);
return x_61;
}
}
else
{
lean_object* x_62; 
lean_free_object(x_7);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_withIncRecDepth___at___Lean_Meta_transformWithCache_visit___at___Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0_spec__0_spec__9_spec__9___redArg(x_16, x_9);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; uint8_t x_78; 
x_63 = lean_ctor_get(x_7, 0);
x_64 = lean_ctor_get(x_7, 1);
x_65 = lean_ctor_get(x_7, 2);
x_66 = lean_ctor_get(x_7, 3);
x_67 = lean_ctor_get(x_7, 4);
x_68 = lean_ctor_get(x_7, 5);
x_69 = lean_ctor_get(x_7, 6);
x_70 = lean_ctor_get(x_7, 7);
x_71 = lean_ctor_get(x_7, 8);
x_72 = lean_ctor_get(x_7, 9);
x_73 = lean_ctor_get(x_7, 10);
x_74 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_75 = lean_ctor_get(x_7, 11);
x_76 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_77 = lean_ctor_get(x_7, 12);
lean_inc(x_77);
lean_inc(x_75);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_7);
x_78 = lean_nat_dec_eq(x_66, x_67);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_eq(x_1, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_66, x_81);
lean_dec(x_66);
x_83 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_83, 0, x_63);
lean_ctor_set(x_83, 1, x_64);
lean_ctor_set(x_83, 2, x_65);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 4, x_67);
lean_ctor_set(x_83, 5, x_68);
lean_ctor_set(x_83, 6, x_69);
lean_ctor_set(x_83, 7, x_70);
lean_ctor_set(x_83, 8, x_71);
lean_ctor_set(x_83, 9, x_72);
lean_ctor_set(x_83, 10, x_73);
lean_ctor_set(x_83, 11, x_75);
lean_ctor_set(x_83, 12, x_77);
lean_ctor_set_uint8(x_83, sizeof(void*)*13, x_74);
lean_ctor_set_uint8(x_83, sizeof(void*)*13 + 1, x_76);
lean_inc(x_8);
lean_inc(x_83);
lean_inc(x_6);
lean_inc(x_5);
x_84 = l_Lean_Meta_intro1Core(x_2, x_78, x_5, x_6, x_83, x_8, x_9);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = l_Lean_Meta_Cases_unifyEqs_x3f___closed__0;
lean_inc(x_8);
lean_inc(x_83);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_90 = l_Lean_Meta_unifyEq_x3f(x_88, x_87, x_3, x_89, x_4, x_5, x_6, x_83, x_8, x_86);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_83);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
x_94 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
lean_dec(x_90);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 2);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_nat_sub(x_1, x_81);
lean_dec(x_1);
x_102 = lean_nat_add(x_101, x_100);
lean_dec(x_100);
lean_dec(x_101);
x_1 = x_102;
x_2 = x_98;
x_3 = x_99;
x_7 = x_83;
x_9 = x_97;
goto _start;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_83);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_104 = lean_ctor_get(x_90, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_90, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_106 = x_90;
} else {
 lean_dec_ref(x_90);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_83);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_108 = lean_ctor_get(x_84, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_84, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_110 = x_84;
} else {
 lean_dec_ref(x_84);
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
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_2);
lean_ctor_set(x_112, 1, x_3);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_9);
return x_114;
}
}
else
{
lean_object* x_115; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_withIncRecDepth___at___Lean_Meta_transformWithCache_visit___at___Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0_spec__0_spec__9_spec__9___redArg(x_68, x_9);
return x_115;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_Meta_FVarSubst_apply(x_1, x_6);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_21 = l_Lean_Meta_Cases_unifyEqs_x3f(x_1, x_17, x_19, x_20, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_free_object(x_14);
lean_dec(x_18);
lean_free_object(x_12);
lean_dec(x_16);
x_24 = x_5;
goto block_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_size(x_18);
x_33 = 0;
lean_inc(x_31);
x_34 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(x_31, x_32, x_33, x_18);
lean_ctor_set(x_14, 2, x_31);
lean_ctor_set(x_14, 1, x_34);
lean_ctor_set(x_14, 0, x_30);
x_35 = lean_array_push(x_5, x_12);
x_24 = x_35;
goto block_28;
}
block_28:
{
size_t x_25; size_t x_26; 
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_3 = x_26;
x_5 = x_24;
x_10 = x_23;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_14);
lean_dec(x_18);
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_12, 1);
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
x_43 = lean_ctor_get(x_14, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
lean_inc(x_40);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_45 = l_Lean_Meta_Cases_unifyEqs_x3f(x_1, x_41, x_43, x_44, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_dec(x_42);
lean_free_object(x_12);
lean_dec(x_40);
x_48 = x_5;
goto block_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_array_size(x_42);
x_57 = 0;
lean_inc(x_55);
x_58 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(x_55, x_56, x_57, x_42);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_12, 0, x_59);
x_60 = lean_array_push(x_5, x_12);
x_48 = x_60;
goto block_52;
}
block_52:
{
size_t x_49; size_t x_50; 
x_49 = 1;
x_50 = lean_usize_add(x_3, x_49);
x_3 = x_50;
x_5 = x_48;
x_10 = x_47;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_42);
lean_free_object(x_12);
lean_dec(x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_45, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_63 = x_45;
} else {
 lean_dec_ref(x_45);
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
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_12, 0);
x_66 = lean_ctor_get(x_12, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_12);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
lean_inc(x_66);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_66);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_72 = l_Lean_Meta_Cases_unifyEqs_x3f(x_1, x_67, x_69, x_71, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_66);
x_75 = x_5;
goto block_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
lean_dec(x_73);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_array_size(x_68);
x_84 = 0;
lean_inc(x_82);
x_85 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(x_82, x_83, x_84, x_68);
if (lean_is_scalar(x_70)) {
 x_86 = lean_alloc_ctor(0, 3, 0);
} else {
 x_86 = x_70;
}
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_82);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_66);
x_88 = lean_array_push(x_5, x_87);
x_75 = x_88;
goto block_79;
}
block_79:
{
size_t x_76; size_t x_77; 
x_76 = 1;
x_77 = lean_usize_add(x_3, x_76);
x_3 = x_77;
x_5 = x_75;
x_10 = x_74;
goto _start;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_89 = lean_ctor_get(x_72, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_72, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_91 = x_72;
} else {
 lean_dec_ref(x_72);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_5);
lean_ctor_set(x_93, 1, x_10);
return x_93;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_21 = l_Lean_Meta_Cases_unifyEqs_x3f(x_1, x_17, x_19, x_20, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_free_object(x_14);
lean_dec(x_18);
lean_free_object(x_12);
lean_dec(x_16);
x_24 = x_5;
goto block_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_size(x_18);
x_33 = 0;
lean_inc(x_31);
x_34 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(x_31, x_32, x_33, x_18);
lean_ctor_set(x_14, 2, x_31);
lean_ctor_set(x_14, 1, x_34);
lean_ctor_set(x_14, 0, x_30);
x_35 = lean_array_push(x_5, x_12);
x_24 = x_35;
goto block_28;
}
block_28:
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(x_1, x_2, x_26, x_4, x_24, x_6, x_7, x_8, x_9, x_23);
return x_27;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_14);
lean_dec(x_18);
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_12, 1);
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
x_43 = lean_ctor_get(x_14, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
lean_inc(x_40);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_45 = l_Lean_Meta_Cases_unifyEqs_x3f(x_1, x_41, x_43, x_44, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_dec(x_42);
lean_free_object(x_12);
lean_dec(x_40);
x_48 = x_5;
goto block_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_array_size(x_42);
x_57 = 0;
lean_inc(x_55);
x_58 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(x_55, x_56, x_57, x_42);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_12, 0, x_59);
x_60 = lean_array_push(x_5, x_12);
x_48 = x_60;
goto block_52;
}
block_52:
{
size_t x_49; size_t x_50; lean_object* x_51; 
x_49 = 1;
x_50 = lean_usize_add(x_3, x_49);
x_51 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(x_1, x_2, x_50, x_4, x_48, x_6, x_7, x_8, x_9, x_47);
return x_51;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_42);
lean_free_object(x_12);
lean_dec(x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_45, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_63 = x_45;
} else {
 lean_dec_ref(x_45);
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
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_12, 0);
x_66 = lean_ctor_get(x_12, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_12);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
lean_inc(x_66);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_66);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_72 = l_Lean_Meta_Cases_unifyEqs_x3f(x_1, x_67, x_69, x_71, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_66);
x_75 = x_5;
goto block_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
lean_dec(x_73);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_array_size(x_68);
x_84 = 0;
lean_inc(x_82);
x_85 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(x_82, x_83, x_84, x_68);
if (lean_is_scalar(x_70)) {
 x_86 = lean_alloc_ctor(0, 3, 0);
} else {
 x_86 = x_70;
}
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_82);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_66);
x_88 = lean_array_push(x_5, x_87);
x_75 = x_88;
goto block_79;
}
block_79:
{
size_t x_76; size_t x_77; lean_object* x_78; 
x_76 = 1;
x_77 = lean_usize_add(x_3, x_76);
x_78 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(x_1, x_2, x_77, x_4, x_75, x_6, x_7, x_8, x_9, x_74);
return x_78;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_89 = lean_ctor_get(x_72, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_72, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_91 = x_72;
} else {
 lean_dec_ref(x_72);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_5);
lean_ctor_set(x_93, 1, x_10);
return x_93;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___closed__0;
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_10, x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_17 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(x_1, x_2, x_15, x_16, x_9, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("casesAuxOn", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = lean_infer_type(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Meta_getInductiveUniverseAndParams(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_st_ref_get(x_10, x_17);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 4);
lean_inc(x_25);
lean_dec(x_21);
x_47 = lean_ctor_get(x_24, 0);
lean_inc(x_47);
lean_dec(x_24);
x_48 = lean_ctor_get(x_22, 0);
lean_inc(x_48);
lean_dec(x_22);
lean_inc(x_47);
x_49 = l_Lean_mkCasesOnName(x_47);
if (x_6 == 0)
{
lean_dec(x_48);
lean_dec(x_47);
x_26 = x_49;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_23;
goto block_46;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1;
x_51 = lean_name_eq(x_47, x_50);
lean_dec(x_47);
if (x_51 == 0)
{
lean_dec(x_48);
x_26 = x_49;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_23;
goto block_46;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3;
x_53 = l_Lean_Environment_contains(x_48, x_52, x_51);
if (x_53 == 0)
{
x_26 = x_49;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_23;
goto block_46;
}
else
{
lean_dec(x_49);
x_26 = x_52;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_23;
goto block_46;
}
}
}
block_46:
{
lean_object* x_32; 
lean_inc(x_4);
x_32 = l_Lean_MVarId_induction(x_3, x_4, x_26, x_5, x_27, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_array_mk(x_25);
x_36 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_34, x_35, x_4, x_18, x_19);
lean_dec(x_19);
lean_dec(x_35);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_array_mk(x_25);
x_40 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_37, x_39, x_4, x_18, x_19);
lean_dec(x_19);
lean_dec(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
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
uint8_t x_54; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
return x_15;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = lean_ctor_get(x_15, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
return x_12;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_12, 0);
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_12);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
x_11 = l_Lean_Expr_fvar___override(x_2);
x_12 = lean_box(x_5);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed), 11, 6);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_12);
x_14 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not applicable to the given hypothesis", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lam__0___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lam__0___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after generalizeIndices\n", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lam__0___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_14 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(x_3, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Cases_cases___lam__0___closed__3;
x_18 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_17, x_7, x_8, x_9, x_10, x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_generalizeIndices(x_1, x_3, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_45 = l_Lean_Meta_Cases_cases___lam__0___closed__4;
x_46 = l_Lean_Meta_Cases_cases___lam__0___closed__5;
x_47 = l_Lean_Name_mkStr3(x_45, x_46, x_4);
lean_inc(x_47);
x_48 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_47, x_9, x_28);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_47);
lean_free_object(x_15);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_51;
goto block_44;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_48, 1);
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_27, 0);
lean_inc(x_55);
x_56 = l_Lean_Meta_Cases_cases___lam__0___closed__7;
lean_ctor_set(x_15, 0, x_55);
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_15);
lean_ctor_set(x_48, 0, x_56);
x_57 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__3;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_47, x_58, x_7, x_8, x_9, x_10, x_53);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_60;
goto block_44;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_dec(x_48);
x_62 = lean_ctor_get(x_27, 0);
lean_inc(x_62);
x_63 = l_Lean_Meta_Cases_cases___lam__0___closed__7;
lean_ctor_set(x_15, 0, x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_15);
x_65 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__3;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_47, x_66, x_7, x_8, x_9, x_10, x_61);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_68;
goto block_44;
}
}
block_44:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 3);
lean_inc(x_36);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_37 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_34, x_35, x_5, x_20, x_25, x_29, x_30, x_31, x_32, x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_40 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(x_27, x_38, x_29, x_30, x_31, x_32, x_39);
lean_dec(x_27);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(x_36, x_41, x_29, x_30, x_31, x_32, x_42);
lean_dec(x_41);
return x_43;
}
else
{
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
return x_40;
}
}
else
{
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
return x_37;
}
}
}
else
{
uint8_t x_69; 
lean_free_object(x_15);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_26);
if (x_69 == 0)
{
return x_26;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_26, 0);
x_71 = lean_ctor_get(x_26, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_26);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_free_object(x_15);
lean_dec(x_4);
x_73 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_1, x_3, x_5, x_20, x_6, x_7, x_8, x_9, x_10, x_22);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_15, 0);
lean_inc(x_74);
lean_dec(x_15);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_14, 1);
lean_inc(x_76);
lean_dec(x_14);
x_77 = lean_ctor_get(x_75, 2);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_eq(x_77, x_78);
lean_dec(x_77);
if (x_79 == 0)
{
lean_object* x_80; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_80 = l_Lean_Meta_generalizeIndices(x_1, x_3, x_7, x_8, x_9, x_10, x_76);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_99 = l_Lean_Meta_Cases_cases___lam__0___closed__4;
x_100 = l_Lean_Meta_Cases_cases___lam__0___closed__5;
x_101 = l_Lean_Name_mkStr3(x_99, x_100, x_4);
lean_inc(x_101);
x_102 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_101, x_9, x_82);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_101);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_83 = x_7;
x_84 = x_8;
x_85 = x_9;
x_86 = x_10;
x_87 = x_105;
goto block_98;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_107 = x_102;
} else {
 lean_dec_ref(x_102);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_81, 0);
lean_inc(x_108);
x_109 = l_Lean_Meta_Cases_cases___lam__0___closed__7;
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_108);
if (lean_is_scalar(x_107)) {
 x_111 = lean_alloc_ctor(7, 2, 0);
} else {
 x_111 = x_107;
 lean_ctor_set_tag(x_111, 7);
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__3;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_101, x_113, x_7, x_8, x_9, x_10, x_106);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_83 = x_7;
x_84 = x_8;
x_85 = x_9;
x_86 = x_10;
x_87 = x_115;
goto block_98;
}
block_98:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_81, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_81, 3);
lean_inc(x_90);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
x_91 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_88, x_89, x_5, x_74, x_79, x_83, x_84, x_85, x_86, x_87);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
x_94 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(x_81, x_92, x_83, x_84, x_85, x_86, x_93);
lean_dec(x_81);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(x_90, x_95, x_83, x_84, x_85, x_86, x_96);
lean_dec(x_95);
return x_97;
}
else
{
lean_dec(x_90);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
return x_94;
}
}
else
{
lean_dec(x_90);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_81);
return x_91;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_74);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_116 = lean_ctor_get(x_80, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_80, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_118 = x_80;
} else {
 lean_dec_ref(x_80);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; 
lean_dec(x_4);
x_120 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_1, x_3, x_5, x_74, x_6, x_7, x_8, x_9, x_10, x_76);
return x_120;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_14);
if (x_121 == 0)
{
return x_14;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_14, 0);
x_123 = lean_ctor_get(x_14, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_14);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_12);
if (x_125 == 0)
{
return x_12;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_12, 0);
x_127 = lean_ctor_get(x_12, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_12);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cases", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Meta_Cases_cases___closed__0;
x_11 = l_Lean_Meta_Cases_cases___closed__1;
x_12 = lean_box(x_4);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lam__0___boxed), 11, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_10);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_20 = l_Lean_Exception_isInterrupt(x_15);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_15);
x_17 = x_21;
goto block_19;
}
else
{
x_17 = x_20;
goto block_19;
}
block_19:
{
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
x_18 = l_Lean_Meta_throwNestedTacticEx___redArg(x_11, x_15, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_Meta_Cases_cases___lam__0(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_MVarId_cases(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_MVarId_casesRec_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_9);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_9, x_8);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = lean_array_uget(x_7, x_9);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_19);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_21, x_19, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_10, 0, x_26);
lean_ctor_set(x_22, 0, x_10);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_10, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_19);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_31);
lean_ctor_set(x_10, 0, x_6);
x_32 = 1;
x_33 = lean_usize_add(x_9, x_32);
x_9 = x_33;
x_15 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_10);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_dec(x_10);
x_40 = lean_array_uget(x_7, x_9);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_39);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_41 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_40, x_39, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
lean_dec(x_39);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
lean_inc(x_6);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_6);
lean_ctor_set(x_50, 1, x_49);
x_51 = 1;
x_52 = lean_usize_add(x_9, x_51);
x_9 = x_52;
x_10 = x_50;
x_15 = x_48;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_56 = x_41;
} else {
 lean_dec_ref(x_41);
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
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_15);
x_18 = lean_apply_7(x_1, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_6, 0, x_2);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_11 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_dec(x_6);
x_36 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_35);
x_37 = lean_apply_7(x_1, x_36, x_35, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
lean_dec(x_35);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
lean_inc(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_45);
x_47 = 1;
x_48 = lean_usize_add(x_5, x_47);
x_5 = x_48;
x_6 = x_46;
x_11 = x_44;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_52 = x_37;
} else {
 lean_dec_ref(x_37);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_array_to_list(x_12);
x_14 = lean_box(0);
x_15 = l_List_mapTR_loop___at___Lean_MVarId_casesRec_spec__0(x_13, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_array_to_list(x_16);
x_19 = lean_box(0);
x_20 = l_List_mapTR_loop___at___Lean_MVarId_casesRec_spec__0(x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
uint8_t x_22; 
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
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_15 = x_5;
} else {
 lean_dec_ref(x_5);
 x_15 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_16 = lean_apply_6(x_1, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_51; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_51 = lean_unbox(x_18);
lean_dec(x_18);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_16, 0, x_52);
return x_16;
}
else
{
lean_object* x_53; 
lean_free_object(x_16);
x_53 = lean_ctor_get(x_14, 1);
lean_inc(x_53);
lean_dec(x_14);
x_20 = x_53;
goto block_50;
}
block_50:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1___closed__0;
x_22 = lean_box(0);
x_23 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__0___boxed), 9, 4);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_22);
x_24 = l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0___redArg(x_23, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
lean_inc(x_25);
if (lean_is_scalar(x_15)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_15;
}
lean_ctor_set(x_34, 0, x_25);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_25, 0);
lean_dec(x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_4);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_25);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_4);
x_39 = lean_alloc_ctor(0, 1, 0);
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
lean_inc(x_25);
if (lean_is_scalar(x_15)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_15;
}
lean_ctor_set(x_41, 0, x_25);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_42 = x_25;
} else {
 lean_dec_ref(x_25);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_4);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_42;
 lean_ctor_set_tag(x_44, 0);
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
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_78; 
x_54 = lean_ctor_get(x_16, 0);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_16);
x_78 = lean_unbox(x_54);
lean_dec(x_54);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_2);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_55);
return x_80;
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_14, 1);
lean_inc(x_81);
lean_dec(x_14);
x_56 = x_81;
goto block_77;
}
block_77:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1___closed__0;
x_58 = lean_box(0);
x_59 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__0___boxed), 9, 4);
lean_closure_set(x_59, 0, x_3);
lean_closure_set(x_59, 1, x_56);
lean_closure_set(x_59, 2, x_57);
lean_closure_set(x_59, 3, x_58);
x_60 = l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0___redArg(x_59, x_7, x_8, x_9, x_10, x_55);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_15);
lean_dec(x_4);
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
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_2);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_2);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
lean_inc(x_61);
if (lean_is_scalar(x_15)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_15;
}
lean_ctor_set(x_68, 0, x_61);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_4);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_69;
 lean_ctor_set_tag(x_71, 0);
}
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
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_73 = lean_ctor_get(x_60, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_60, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_75 = x_60;
} else {
 lean_dec_ref(x_60);
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
uint8_t x_82; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_16);
if (x_82 == 0)
{
return x_16;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_16, 0);
x_84 = lean_ctor_get(x_16, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_16);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
x_17 = lean_array_size(x_14);
x_18 = 0;
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_15, x_14, x_17, x_18, x_16, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_free_object(x_6);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_free_object(x_6);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
lean_dec(x_6);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_7);
x_41 = lean_array_size(x_38);
x_42 = 0;
x_43 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_39, x_38, x_41, x_42, x_40, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_38);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_47 = x_43;
} else {
 lean_dec_ref(x_43);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_44);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
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
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_43, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_57 = x_43;
} else {
 lean_dec_ref(x_43);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_6);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_6, 0);
x_61 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1), 11, 4);
lean_closure_set(x_61, 0, x_1);
lean_closure_set(x_61, 1, x_2);
lean_closure_set(x_61, 2, x_3);
lean_closure_set(x_61, 3, x_4);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_7);
x_64 = lean_array_size(x_60);
x_65 = 0;
x_66 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__2(x_61, x_62, x_60, x_64, x_65, x_63, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_60);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
lean_ctor_set(x_6, 0, x_71);
lean_ctor_set(x_66, 0, x_6);
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec(x_67);
lean_ctor_set(x_6, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_6);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_67);
lean_free_object(x_6);
x_75 = !lean_is_exclusive(x_66);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_66, 0);
lean_dec(x_76);
x_77 = lean_ctor_get(x_68, 0);
lean_inc(x_77);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_77);
return x_66;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_dec(x_66);
x_79 = lean_ctor_get(x_68, 0);
lean_inc(x_79);
lean_dec(x_68);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_free_object(x_6);
x_81 = !lean_is_exclusive(x_66);
if (x_81 == 0)
{
return x_66;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_66, 0);
x_83 = lean_ctor_get(x_66, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_66);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; size_t x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_6, 0);
lean_inc(x_85);
lean_dec(x_6);
x_86 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1), 11, 4);
lean_closure_set(x_86, 0, x_1);
lean_closure_set(x_86, 1, x_2);
lean_closure_set(x_86, 2, x_3);
lean_closure_set(x_86, 3, x_4);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_7);
x_89 = lean_array_size(x_85);
x_90 = 0;
x_91 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__2(x_86, x_87, x_85, x_89, x_90, x_88, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_85);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
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
lean_dec(x_92);
x_99 = lean_ctor_get(x_91, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_100 = x_91;
} else {
 lean_dec_ref(x_91);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_93, 0);
lean_inc(x_101);
lean_dec(x_93);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_91, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_91, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_105 = x_91;
} else {
 lean_dec_ref(x_91);
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
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_15);
x_18 = lean_apply_7(x_1, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_6, 0, x_19);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_27 = x_19;
} else {
 lean_dec_ref(x_19);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
 lean_ctor_set_tag(x_28, 1);
}
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_6, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_15);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_31);
lean_ctor_set(x_6, 0, x_2);
x_32 = 1;
x_33 = lean_usize_add(x_5, x_32);
x_5 = x_33;
x_11 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_39);
x_41 = lean_apply_7(x_1, x_40, x_39, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_46;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; 
lean_dec(x_39);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
lean_inc(x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_51);
x_53 = 1;
x_54 = lean_usize_add(x_5, x_53);
x_5 = x_54;
x_6 = x_52;
x_11 = x_50;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_58 = x_41;
} else {
 lean_dec_ref(x_41);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_array_to_list(x_12);
x_14 = lean_box(0);
x_15 = l_List_mapTR_loop___at___Lean_MVarId_casesRec_spec__0(x_13, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_array_to_list(x_16);
x_19 = lean_box(0);
x_20 = l_List_mapTR_loop___at___Lean_MVarId_casesRec_spec__0(x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
uint8_t x_22; 
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_15 = x_5;
} else {
 lean_dec_ref(x_5);
 x_15 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_16 = lean_apply_6(x_1, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_51; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_51 = lean_unbox(x_18);
lean_dec(x_18);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_16, 0, x_52);
return x_16;
}
else
{
lean_object* x_53; 
lean_free_object(x_16);
x_53 = lean_ctor_get(x_14, 1);
lean_inc(x_53);
lean_dec(x_14);
x_20 = x_53;
goto block_50;
}
block_50:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1___closed__0;
x_22 = lean_box(0);
x_23 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1___lam__0___boxed), 9, 4);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_22);
x_24 = l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0___redArg(x_23, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
lean_inc(x_25);
if (lean_is_scalar(x_15)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_15;
}
lean_ctor_set(x_34, 0, x_25);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_25, 0);
lean_dec(x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_4);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_25);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_4);
x_39 = lean_alloc_ctor(0, 1, 0);
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
lean_inc(x_25);
if (lean_is_scalar(x_15)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_15;
}
lean_ctor_set(x_41, 0, x_25);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_42 = x_25;
} else {
 lean_dec_ref(x_25);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_4);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_42;
 lean_ctor_set_tag(x_44, 0);
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
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_78; 
x_54 = lean_ctor_get(x_16, 0);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_16);
x_78 = lean_unbox(x_54);
lean_dec(x_54);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_2);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_55);
return x_80;
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_14, 1);
lean_inc(x_81);
lean_dec(x_14);
x_56 = x_81;
goto block_77;
}
block_77:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1___closed__0;
x_58 = lean_box(0);
x_59 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1___lam__0___boxed), 9, 4);
lean_closure_set(x_59, 0, x_3);
lean_closure_set(x_59, 1, x_56);
lean_closure_set(x_59, 2, x_57);
lean_closure_set(x_59, 3, x_58);
x_60 = l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0___redArg(x_59, x_7, x_8, x_9, x_10, x_55);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_15);
lean_dec(x_4);
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
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_2);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_2);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
lean_inc(x_61);
if (lean_is_scalar(x_15)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_15;
}
lean_ctor_set(x_68, 0, x_61);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_4);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_69;
 lean_ctor_set_tag(x_71, 0);
}
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
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_73 = lean_ctor_get(x_60, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_60, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_75 = x_60;
} else {
 lean_dec_ref(x_60);
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
uint8_t x_82; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_16);
if (x_82 == 0)
{
return x_16;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_16, 0);
x_84 = lean_ctor_get(x_16, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_16);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1(x_1, x_2, x_3, x_4, x_6, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1___lam__1), 11, 4);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_array_size(x_13);
x_28 = 0;
x_29 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__4(x_24, x_25, x_13, x_27, x_28, x_26, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_30);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
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
}
static lean_object* _init_l_Lean_MVarId_casesRec___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = l_Lean_MVarId_casesRec___lam__0___closed__0;
x_12 = l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1(x_1, x_11, x_2, x_10, x_9, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_23);
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_2, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__1), 7, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_saturate(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1_spec__2(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__4(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1___lam__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_casesAnd___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_dec(x_1);
x_7 = x_23;
goto block_22;
block_22:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_7, x_3, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_MVarId_casesAnd___lam__0___closed__1;
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Expr_isAppOfArity(x_10, x_11, x_12);
lean_dec(x_10);
x_14 = lean_box(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = l_Lean_MVarId_casesAnd___lam__0___closed__1;
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Expr_isAppOfArity(x_15, x_17, x_18);
lean_dec(x_15);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected number of goals", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_casesAnd___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_casesAnd___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_MVarId_casesAnd___lam__0___boxed), 6, 0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_MVarId_casesRec(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_MVarId_casesAnd___closed__2;
x_12 = l_Lean_Meta_exactlyOne(x_9, x_11, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_casesAnd___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_24; 
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
lean_dec(x_1);
x_7 = x_24;
goto block_23;
block_23:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_7, x_3, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_isEq(x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_isHEq(x_10);
lean_dec(x_10);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = lean_box(x_11);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = l_Lean_Expr_isEq(x_15);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_Expr_isHEq(x_15);
lean_dec(x_15);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_21 = lean_box(x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_MVarId_substEqs___lam__0___boxed), 6, 0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_MVarId_casesRec(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_MVarId_casesAnd___closed__2;
x_12 = l_Lean_Meta_ensureAtMostOne(x_9, x_11, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_substEqs___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'byCases' tactic failed, unexpected new hypothesis", 50, 50);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_get_size(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_1);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_fget(x_19, x_23);
lean_dec(x_19);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
else
{
lean_dec(x_24);
lean_dec(x_18);
lean_free_object(x_1);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
goto block_14;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_get_size(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
goto block_14;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_fget(x_29, x_33);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_6);
return x_37;
}
else
{
lean_dec(x_34);
lean_dec(x_28);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
goto block_14;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1;
x_13 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hByCases", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_byCases___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'byCases' tactic failed, unexpected number of subgoals", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_byCases___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_MVarId_byCases___closed__1;
lean_inc(x_2);
x_10 = l_Lean_mkNot(x_2);
lean_inc(x_2);
x_11 = l_Lean_mkOr(x_2, x_10);
x_12 = l_Lean_mkEM(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_MVarId_assert(x_1, x_9, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Meta_intro1Core(x_14, x_17, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_unbox(x_16);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_MVarId_byCases___closed__2;
lean_inc(x_26);
x_30 = lean_array_push(x_29, x_26);
x_31 = lean_array_push(x_30, x_26);
x_32 = lean_unbox(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Lean_Meta_Cases_cases(x_23, x_22, x_31, x_32, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_array_get_size(x_34);
x_37 = lean_nat_dec_eq(x_36, x_28);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
lean_free_object(x_19);
x_38 = l_Lean_MVarId_byCases___closed__4;
x_39 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_38, x_4, x_5, x_6, x_7, x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_array_fget(x_34, x_40);
x_42 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_41, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_array_fget(x_34, x_45);
lean_dec(x_34);
x_47 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_46, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_ctor_set(x_19, 1, x_49);
lean_ctor_set(x_19, 0, x_43);
lean_ctor_set(x_47, 0, x_19);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_47);
lean_ctor_set(x_19, 1, x_50);
lean_ctor_set(x_19, 0, x_43);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_19);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_43);
lean_free_object(x_19);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
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
lean_dec(x_34);
lean_free_object(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
return x_42;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_42, 0);
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_42);
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
lean_free_object(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_33);
if (x_61 == 0)
{
return x_33;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_33, 0);
x_63 = lean_ctor_get(x_33, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_33);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_65 = lean_ctor_get(x_19, 0);
x_66 = lean_ctor_get(x_19, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_19);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_3);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_unbox(x_16);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_70);
x_71 = lean_unsigned_to_nat(2u);
x_72 = l_Lean_MVarId_byCases___closed__2;
lean_inc(x_69);
x_73 = lean_array_push(x_72, x_69);
x_74 = lean_array_push(x_73, x_69);
x_75 = lean_unbox(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_76 = l_Lean_Meta_Cases_cases(x_66, x_65, x_74, x_75, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_array_get_size(x_77);
x_80 = lean_nat_dec_eq(x_79, x_71);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
x_81 = l_Lean_MVarId_byCases___closed__4;
x_82 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_81, x_4, x_5, x_6, x_7, x_78);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_array_fget(x_77, x_83);
x_85 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_84, x_4, x_5, x_6, x_7, x_78);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_array_fget(x_77, x_88);
lean_dec(x_77);
x_90 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_89, x_4, x_5, x_6, x_7, x_87);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
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
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_86);
lean_ctor_set(x_94, 1, x_91);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_86);
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
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
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_77);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_100 = lean_ctor_get(x_85, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_85, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_102 = x_85;
} else {
 lean_dec_ref(x_85);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_104 = lean_ctor_get(x_76, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_76, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_106 = x_76;
} else {
 lean_dec_ref(x_76);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_108 = !lean_is_exclusive(x_18);
if (x_108 == 0)
{
return x_18;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_18, 0);
x_110 = lean_ctor_get(x_18, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_18);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_13);
if (x_112 == 0)
{
return x_13;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_13, 0);
x_114 = lean_ctor_get(x_13, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_13);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_byCasesDec___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_byCasesDec___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'byCasesDec' tactic failed, unexpected number of subgoals", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_byCasesDec___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_MVarId_byCases___closed__1;
x_11 = l_Lean_MVarId_byCasesDec___closed__2;
x_12 = l_Lean_Expr_app___override(x_11, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_MVarId_assert(x_1, x_10, x_12, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Meta_intro1Core(x_14, x_17, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_unbox(x_16);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_MVarId_byCases___closed__2;
lean_inc(x_26);
x_30 = lean_array_push(x_29, x_26);
x_31 = lean_array_push(x_30, x_26);
x_32 = lean_unbox(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Meta_Cases_cases(x_23, x_22, x_31, x_32, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_array_get_size(x_34);
x_37 = lean_nat_dec_eq(x_36, x_28);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
lean_free_object(x_19);
x_38 = l_Lean_MVarId_byCasesDec___closed__4;
x_39 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_38, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_array_fget(x_34, x_40);
x_42 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_41, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_fget(x_34, x_45);
lean_dec(x_34);
x_47 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_46, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_ctor_set(x_19, 1, x_49);
lean_ctor_set(x_19, 0, x_43);
lean_ctor_set(x_47, 0, x_19);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_47);
lean_ctor_set(x_19, 1, x_50);
lean_ctor_set(x_19, 0, x_43);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_19);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_43);
lean_free_object(x_19);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
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
lean_dec(x_34);
lean_free_object(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
return x_42;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_42, 0);
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_42);
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
lean_free_object(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_61 = !lean_is_exclusive(x_33);
if (x_61 == 0)
{
return x_33;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_33, 0);
x_63 = lean_ctor_get(x_33, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_33);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_65 = lean_ctor_get(x_19, 0);
x_66 = lean_ctor_get(x_19, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_19);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_unbox(x_16);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_70);
x_71 = lean_unsigned_to_nat(2u);
x_72 = l_Lean_MVarId_byCases___closed__2;
lean_inc(x_69);
x_73 = lean_array_push(x_72, x_69);
x_74 = lean_array_push(x_73, x_69);
x_75 = lean_unbox(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_76 = l_Lean_Meta_Cases_cases(x_66, x_65, x_74, x_75, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_array_get_size(x_77);
x_80 = lean_nat_dec_eq(x_79, x_71);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
x_81 = l_Lean_MVarId_byCasesDec___closed__4;
x_82 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_81, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_array_fget(x_77, x_83);
x_85 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_84, x_5, x_6, x_7, x_8, x_78);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_array_fget(x_77, x_88);
lean_dec(x_77);
x_90 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_89, x_5, x_6, x_7, x_8, x_87);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
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
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_86);
lean_ctor_set(x_94, 1, x_91);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_86);
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
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
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_77);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_100 = lean_ctor_get(x_85, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_85, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_102 = x_85;
} else {
 lean_dec_ref(x_85);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_104 = lean_ctor_get(x_76, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_76, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_106 = x_76;
} else {
 lean_dec_ref(x_76);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
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
x_108 = !lean_is_exclusive(x_18);
if (x_108 == 0)
{
return x_18;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_18, 0);
x_110 = lean_ctor_get(x_18, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_18);
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
x_112 = !lean_is_exclusive(x_13);
if (x_112 == 0)
{
return x_13;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_13, 0);
x_114 = lean_ctor_get(x_13, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_13);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Cases_cases___closed__0;
x_2 = l_Lean_Meta_Cases_cases___lam__0___closed__5;
x_3 = l_Lean_Meta_Cases_cases___lam__0___closed__4;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cases_cases___lam__0___closed__4;
x_2 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_2 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_2 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_2 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cases_cases___lam__0___closed__4;
x_2 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cases_cases___lam__0___closed__5;
x_2 = l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cases", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_2 = l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_2 = l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Cases___hyg_3955_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3955u);
x_2 = l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3955_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_3 = lean_box(0);
x_4 = l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Cases___hyg_3955_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Induction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Acyclic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Induction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Injection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Acyclic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_UnifyEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__2);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__3);
l_Lean_Meta_getInductiveUniverseAndParams___closed__0 = _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0();
lean_mark_persistent(l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6);
l_Lean_Meta_withNewEqs_loop___redArg___closed__0 = _init_l_Lean_Meta_withNewEqs_loop___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_withNewEqs_loop___redArg___closed__0);
l_Lean_Meta_withNewEqs_loop___redArg___closed__1 = _init_l_Lean_Meta_withNewEqs_loop___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_withNewEqs_loop___redArg___closed__1);
l_Lean_Meta_withNewEqs___redArg___closed__0 = _init_l_Lean_Meta_withNewEqs___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_withNewEqs___redArg___closed__0);
l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0 = _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0);
l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1 = _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1);
l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2 = _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2);
l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3 = _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3);
l_Lean_Meta_generalizeTargetsEq___closed__0 = _init_l_Lean_Meta_generalizeTargetsEq___closed__0();
lean_mark_persistent(l_Lean_Meta_generalizeTargetsEq___closed__0);
l_Lean_Meta_generalizeTargetsEq___closed__1 = _init_l_Lean_Meta_generalizeTargetsEq___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeTargetsEq___closed__1);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__0___closed__0 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__0___closed__0();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__0___closed__0);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__0 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__0();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__0);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__1 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__1);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__2 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__2);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__3 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__3);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__4 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__4);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__5 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__5);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__6 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__6);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__7 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__7);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__8 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__8);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__9 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__9();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__9);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__10 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__10();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__10);
l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__11 = _init_l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__11();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___Lean_Meta_generalizeIndices_x27_spec__0___closed__11);
l_Lean_Meta_generalizeIndices_x27___lam__0___closed__0 = _init_l_Lean_Meta_generalizeIndices_x27___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_generalizeIndices_x27___lam__0___closed__0);
l_Lean_Meta_generalizeIndices_x27___lam__0___closed__1 = _init_l_Lean_Meta_generalizeIndices_x27___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeIndices_x27___lam__0___closed__1);
l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0 = _init_l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0);
l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__0 = _init_l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__0();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__0);
l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__1 = _init_l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__1();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__1);
l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__2 = _init_l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__2();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__2);
l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__3 = _init_l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__3();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__3);
l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__4 = _init_l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__4();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_spec__5_spec__6___redArg___closed__4);
l_Lean_Meta_Cases_unifyEqs_x3f___closed__0 = _init_l_Lean_Meta_Cases_unifyEqs_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___closed__0 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___closed__0);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3);
l_Lean_Meta_Cases_cases___lam__0___closed__0 = _init_l_Lean_Meta_Cases_cases___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lam__0___closed__0);
l_Lean_Meta_Cases_cases___lam__0___closed__1 = _init_l_Lean_Meta_Cases_cases___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lam__0___closed__1);
l_Lean_Meta_Cases_cases___lam__0___closed__2 = _init_l_Lean_Meta_Cases_cases___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lam__0___closed__2);
l_Lean_Meta_Cases_cases___lam__0___closed__3 = _init_l_Lean_Meta_Cases_cases___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lam__0___closed__3);
l_Lean_Meta_Cases_cases___lam__0___closed__4 = _init_l_Lean_Meta_Cases_cases___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lam__0___closed__4);
l_Lean_Meta_Cases_cases___lam__0___closed__5 = _init_l_Lean_Meta_Cases_cases___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lam__0___closed__5);
l_Lean_Meta_Cases_cases___lam__0___closed__6 = _init_l_Lean_Meta_Cases_cases___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lam__0___closed__6);
l_Lean_Meta_Cases_cases___lam__0___closed__7 = _init_l_Lean_Meta_Cases_cases___lam__0___closed__7();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lam__0___closed__7);
l_Lean_Meta_Cases_cases___closed__0 = _init_l_Lean_Meta_Cases_cases___closed__0();
lean_mark_persistent(l_Lean_Meta_Cases_cases___closed__0);
l_Lean_Meta_Cases_cases___closed__1 = _init_l_Lean_Meta_Cases_cases___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_cases___closed__1);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1___closed__0 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1___closed__0();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_casesRec_spec__1_spec__1___lam__1___closed__0);
l_Lean_MVarId_casesRec___lam__0___closed__0 = _init_l_Lean_MVarId_casesRec___lam__0___closed__0();
lean_mark_persistent(l_Lean_MVarId_casesRec___lam__0___closed__0);
l_Lean_MVarId_casesAnd___lam__0___closed__0 = _init_l_Lean_MVarId_casesAnd___lam__0___closed__0();
lean_mark_persistent(l_Lean_MVarId_casesAnd___lam__0___closed__0);
l_Lean_MVarId_casesAnd___lam__0___closed__1 = _init_l_Lean_MVarId_casesAnd___lam__0___closed__1();
lean_mark_persistent(l_Lean_MVarId_casesAnd___lam__0___closed__1);
l_Lean_MVarId_casesAnd___closed__0 = _init_l_Lean_MVarId_casesAnd___closed__0();
lean_mark_persistent(l_Lean_MVarId_casesAnd___closed__0);
l_Lean_MVarId_casesAnd___closed__1 = _init_l_Lean_MVarId_casesAnd___closed__1();
lean_mark_persistent(l_Lean_MVarId_casesAnd___closed__1);
l_Lean_MVarId_casesAnd___closed__2 = _init_l_Lean_MVarId_casesAnd___closed__2();
lean_mark_persistent(l_Lean_MVarId_casesAnd___closed__2);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1);
l_Lean_MVarId_byCases___closed__0 = _init_l_Lean_MVarId_byCases___closed__0();
lean_mark_persistent(l_Lean_MVarId_byCases___closed__0);
l_Lean_MVarId_byCases___closed__1 = _init_l_Lean_MVarId_byCases___closed__1();
lean_mark_persistent(l_Lean_MVarId_byCases___closed__1);
l_Lean_MVarId_byCases___closed__2 = _init_l_Lean_MVarId_byCases___closed__2();
lean_mark_persistent(l_Lean_MVarId_byCases___closed__2);
l_Lean_MVarId_byCases___closed__3 = _init_l_Lean_MVarId_byCases___closed__3();
lean_mark_persistent(l_Lean_MVarId_byCases___closed__3);
l_Lean_MVarId_byCases___closed__4 = _init_l_Lean_MVarId_byCases___closed__4();
lean_mark_persistent(l_Lean_MVarId_byCases___closed__4);
l_Lean_MVarId_byCasesDec___closed__0 = _init_l_Lean_MVarId_byCasesDec___closed__0();
lean_mark_persistent(l_Lean_MVarId_byCasesDec___closed__0);
l_Lean_MVarId_byCasesDec___closed__1 = _init_l_Lean_MVarId_byCasesDec___closed__1();
lean_mark_persistent(l_Lean_MVarId_byCasesDec___closed__1);
l_Lean_MVarId_byCasesDec___closed__2 = _init_l_Lean_MVarId_byCasesDec___closed__2();
lean_mark_persistent(l_Lean_MVarId_byCasesDec___closed__2);
l_Lean_MVarId_byCasesDec___closed__3 = _init_l_Lean_MVarId_byCasesDec___closed__3();
lean_mark_persistent(l_Lean_MVarId_byCasesDec___closed__3);
l_Lean_MVarId_byCasesDec___closed__4 = _init_l_Lean_MVarId_byCasesDec___closed__4();
lean_mark_persistent(l_Lean_MVarId_byCasesDec___closed__4);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Cases___hyg_3955_ = _init_l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Cases___hyg_3955_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Cases___hyg_3955_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3955_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq
// Imports: Init.Grind.Ring.Poly Lean.Meta.Tactic.Grind.Arith.CommRing.Reify Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr Lean.Meta.Tactic.Grind.Arith.Linear.Var Lean.Meta.Tactic.Grind.Arith.Linear.StructId Lean.Meta.Tactic.Grind.Arith.Linear.Reify Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr Lean.Meta.Tactic.Grind.Arith.Linear.Proof
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__0;
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1;
lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2;
lean_object* l_Lean_Level_succ___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1;
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__0;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_process_linarith_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_process_linarith_diseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0;
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2;
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_958_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_mkIntLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr;
static lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4;
lean_object* l_Lean_Grind_Linarith_Poly_coeff(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__4;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4;
lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_toIntModuleExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___closed__1;
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0;
lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__2;
lean_object* lean_int_neg(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__3;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object**);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_20_(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 12);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_1, x_9, x_11);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0;
x_14 = lean_int_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_30; uint8_t x_31; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 30);
lean_inc_ref(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_16, 23);
lean_inc_ref(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_20, 2);
x_25 = l_Lean_mkIntLit(x_1);
x_30 = l_Lean_instInhabitedExpr;
x_31 = lean_nat_dec_lt(x_2, x_24);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec_ref(x_20);
x_32 = l_outOfBounds___redArg(x_30);
x_26 = x_32;
goto block_29;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_PersistentArray_get_x21___redArg(x_30, x_20, x_2);
x_26 = x_33;
goto block_29;
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_mkAppB(x_23, x_25, x_26);
if (lean_is_scalar(x_22)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_22;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
uint8_t x_34; 
lean_dec(x_16);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
return x_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_18);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
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
x_42 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 30);
lean_inc_ref(x_44);
lean_dec(x_43);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_42, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_44, 2);
x_48 = l_Lean_instInhabitedExpr;
x_49 = lean_nat_dec_lt(x_2, x_47);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec_ref(x_44);
x_50 = l_outOfBounds___redArg(x_48);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
else
{
lean_object* x_51; 
x_51 = l_Lean_PersistentArray_get_x21___redArg(x_48, x_44, x_2);
lean_ctor_set(x_42, 0, x_51);
return x_42;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_dec(x_42);
x_53 = lean_ctor_get(x_44, 2);
x_54 = l_Lean_instInhabitedExpr;
x_55 = lean_nat_dec_lt(x_2, x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_44);
x_56 = l_outOfBounds___redArg(x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_PersistentArray_get_x21___redArg(x_54, x_44, x_2);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_42);
if (x_60 == 0)
{
return x_42;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_42, 0);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_42);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_18, 22);
lean_inc_ref(x_23);
lean_dec(x_18);
x_24 = l_Lean_mkAppB(x_23, x_2, x_21);
x_1 = x_16;
x_2 = x_24;
x_12 = x_22;
goto _start;
}
else
{
lean_dec(x_18);
lean_dec_ref(x_2);
return x_20;
}
}
else
{
uint8_t x_26; 
lean_dec_ref(x_2);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 17);
lean_inc_ref(x_15);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_ctor_get(x_16, 17);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(x_24, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2(x_26, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
return x_30;
}
else
{
return x_27;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__1;
x_19 = l_Lean_Level_succ___override(x_17);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Expr_const___override(x_18, x_21);
x_23 = l_Lean_mkApp3(x_22, x_16, x_1, x_2);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_24, 3);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__1;
x_29 = l_Lean_Level_succ___override(x_27);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Expr_const___override(x_28, x_31);
x_33 = l_Lean_mkApp3(x_32, x_26, x_1, x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_ctor_get(x_17, 18);
lean_inc_ref(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4(x_14, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_14);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc_ref(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc_ref(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_3, x_27);
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
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc_ref(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
static double _init_l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6_spec__6(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc_ref(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 4);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; double x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__0;
x_23 = 0;
x_24 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__1;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__2;
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_8);
x_28 = l_Lean_PersistentArray_push___redArg(x_21, x_12);
lean_ctor_set(x_14, 0, x_28);
x_29 = lean_st_ref_set(x_6, x_13, x_16);
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
else
{
uint64_t x_36; lean_object* x_37; double x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__0;
x_39 = 0;
x_40 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__1;
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_39);
x_42 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__2;
x_43 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_10);
lean_ctor_set(x_43, 2, x_42);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_43);
lean_ctor_set(x_12, 0, x_8);
x_44 = l_Lean_PersistentArray_push___redArg(x_37, x_12);
x_45 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint64(x_45, sizeof(void*)*1, x_36);
lean_ctor_set(x_13, 4, x_45);
x_46 = lean_st_ref_set(x_6, x_13, x_16);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; double x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
x_53 = lean_ctor_get(x_13, 2);
x_54 = lean_ctor_get(x_13, 3);
x_55 = lean_ctor_get(x_13, 5);
x_56 = lean_ctor_get(x_13, 6);
x_57 = lean_ctor_get(x_13, 7);
x_58 = lean_ctor_get(x_13, 8);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_59 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_60 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_61 = x_14;
} else {
 lean_dec_ref(x_14);
 x_61 = lean_box(0);
}
x_62 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__0;
x_63 = 0;
x_64 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__1;
x_65 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_float(x_65, sizeof(void*)*2, x_62);
lean_ctor_set_float(x_65, sizeof(void*)*2 + 8, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 16, x_63);
x_66 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__2;
x_67 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_10);
lean_ctor_set(x_67, 2, x_66);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_67);
lean_ctor_set(x_12, 0, x_8);
x_68 = l_Lean_PersistentArray_push___redArg(x_60, x_12);
if (lean_is_scalar(x_61)) {
 x_69 = lean_alloc_ctor(0, 1, 8);
} else {
 x_69 = x_61;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_uint64(x_69, sizeof(void*)*1, x_59);
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_52);
lean_ctor_set(x_70, 2, x_53);
lean_ctor_set(x_70, 3, x_54);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_55);
lean_ctor_set(x_70, 6, x_56);
lean_ctor_set(x_70, 7, x_57);
lean_ctor_set(x_70, 8, x_58);
x_71 = lean_st_ref_set(x_6, x_70, x_16);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; double x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_dec(x_12);
x_77 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_13, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_13, 3);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_13, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_13, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_13, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_13, 8);
lean_inc_ref(x_84);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 lean_ctor_release(x_13, 6);
 lean_ctor_release(x_13, 7);
 lean_ctor_release(x_13, 8);
 x_85 = x_13;
} else {
 lean_dec_ref(x_13);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_87 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_88 = x_14;
} else {
 lean_dec_ref(x_14);
 x_88 = lean_box(0);
}
x_89 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__0;
x_90 = 0;
x_91 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__1;
x_92 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_float(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_float(x_92, sizeof(void*)*2 + 8, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 16, x_90);
x_93 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__2;
x_94 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_10);
lean_ctor_set(x_94, 2, x_93);
lean_inc(x_8);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_8);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_PersistentArray_push___redArg(x_87, x_95);
if (lean_is_scalar(x_88)) {
 x_97 = lean_alloc_ctor(0, 1, 8);
} else {
 x_97 = x_88;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set_uint64(x_97, sizeof(void*)*1, x_86);
if (lean_is_scalar(x_85)) {
 x_98 = lean_alloc_ctor(0, 9, 0);
} else {
 x_98 = x_85;
}
lean_ctor_set(x_98, 0, x_77);
lean_ctor_set(x_98, 1, x_78);
lean_ctor_set(x_98, 2, x_79);
lean_ctor_set(x_98, 3, x_80);
lean_ctor_set(x_98, 4, x_97);
lean_ctor_set(x_98, 5, x_81);
lean_ctor_set(x_98, 6, x_82);
lean_ctor_set(x_98, 7, x_83);
lean_ctor_set(x_98, 8, x_84);
x_99 = lean_st_ref_set(x_6, x_98, x_76);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linarith", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Grind_Linarith_Poly_findVarToSubst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_1);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_46; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_21 = x_13;
} else {
 lean_dec_ref(x_13);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec_ref(x_12);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_25 = x_20;
} else {
 lean_dec_ref(x_20);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_28 = x_22;
} else {
 lean_dec_ref(x_22);
 x_28 = lean_box(0);
}
x_29 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_30 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_29, x_9, x_23);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_27, 0);
x_35 = l_Lean_Grind_Linarith_Poly_coeff(x_34, x_26);
lean_inc(x_1);
x_36 = l_Lean_Grind_Linarith_Poly_mul(x_1, x_35);
x_37 = lean_int_neg(x_24);
lean_inc(x_34);
x_38 = l_Lean_Grind_Linarith_Poly_mul(x_34, x_37);
lean_dec(x_37);
x_39 = l_Lean_Grind_Linarith_Poly_combine(x_36, x_38);
x_46 = lean_unbox(x_31);
lean_dec(x_31);
if (x_46 == 0)
{
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_1);
x_40 = x_32;
goto block_45;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_1);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_75; lean_object* x_76; lean_object* x_99; uint8_t x_100; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_60 = l_Lean_MessageData_ofExpr(x_48);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_61);
lean_ctor_set(x_75, 1, x_62);
x_99 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
x_100 = lean_int_dec_lt(x_24, x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_nat_abs(x_24);
lean_dec(x_24);
x_102 = l_Nat_reprFast(x_101);
x_76 = x_102;
goto block_98;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_nat_abs(x_24);
lean_dec(x_24);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_sub(x_103, x_104);
lean_dec(x_103);
x_106 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
x_107 = lean_nat_add(x_105, x_104);
lean_dec(x_105);
x_108 = l_Nat_reprFast(x_107);
x_109 = lean_string_append(x_106, x_108);
lean_dec_ref(x_108);
x_76 = x_109;
goto block_98;
}
block_74:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Lean_MessageData_ofFormat(x_65);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
x_69 = l_Lean_MessageData_ofExpr(x_57);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_59);
x_72 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_29, x_71, x_7, x_8, x_9, x_10, x_58);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec_ref(x_72);
x_40 = x_73;
goto block_45;
}
block_98:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l_Lean_MessageData_ofFormat(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_62);
x_81 = l_Lean_MessageData_ofExpr(x_51);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_62);
x_84 = l_Lean_MessageData_ofExpr(x_54);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_62);
x_87 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
x_88 = lean_int_dec_lt(x_35, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_nat_abs(x_35);
lean_dec(x_35);
x_90 = l_Nat_reprFast(x_89);
x_63 = x_86;
x_64 = x_90;
goto block_74;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_nat_abs(x_35);
lean_dec(x_35);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_sub(x_91, x_92);
lean_dec(x_91);
x_94 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
x_95 = lean_nat_add(x_93, x_92);
lean_dec(x_93);
x_96 = l_Nat_reprFast(x_95);
x_97 = lean_string_append(x_94, x_96);
lean_dec_ref(x_96);
x_63 = x_86;
x_64 = x_97;
goto block_74;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_110 = !lean_is_exclusive(x_56);
if (x_110 == 0)
{
return x_56;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_56, 0);
x_112 = lean_ctor_get(x_56, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_56);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_114 = !lean_is_exclusive(x_53);
if (x_114 == 0)
{
return x_53;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_53, 0);
x_116 = lean_ctor_get(x_53, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_53);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_48);
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_118 = !lean_is_exclusive(x_50);
if (x_118 == 0)
{
return x_50;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_50, 0);
x_120 = lean_ctor_get(x_50, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_50);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_122 = !lean_is_exclusive(x_47);
if (x_122 == 0)
{
return x_47;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_47, 0);
x_124 = lean_ctor_get(x_47, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_47);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
block_45:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
if (lean_is_scalar(x_28)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_28;
}
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_39);
if (lean_is_scalar(x_25)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_25;
}
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_41);
if (lean_is_scalar(x_21)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_21;
}
lean_ctor_set(x_43, 0, x_42);
if (lean_is_scalar(x_33)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_33;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_12);
if (x_126 == 0)
{
return x_12;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_12, 0);
x_128 = lean_ctor_get(x_12, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_12);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6_spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_ctor_get(x_17, 18);
lean_inc_ref(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4(x_14, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_mkNot(x_22);
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
x_26 = l_Lean_mkNot(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
return x_20;
}
}
else
{
uint8_t x_28; 
lean_dec(x_14);
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
else
{
return x_13;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0;
x_72 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_71, x_13, x_15);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec_ref(x_72);
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = x_75;
goto block_70;
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_72, 1);
x_78 = lean_ctor_get(x_72, 0);
lean_dec(x_78);
x_79 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec_ref(x_82);
x_85 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_89 = l_Lean_MessageData_ofExpr(x_80);
lean_ctor_set_tag(x_72, 7);
lean_ctor_set(x_72, 1, x_89);
lean_ctor_set(x_72, 0, x_88);
x_90 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_72);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_MessageData_ofExpr(x_83);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_90);
x_95 = l_Lean_MessageData_ofExpr(x_86);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_88);
x_98 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_71, x_97, x_11, x_12, x_13, x_14, x_87);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec_ref(x_98);
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = x_99;
goto block_70;
}
else
{
uint8_t x_100; 
lean_dec(x_83);
lean_dec(x_80);
lean_free_object(x_72);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_100 = !lean_is_exclusive(x_85);
if (x_100 == 0)
{
return x_85;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_85, 0);
x_102 = lean_ctor_get(x_85, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_85);
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
lean_dec(x_80);
lean_free_object(x_72);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_104 = !lean_is_exclusive(x_82);
if (x_104 == 0)
{
return x_82;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_82, 0);
x_106 = lean_ctor_get(x_82, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_82);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_free_object(x_72);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_108 = !lean_is_exclusive(x_79);
if (x_108 == 0)
{
return x_79;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_79, 0);
x_110 = lean_ctor_get(x_79, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_79);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_72, 1);
lean_inc(x_112);
lean_dec(x_72);
x_113 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec_ref(x_113);
x_116 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
x_119 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_123 = l_Lean_MessageData_ofExpr(x_114);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_MessageData_ofExpr(x_117);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_125);
x_130 = l_Lean_MessageData_ofExpr(x_120);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_122);
x_133 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_71, x_132, x_11, x_12, x_13, x_14, x_121);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec_ref(x_133);
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = x_134;
goto block_70;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_117);
lean_dec(x_114);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_135 = lean_ctor_get(x_119, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_119, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_137 = x_119;
} else {
 lean_dec_ref(x_119);
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
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_114);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_139 = lean_ctor_get(x_116, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_116, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_141 = x_116;
} else {
 lean_dec_ref(x_116);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_143 = lean_ctor_get(x_113, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_113, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_145 = x_113;
} else {
 lean_dec_ref(x_113);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
block_70:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_int_emod(x_4, x_1);
x_29 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
x_30 = lean_int_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_31, 0);
lean_dec(x_41);
lean_inc(x_26);
x_42 = l_Lean_Grind_Linarith_Poly_mul(x_26, x_4);
x_43 = lean_int_neg(x_1);
lean_inc(x_27);
x_44 = l_Lean_Grind_Linarith_Poly_mul(x_27, x_43);
x_45 = l_Lean_Grind_Linarith_Poly_combine(x_42, x_44);
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_4);
lean_ctor_set(x_46, 2, x_3);
lean_ctor_set(x_46, 3, x_5);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
lean_inc(x_26);
x_50 = l_Lean_Grind_Linarith_Poly_mul(x_26, x_4);
x_51 = lean_int_neg(x_1);
lean_inc(x_27);
x_52 = l_Lean_Grind_Linarith_Poly_mul(x_27, x_51);
x_53 = l_Lean_Grind_Linarith_Poly_combine(x_50, x_52);
x_54 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_4);
lean_ctor_set(x_54, 2, x_3);
lean_ctor_set(x_54, 3, x_5);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_49);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_58 = !lean_is_exclusive(x_31);
if (x_58 == 0)
{
return x_31;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_31, 0);
x_60 = lean_ctor_get(x_31, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_31);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_int_neg(x_4);
lean_dec(x_4);
x_63 = lean_int_ediv(x_62, x_1);
lean_dec(x_62);
lean_inc(x_26);
x_64 = l_Lean_Grind_Linarith_Poly_mul(x_26, x_63);
lean_inc(x_27);
x_65 = l_Lean_Grind_Linarith_Poly_combine(x_64, x_27);
x_66 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_3);
lean_ctor_set(x_66, 2, x_5);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_25);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(x_2, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec_ref(x_6);
return x_9;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_nat_dec_eq(x_8, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_6);
x_15 = lean_box(0);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec_ref(x_10);
x_18 = lean_nat_dec_eq(x_8, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_6);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
}
else
{
lean_dec_ref(x_6);
return x_9;
}
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(x_1, x_2, x_3, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = 0;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_box(x_13);
lean_inc_ref(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 13, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec_ref(x_17);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec_ref(x_18);
x_27 = lean_box(x_13);
lean_inc_ref(x_2);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 13, 3);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_dec_ref(x_29);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec_ref(x_30);
x_39 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_143; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_143 = lean_nat_dec_le(x_40, x_43);
if (x_143 == 0)
{
lean_dec(x_43);
x_45 = x_40;
goto block_142;
}
else
{
lean_dec(x_40);
x_45 = x_43;
goto block_142;
}
block_142:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_38);
lean_inc(x_26);
x_46 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_46, 0, x_26);
lean_ctor_set(x_46, 1, x_38);
x_47 = l_Lean_Grind_CommRing_Expr_toPoly(x_46);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_45);
lean_inc_ref(x_47);
x_48 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_47, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_49, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_51, 0, x_55);
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_51);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_51, 1);
x_61 = lean_ctor_get(x_51, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_52, 0);
lean_inc(x_62);
lean_dec_ref(x_52);
lean_inc(x_62);
x_63 = l_Lean_Grind_Linarith_Expr_norm(x_62);
x_64 = lean_box(0);
x_65 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_958_(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_51);
lean_inc_ref(x_47);
lean_inc(x_38);
lean_inc(x_26);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_66 = lean_alloc_ctor(10, 6, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_2);
lean_ctor_set(x_66, 2, x_26);
lean_ctor_set(x_66, 3, x_38);
lean_ctor_set(x_66, 4, x_47);
lean_ctor_set(x_66, 5, x_62);
lean_inc(x_63);
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_68 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_60);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_71 = l_Lean_Grind_CommRing_Poly_mulConst(x_70, x_47);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_71);
x_72 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_71, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_75 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_73, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
lean_dec_ref(x_71);
lean_dec(x_63);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 0);
lean_dec(x_78);
x_79 = lean_box(0);
lean_ctor_set(x_75, 0, x_79);
return x_75;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_dec(x_75);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
lean_dec_ref(x_75);
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
lean_dec_ref(x_76);
x_85 = l_Lean_Grind_Linarith_Poly_mul(x_63, x_70);
x_86 = lean_alloc_ctor(10, 6, 0);
lean_ctor_set(x_86, 0, x_2);
lean_ctor_set(x_86, 1, x_1);
lean_ctor_set(x_86, 2, x_38);
lean_ctor_set(x_86, 3, x_26);
lean_ctor_set(x_86, 4, x_71);
lean_ctor_set(x_86, 5, x_84);
x_87 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_13);
x_88 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_87, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_83);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec_ref(x_71);
lean_dec(x_63);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_89 = !lean_is_exclusive(x_75);
if (x_89 == 0)
{
return x_75;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_75, 0);
x_91 = lean_ctor_get(x_75, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_75);
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
lean_dec_ref(x_71);
lean_dec(x_63);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_93 = !lean_is_exclusive(x_72);
if (x_93 == 0)
{
return x_72;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_72, 0);
x_95 = lean_ctor_get(x_72, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_72);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_dec(x_63);
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_68;
}
}
else
{
lean_object* x_97; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_97 = lean_box(0);
lean_ctor_set(x_51, 0, x_97);
return x_51;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = lean_ctor_get(x_51, 1);
lean_inc(x_98);
lean_dec(x_51);
x_99 = lean_ctor_get(x_52, 0);
lean_inc(x_99);
lean_dec_ref(x_52);
lean_inc(x_99);
x_100 = l_Lean_Grind_Linarith_Expr_norm(x_99);
x_101 = lean_box(0);
x_102 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_958_(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_inc_ref(x_47);
lean_inc(x_38);
lean_inc(x_26);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_103 = lean_alloc_ctor(10, 6, 0);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_2);
lean_ctor_set(x_103, 2, x_26);
lean_ctor_set(x_103, 3, x_38);
lean_ctor_set(x_103, 4, x_47);
lean_ctor_set(x_103, 5, x_99);
lean_inc(x_100);
x_104 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*2, x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_105 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_98);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_108 = l_Lean_Grind_CommRing_Poly_mulConst(x_107, x_47);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_108);
x_109 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_108, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_106);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec_ref(x_109);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_112 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_110, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_108);
lean_dec(x_100);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
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
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
lean_dec_ref(x_112);
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
lean_dec_ref(x_113);
x_120 = l_Lean_Grind_Linarith_Poly_mul(x_100, x_107);
x_121 = lean_alloc_ctor(10, 6, 0);
lean_ctor_set(x_121, 0, x_2);
lean_ctor_set(x_121, 1, x_1);
lean_ctor_set(x_121, 2, x_38);
lean_ctor_set(x_121, 3, x_26);
lean_ctor_set(x_121, 4, x_108);
lean_ctor_set(x_121, 5, x_119);
x_122 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*2, x_13);
x_123 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_122, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_118);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_108);
lean_dec(x_100);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_124 = lean_ctor_get(x_112, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_112, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_126 = x_112;
} else {
 lean_dec_ref(x_112);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec_ref(x_108);
lean_dec(x_100);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = lean_ctor_get(x_109, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_109, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_130 = x_109;
} else {
 lean_dec_ref(x_109);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_dec(x_100);
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_105;
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_98);
return x_133;
}
}
}
}
else
{
uint8_t x_134; 
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_134 = !lean_is_exclusive(x_51);
if (x_134 == 0)
{
return x_51;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_51, 0);
x_136 = lean_ctor_get(x_51, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_51);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_138 = !lean_is_exclusive(x_48);
if (x_138 == 0)
{
return x_48;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_48, 0);
x_140 = lean_ctor_get(x_48, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_48);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_144 = !lean_is_exclusive(x_42);
if (x_144 == 0)
{
return x_42;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_42, 0);
x_146 = lean_ctor_get(x_42, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_42);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_148 = !lean_is_exclusive(x_39);
if (x_148 == 0)
{
return x_39;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_39, 0);
x_150 = lean_ctor_get(x_39, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_39);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_152 = !lean_is_exclusive(x_29);
if (x_152 == 0)
{
return x_29;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_29, 0);
x_154 = lean_ctor_get(x_29, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_29);
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
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_156 = !lean_is_exclusive(x_17);
if (x_156 == 0)
{
return x_17;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_17, 0);
x_158 = lean_ctor_get(x_17, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_17);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_14 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec_ref(x_15);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_24 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_24, 1);
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec_ref(x_25);
lean_inc(x_35);
lean_inc(x_23);
x_36 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Grind_Linarith_Expr_norm(x_36);
x_38 = lean_box(0);
x_39 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_958_(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_24);
lean_inc(x_35);
lean_inc(x_23);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_40 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_2);
lean_ctor_set(x_40, 2, x_23);
lean_ctor_set(x_40, 3, x_35);
lean_inc(x_37);
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_45 = l_Lean_Grind_Linarith_Poly_mul(x_37, x_44);
x_46 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_1);
lean_ctor_set(x_46, 2, x_35);
lean_ctor_set(x_46, 3, x_23);
x_47 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_13);
x_48 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_48;
}
else
{
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_42;
}
}
else
{
lean_object* x_49; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = lean_box(0);
lean_ctor_set(x_24, 0, x_49);
return x_24;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_dec(x_24);
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
lean_dec_ref(x_25);
lean_inc(x_51);
lean_inc(x_23);
x_52 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_52, 0, x_23);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Grind_Linarith_Expr_norm(x_52);
x_54 = lean_box(0);
x_55 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_958_(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_inc(x_51);
lean_inc(x_23);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_56 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_2);
lean_ctor_set(x_56, 2, x_23);
lean_ctor_set(x_56, 3, x_51);
lean_inc(x_53);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_58 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_61 = l_Lean_Grind_Linarith_Poly_mul(x_53, x_60);
x_62 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_62, 0, x_2);
lean_ctor_set(x_62, 1, x_1);
lean_ctor_set(x_62, 2, x_51);
lean_ctor_set(x_62, 3, x_23);
x_63 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_13);
x_64 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_59);
return x_64;
}
else
{
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_58;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_50);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_67 = !lean_is_exclusive(x_24);
if (x_67 == 0)
{
return x_24;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_24, 0);
x_69 = lean_ctor_get(x_24, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_24);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_14);
if (x_71 == 0)
{
return x_14;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_14, 0);
x_73 = lean_ctor_get(x_14, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_14);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
static lean_object* _init_l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0;
x_13 = l_ReaderT_instMonad___redArg(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 2);
x_20 = lean_ctor_get(x_15, 3);
x_21 = lean_ctor_get(x_15, 4);
x_22 = lean_ctor_get(x_15, 1);
lean_dec(x_22);
x_23 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__1;
x_24 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__2;
lean_inc_ref(x_18);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_25, 0, x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_28, 0, x_21);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_20);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_30, 0, x_19);
lean_ctor_set(x_15, 4, x_28);
lean_ctor_set(x_15, 3, x_29);
lean_ctor_set(x_15, 2, x_30);
lean_ctor_set(x_15, 1, x_23);
lean_ctor_set(x_15, 0, x_27);
lean_ctor_set(x_13, 1, x_24);
x_31 = l_ReaderT_instMonad___redArg(x_13);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 2);
x_38 = lean_ctor_get(x_33, 3);
x_39 = lean_ctor_get(x_33, 4);
x_40 = lean_ctor_get(x_33, 1);
lean_dec(x_40);
x_41 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__3;
x_42 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__4;
lean_inc_ref(x_36);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_43, 0, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_36);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_39);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_38);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_48, 0, x_37);
lean_ctor_set(x_33, 4, x_46);
lean_ctor_set(x_33, 3, x_47);
lean_ctor_set(x_33, 2, x_48);
lean_ctor_set(x_33, 1, x_41);
lean_ctor_set(x_33, 0, x_45);
lean_ctor_set(x_31, 1, x_42);
x_49 = l_ReaderT_instMonad___redArg(x_31);
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = l_ReaderT_instMonad___redArg(x_50);
x_52 = l_ReaderT_instMonad___redArg(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__5;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_instInhabitedOfMonad___redArg(x_52, x_55);
x_57 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = lean_panic_fn(x_57, x_1);
x_59 = lean_apply_10(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_60 = lean_ctor_get(x_33, 0);
x_61 = lean_ctor_get(x_33, 2);
x_62 = lean_ctor_get(x_33, 3);
x_63 = lean_ctor_get(x_33, 4);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_33);
x_64 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__3;
x_65 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__4;
lean_inc_ref(x_60);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_66, 0, x_60);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_67, 0, x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_69, 0, x_63);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_70, 0, x_62);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_71, 0, x_61);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_64);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_70);
lean_ctor_set(x_72, 4, x_69);
lean_ctor_set(x_31, 1, x_65);
lean_ctor_set(x_31, 0, x_72);
x_73 = l_ReaderT_instMonad___redArg(x_31);
x_74 = l_ReaderT_instMonad___redArg(x_73);
x_75 = l_ReaderT_instMonad___redArg(x_74);
x_76 = l_ReaderT_instMonad___redArg(x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__5;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_instInhabitedOfMonad___redArg(x_76, x_79);
x_81 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_81, 0, x_80);
x_82 = lean_panic_fn(x_81, x_1);
x_83 = lean_apply_10(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_84 = lean_ctor_get(x_31, 0);
lean_inc(x_84);
lean_dec(x_31);
x_85 = lean_ctor_get(x_84, 0);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_84, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_84, 4);
lean_inc(x_88);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 lean_ctor_release(x_84, 4);
 x_89 = x_84;
} else {
 lean_dec_ref(x_84);
 x_89 = lean_box(0);
}
x_90 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__3;
x_91 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__4;
lean_inc_ref(x_85);
x_92 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_92, 0, x_85);
x_93 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_93, 0, x_85);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_95, 0, x_88);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_96, 0, x_87);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_97, 0, x_86);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(0, 5, 0);
} else {
 x_98 = x_89;
}
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_90);
lean_ctor_set(x_98, 2, x_97);
lean_ctor_set(x_98, 3, x_96);
lean_ctor_set(x_98, 4, x_95);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_91);
x_100 = l_ReaderT_instMonad___redArg(x_99);
x_101 = l_ReaderT_instMonad___redArg(x_100);
x_102 = l_ReaderT_instMonad___redArg(x_101);
x_103 = l_ReaderT_instMonad___redArg(x_102);
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__5;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_instInhabitedOfMonad___redArg(x_103, x_106);
x_108 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_108, 0, x_107);
x_109 = lean_panic_fn(x_108, x_1);
x_110 = lean_apply_10(x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_111 = lean_ctor_get(x_15, 0);
x_112 = lean_ctor_get(x_15, 2);
x_113 = lean_ctor_get(x_15, 3);
x_114 = lean_ctor_get(x_15, 4);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_15);
x_115 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__1;
x_116 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__2;
lean_inc_ref(x_111);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_117, 0, x_111);
x_118 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_118, 0, x_111);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_120, 0, x_114);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_121, 0, x_113);
x_122 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_122, 0, x_112);
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_115);
lean_ctor_set(x_123, 2, x_122);
lean_ctor_set(x_123, 3, x_121);
lean_ctor_set(x_123, 4, x_120);
lean_ctor_set(x_13, 1, x_116);
lean_ctor_set(x_13, 0, x_123);
x_124 = l_ReaderT_instMonad___redArg(x_13);
x_125 = lean_ctor_get(x_124, 0);
lean_inc_ref(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_125, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_125, 4);
lean_inc(x_130);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__3;
x_133 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__4;
lean_inc_ref(x_127);
x_134 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_134, 0, x_127);
x_135 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_135, 0, x_127);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_137, 0, x_130);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_138, 0, x_129);
x_139 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_139, 0, x_128);
if (lean_is_scalar(x_131)) {
 x_140 = lean_alloc_ctor(0, 5, 0);
} else {
 x_140 = x_131;
}
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_132);
lean_ctor_set(x_140, 2, x_139);
lean_ctor_set(x_140, 3, x_138);
lean_ctor_set(x_140, 4, x_137);
if (lean_is_scalar(x_126)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_126;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_133);
x_142 = l_ReaderT_instMonad___redArg(x_141);
x_143 = l_ReaderT_instMonad___redArg(x_142);
x_144 = l_ReaderT_instMonad___redArg(x_143);
x_145 = l_ReaderT_instMonad___redArg(x_144);
x_146 = lean_unsigned_to_nat(0u);
x_147 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__5;
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_instInhabitedOfMonad___redArg(x_145, x_148);
x_150 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_150, 0, x_149);
x_151 = lean_panic_fn(x_150, x_1);
x_152 = lean_apply_10(x_151, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_153 = lean_ctor_get(x_13, 0);
lean_inc(x_153);
lean_dec(x_13);
x_154 = lean_ctor_get(x_153, 0);
lean_inc_ref(x_154);
x_155 = lean_ctor_get(x_153, 2);
lean_inc(x_155);
x_156 = lean_ctor_get(x_153, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 4);
lean_inc(x_157);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 lean_ctor_release(x_153, 3);
 lean_ctor_release(x_153, 4);
 x_158 = x_153;
} else {
 lean_dec_ref(x_153);
 x_158 = lean_box(0);
}
x_159 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__1;
x_160 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__2;
lean_inc_ref(x_154);
x_161 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_161, 0, x_154);
x_162 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_162, 0, x_154);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_164, 0, x_157);
x_165 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_165, 0, x_156);
x_166 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_166, 0, x_155);
if (lean_is_scalar(x_158)) {
 x_167 = lean_alloc_ctor(0, 5, 0);
} else {
 x_167 = x_158;
}
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_159);
lean_ctor_set(x_167, 2, x_166);
lean_ctor_set(x_167, 3, x_165);
lean_ctor_set(x_167, 4, x_164);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_160);
x_169 = l_ReaderT_instMonad___redArg(x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc_ref(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_170, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_170, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_170, 4);
lean_inc(x_175);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 x_176 = x_170;
} else {
 lean_dec_ref(x_170);
 x_176 = lean_box(0);
}
x_177 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__3;
x_178 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__4;
lean_inc_ref(x_172);
x_179 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_179, 0, x_172);
x_180 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_180, 0, x_172);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_182, 0, x_175);
x_183 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_183, 0, x_174);
x_184 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_184, 0, x_173);
if (lean_is_scalar(x_176)) {
 x_185 = lean_alloc_ctor(0, 5, 0);
} else {
 x_185 = x_176;
}
lean_ctor_set(x_185, 0, x_181);
lean_ctor_set(x_185, 1, x_177);
lean_ctor_set(x_185, 2, x_184);
lean_ctor_set(x_185, 3, x_183);
lean_ctor_set(x_185, 4, x_182);
if (lean_is_scalar(x_171)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_171;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_178);
x_187 = l_ReaderT_instMonad___redArg(x_186);
x_188 = l_ReaderT_instMonad___redArg(x_187);
x_189 = l_ReaderT_instMonad___redArg(x_188);
x_190 = l_ReaderT_instMonad___redArg(x_189);
x_191 = lean_unsigned_to_nat(0u);
x_192 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__5;
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_instInhabitedOfMonad___redArg(x_190, x_193);
x_195 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_195, 0, x_194);
x_196 = lean_panic_fn(x_195, x_1);
x_197 = lean_apply_10(x_196, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_197;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Linear.EqCnstr.norm", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2;
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_unsigned_to_nat(90u);
x_4 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1;
x_5 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; 
x_21 = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_65; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_65 = lean_unbox(x_22);
lean_dec(x_22);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_24 = x_1;
x_25 = x_66;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
goto block_64;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_1, 0);
x_68 = l_Lean_Grind_Linarith_Poly_gcdCoeffs(x_67);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_dec_eq(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_inc(x_68);
x_71 = lean_nat_to_int(x_68);
lean_inc(x_67);
x_72 = l_Lean_Grind_Linarith_Poly_div(x_67, x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_1);
lean_inc(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_24 = x_74;
x_25 = x_72;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
goto block_64;
}
else
{
lean_dec(x_68);
lean_inc(x_67);
x_24 = x_1;
x_25 = x_67;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
goto block_64;
}
}
block_64:
{
lean_object* x_35; 
lean_inc(x_25);
x_35 = l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_25);
lean_dec_ref(x_24);
x_36 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3;
x_37 = l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(x_36, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_23);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
x_44 = lean_int_dec_lt(x_41, x_43);
if (x_44 == 0)
{
lean_free_object(x_39);
lean_free_object(x_35);
lean_dec(x_25);
x_12 = x_41;
x_13 = x_42;
x_14 = x_24;
x_15 = x_23;
goto block_20;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_46 = l_Lean_Grind_Linarith_Poly_mul(x_25, x_45);
lean_ctor_set_tag(x_35, 2);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_46);
x_12 = x_41;
x_13 = x_42;
x_14 = x_39;
x_15 = x_23;
goto block_20;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
x_50 = lean_int_dec_lt(x_47, x_49);
if (x_50 == 0)
{
lean_free_object(x_35);
lean_dec(x_25);
x_12 = x_47;
x_13 = x_48;
x_14 = x_24;
x_15 = x_23;
goto block_20;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_52 = l_Lean_Grind_Linarith_Poly_mul(x_25, x_51);
lean_ctor_set_tag(x_35, 2);
lean_ctor_set(x_35, 0, x_24);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_35);
x_12 = x_47;
x_13 = x_48;
x_14 = x_53;
x_15 = x_23;
goto block_20;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_35, 0);
lean_inc(x_54);
lean_dec(x_35);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
x_59 = lean_int_dec_lt(x_55, x_58);
if (x_59 == 0)
{
lean_dec(x_57);
lean_dec(x_25);
x_12 = x_55;
x_13 = x_56;
x_14 = x_24;
x_15 = x_23;
goto block_20;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_61 = l_Lean_Grind_Linarith_Poly_mul(x_25, x_60);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_24);
if (lean_is_scalar(x_57)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_57;
}
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_12 = x_55;
x_13 = x_56;
x_14 = x_63;
x_15 = x_23;
goto block_20;
}
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_21);
if (x_75 == 0)
{
return x_21;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_21, 0);
x_77 = lean_ctor_get(x_21, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_21);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
block_20:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_nat_abs(x_12);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__6;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_2, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
x_15 = lean_ctor_get(x_9, 2);
x_16 = lean_ctor_get(x_9, 3);
x_17 = lean_ctor_get(x_9, 4);
x_18 = lean_ctor_get(x_9, 5);
x_19 = lean_ctor_get(x_9, 6);
x_20 = lean_ctor_get(x_9, 7);
x_21 = lean_ctor_get(x_9, 8);
x_22 = lean_ctor_get(x_9, 9);
x_23 = lean_ctor_get(x_9, 10);
x_24 = lean_ctor_get(x_9, 11);
x_25 = lean_ctor_get(x_9, 12);
x_26 = lean_nat_dec_eq(x_16, x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_16, x_28);
lean_dec(x_16);
lean_ctor_set(x_9, 3, x_29);
lean_inc(x_27);
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec_ref(x_9);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
lean_ctor_set(x_30, 0, x_1);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec_ref(x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec_ref(x_30);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_dec(x_41);
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
x_59 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_60 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_59, x_9, x_38);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_free_object(x_36);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec_ref(x_60);
x_45 = x_2;
x_46 = x_3;
x_47 = x_4;
x_48 = x_5;
x_49 = x_6;
x_50 = x_7;
x_51 = x_8;
x_52 = x_9;
x_53 = x_10;
x_54 = x_63;
goto block_58;
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 1);
x_66 = lean_ctor_get(x_60, 0);
lean_dec(x_66);
x_67 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec_ref(x_70);
x_73 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_77 = l_Lean_MessageData_ofExpr(x_68);
lean_ctor_set_tag(x_60, 7);
lean_ctor_set(x_60, 1, x_77);
lean_ctor_set(x_60, 0, x_76);
x_78 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_78);
lean_ctor_set(x_36, 0, x_60);
x_79 = l_Lean_MessageData_ofExpr(x_71);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_36);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
x_82 = l_Lean_MessageData_ofExpr(x_74);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
x_85 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_59, x_84, x_7, x_8, x_9, x_10, x_75);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec_ref(x_85);
x_45 = x_2;
x_46 = x_3;
x_47 = x_4;
x_48 = x_5;
x_49 = x_6;
x_50 = x_7;
x_51 = x_8;
x_52 = x_9;
x_53 = x_10;
x_54 = x_86;
goto block_58;
}
else
{
uint8_t x_87; 
lean_dec(x_71);
lean_dec(x_68);
lean_free_object(x_60);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_36);
lean_dec(x_40);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_87 = !lean_is_exclusive(x_73);
if (x_87 == 0)
{
return x_73;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_73, 0);
x_89 = lean_ctor_get(x_73, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_73);
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
lean_dec(x_68);
lean_free_object(x_60);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_36);
lean_dec(x_40);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_91 = !lean_is_exclusive(x_70);
if (x_91 == 0)
{
return x_70;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_70, 0);
x_93 = lean_ctor_get(x_70, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_70);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_free_object(x_60);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_36);
lean_dec(x_40);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_67);
if (x_95 == 0)
{
return x_67;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_67, 0);
x_97 = lean_ctor_get(x_67, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_67);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_60, 1);
lean_inc(x_99);
lean_dec(x_60);
x_100 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
x_103 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_109 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_110 = l_Lean_MessageData_ofExpr(x_101);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_112);
lean_ctor_set(x_36, 0, x_111);
x_113 = l_Lean_MessageData_ofExpr(x_104);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_36);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
x_116 = l_Lean_MessageData_ofExpr(x_107);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_109);
x_119 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_59, x_118, x_7, x_8, x_9, x_10, x_108);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec_ref(x_119);
x_45 = x_2;
x_46 = x_3;
x_47 = x_4;
x_48 = x_5;
x_49 = x_6;
x_50 = x_7;
x_51 = x_8;
x_52 = x_9;
x_53 = x_10;
x_54 = x_120;
goto block_58;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_36);
lean_dec(x_40);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_121 = lean_ctor_get(x_106, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_106, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_123 = x_106;
} else {
 lean_dec_ref(x_106);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_101);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_36);
lean_dec(x_40);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_125 = lean_ctor_get(x_103, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_103, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_127 = x_103;
} else {
 lean_dec_ref(x_103);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_36);
lean_dec(x_40);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_129 = lean_ctor_get(x_100, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_100, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_131 = x_100;
} else {
 lean_dec_ref(x_100);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
}
block_58:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_55, 0, x_40);
lean_ctor_set(x_55, 1, x_42);
lean_ctor_set(x_55, 2, x_1);
if (lean_is_scalar(x_44)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_44;
}
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_55);
x_1 = x_56;
x_2 = x_45;
x_3 = x_46;
x_4 = x_47;
x_5 = x_48;
x_6 = x_49;
x_7 = x_50;
x_8 = x_51;
x_9 = x_52;
x_10 = x_53;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_133 = lean_ctor_get(x_36, 0);
lean_inc(x_133);
lean_dec(x_36);
x_134 = lean_ctor_get(x_37, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_37, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_136 = x_37;
} else {
 lean_dec_ref(x_37);
 x_136 = lean_box(0);
}
x_151 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_152 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_151, x_9, x_38);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_unbox(x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec_ref(x_152);
x_137 = x_2;
x_138 = x_3;
x_139 = x_4;
x_140 = x_5;
x_141 = x_6;
x_142 = x_7;
x_143 = x_8;
x_144 = x_9;
x_145 = x_10;
x_146 = x_155;
goto block_150;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_157 = x_152;
} else {
 lean_dec_ref(x_152);
 x_157 = lean_box(0);
}
x_158 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_133, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_156);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec_ref(x_158);
x_161 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec_ref(x_161);
x_164 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_134, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec_ref(x_164);
x_167 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_168 = l_Lean_MessageData_ofExpr(x_159);
if (lean_is_scalar(x_157)) {
 x_169 = lean_alloc_ctor(7, 2, 0);
} else {
 x_169 = x_157;
 lean_ctor_set_tag(x_169, 7);
}
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_Lean_MessageData_ofExpr(x_162);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_170);
x_175 = l_Lean_MessageData_ofExpr(x_165);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_167);
x_178 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_151, x_177, x_7, x_8, x_9, x_10, x_166);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec_ref(x_178);
x_137 = x_2;
x_138 = x_3;
x_139 = x_4;
x_140 = x_5;
x_141 = x_6;
x_142 = x_7;
x_143 = x_8;
x_144 = x_9;
x_145 = x_10;
x_146 = x_179;
goto block_150;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_162);
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_180 = lean_ctor_get(x_164, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_164, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_182 = x_164;
} else {
 lean_dec_ref(x_164);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_184 = lean_ctor_get(x_161, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_161, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_186 = x_161;
} else {
 lean_dec_ref(x_161);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_157);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_188 = lean_ctor_get(x_158, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_158, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_190 = x_158;
} else {
 lean_dec_ref(x_158);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
block_150:
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_147, 0, x_133);
lean_ctor_set(x_147, 1, x_134);
lean_ctor_set(x_147, 2, x_1);
if (lean_is_scalar(x_136)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_136;
}
lean_ctor_set(x_148, 0, x_135);
lean_ctor_set(x_148, 1, x_147);
x_1 = x_148;
x_2 = x_137;
x_3 = x_138;
x_4 = x_139;
x_5 = x_140;
x_6 = x_141;
x_7 = x_142;
x_8 = x_143;
x_9 = x_144;
x_10 = x_145;
x_11 = x_146;
goto _start;
}
}
}
}
else
{
uint8_t x_192; 
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_192 = !lean_is_exclusive(x_30);
if (x_192 == 0)
{
return x_30;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_30, 0);
x_194 = lean_ctor_get(x_30, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_30);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; 
lean_free_object(x_9);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_1);
x_196 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_18, x_11);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; uint8_t x_212; 
x_197 = lean_ctor_get(x_9, 0);
x_198 = lean_ctor_get(x_9, 1);
x_199 = lean_ctor_get(x_9, 2);
x_200 = lean_ctor_get(x_9, 3);
x_201 = lean_ctor_get(x_9, 4);
x_202 = lean_ctor_get(x_9, 5);
x_203 = lean_ctor_get(x_9, 6);
x_204 = lean_ctor_get(x_9, 7);
x_205 = lean_ctor_get(x_9, 8);
x_206 = lean_ctor_get(x_9, 9);
x_207 = lean_ctor_get(x_9, 10);
x_208 = lean_ctor_get_uint8(x_9, sizeof(void*)*13);
x_209 = lean_ctor_get(x_9, 11);
x_210 = lean_ctor_get_uint8(x_9, sizeof(void*)*13 + 1);
x_211 = lean_ctor_get(x_9, 12);
lean_inc(x_211);
lean_inc(x_209);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_9);
x_212 = lean_nat_dec_eq(x_200, x_201);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_213 = lean_ctor_get(x_1, 0);
x_214 = lean_unsigned_to_nat(1u);
x_215 = lean_nat_add(x_200, x_214);
lean_dec(x_200);
x_216 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_216, 0, x_197);
lean_ctor_set(x_216, 1, x_198);
lean_ctor_set(x_216, 2, x_199);
lean_ctor_set(x_216, 3, x_215);
lean_ctor_set(x_216, 4, x_201);
lean_ctor_set(x_216, 5, x_202);
lean_ctor_set(x_216, 6, x_203);
lean_ctor_set(x_216, 7, x_204);
lean_ctor_set(x_216, 8, x_205);
lean_ctor_set(x_216, 9, x_206);
lean_ctor_set(x_216, 10, x_207);
lean_ctor_set(x_216, 11, x_209);
lean_ctor_set(x_216, 12, x_211);
lean_ctor_set_uint8(x_216, sizeof(void*)*13, x_208);
lean_ctor_set_uint8(x_216, sizeof(void*)*13 + 1, x_210);
lean_inc(x_213);
x_217 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(x_213, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_216, x_10, x_11);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec_ref(x_216);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_220 = x_217;
} else {
 lean_dec_ref(x_217);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_1);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_222 = lean_ctor_get(x_218, 0);
lean_inc(x_222);
lean_dec_ref(x_218);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_217, 1);
lean_inc(x_224);
lean_dec_ref(x_217);
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_226 = x_222;
} else {
 lean_dec_ref(x_222);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_223, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_229 = x_223;
} else {
 lean_dec_ref(x_223);
 x_229 = lean_box(0);
}
x_244 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_245 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_244, x_216, x_224);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_unbox(x_246);
lean_dec(x_246);
if (x_247 == 0)
{
lean_object* x_248; 
lean_dec(x_226);
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_248);
lean_dec_ref(x_245);
x_230 = x_2;
x_231 = x_3;
x_232 = x_4;
x_233 = x_5;
x_234 = x_6;
x_235 = x_7;
x_236 = x_8;
x_237 = x_216;
x_238 = x_10;
x_239 = x_248;
goto block_243;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_250 = x_245;
} else {
 lean_dec_ref(x_245);
 x_250 = lean_box(0);
}
x_251 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_225, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_216, x_10, x_249);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec_ref(x_251);
x_254 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_216, x_10, x_253);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec_ref(x_254);
x_257 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_227, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_216, x_10, x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec_ref(x_257);
x_260 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_261 = l_Lean_MessageData_ofExpr(x_252);
if (lean_is_scalar(x_250)) {
 x_262 = lean_alloc_ctor(7, 2, 0);
} else {
 x_262 = x_250;
 lean_ctor_set_tag(x_262, 7);
}
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
x_263 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
if (lean_is_scalar(x_226)) {
 x_264 = lean_alloc_ctor(7, 2, 0);
} else {
 x_264 = x_226;
 lean_ctor_set_tag(x_264, 7);
}
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = l_Lean_MessageData_ofExpr(x_255);
x_266 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_263);
x_268 = l_Lean_MessageData_ofExpr(x_258);
x_269 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_260);
x_271 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_244, x_270, x_7, x_8, x_216, x_10, x_259);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
lean_dec_ref(x_271);
x_230 = x_2;
x_231 = x_3;
x_232 = x_4;
x_233 = x_5;
x_234 = x_6;
x_235 = x_7;
x_236 = x_8;
x_237 = x_216;
x_238 = x_10;
x_239 = x_272;
goto block_243;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_255);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec_ref(x_216);
lean_dec_ref(x_1);
x_273 = lean_ctor_get(x_257, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_257, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_275 = x_257;
} else {
 lean_dec_ref(x_257);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec_ref(x_216);
lean_dec_ref(x_1);
x_277 = lean_ctor_get(x_254, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_254, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_279 = x_254;
} else {
 lean_dec_ref(x_254);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_250);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec_ref(x_216);
lean_dec_ref(x_1);
x_281 = lean_ctor_get(x_251, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_251, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_283 = x_251;
} else {
 lean_dec_ref(x_251);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
block_243:
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_240, 0, x_225);
lean_ctor_set(x_240, 1, x_227);
lean_ctor_set(x_240, 2, x_1);
if (lean_is_scalar(x_229)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_229;
}
lean_ctor_set(x_241, 0, x_228);
lean_ctor_set(x_241, 1, x_240);
x_1 = x_241;
x_2 = x_230;
x_3 = x_231;
x_4 = x_232;
x_5 = x_233;
x_6 = x_234;
x_7 = x_235;
x_8 = x_236;
x_9 = x_237;
x_10 = x_238;
x_11 = x_239;
goto _start;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec_ref(x_216);
lean_dec_ref(x_1);
x_285 = lean_ctor_get(x_217, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_217, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_287 = x_217;
} else {
 lean_dec_ref(x_217);
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
else
{
lean_object* x_289; 
lean_dec_ref(x_211);
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_1);
x_289 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_202, x_11);
return x_289;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6_spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind linarith` internal error, structure is not an ordered int module", 71, 71);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 20);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___closed__1;
x_16 = l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0___redArg(x_15, x_6, x_7, x_8, x_9, x_14);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec_ref(x_13);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec_ref(x_13);
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
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind linarith` internal error, structure is not an ordered module", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 21);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1;
x_16 = l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0___redArg(x_15, x_6, x_7, x_8, x_9, x_14);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec_ref(x_13);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec_ref(x_13);
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
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_2 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 18);
lean_inc_ref(x_22);
lean_dec(x_21);
x_23 = l_Lean_mkAppB(x_14, x_17, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_ctor_get(x_24, 18);
lean_inc_ref(x_26);
lean_dec(x_24);
x_27 = l_Lean_mkAppB(x_14, x_17, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_17);
lean_dec(x_14);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_dec(x_14);
return x_16;
}
}
else
{
return x_13;
}
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_41, 18);
lean_inc_ref(x_42);
lean_dec(x_41);
x_43 = l_Lean_mkAppB(x_34, x_37, x_42);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_ctor_get(x_44, 18);
lean_inc_ref(x_46);
lean_dec(x_44);
x_47 = l_Lean_mkAppB(x_34, x_37, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_37);
lean_dec(x_34);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
return x_39;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_39);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_dec(x_34);
return x_36;
}
}
else
{
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_34; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0;
x_17 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_16, x_13, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_24 = lean_nat_to_int(x_1);
lean_inc(x_22);
x_25 = l_Lean_Grind_Linarith_Poly_mul(x_22, x_24);
lean_dec(x_24);
x_26 = lean_int_neg(x_4);
lean_inc(x_21);
x_27 = l_Lean_Grind_Linarith_Poly_mul(x_21, x_26);
lean_dec(x_26);
x_28 = l_Lean_Grind_Linarith_Poly_combine(x_25, x_27);
x_34 = lean_unbox(x_18);
lean_dec(x_18);
if (x_34 == 0)
{
x_29 = x_19;
goto block_33;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_45 = l_Lean_MessageData_ofExpr(x_36);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_MessageData_ofExpr(x_39);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
x_52 = l_Lean_MessageData_ofExpr(x_42);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_44);
x_55 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_16, x_54, x_11, x_12, x_13, x_14, x_43);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_29 = x_56;
goto block_33;
}
else
{
uint8_t x_57; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_41);
if (x_57 == 0)
{
return x_41;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_41, 0);
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_41);
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
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_38);
if (x_61 == 0)
{
return x_38;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_38, 0);
x_63 = lean_ctor_get(x_38, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_38);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_28);
lean_dec(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_35);
if (x_65 == 0)
{
return x_35;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_35, 0);
x_67 = lean_ctor_get(x_35, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_35);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
block_33:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_alloc_ctor(11, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_5);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_23);
if (lean_is_scalar(x_20)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_20;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwError___at___Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_16;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_8, x_7);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_dec_ref(x_9);
x_22 = lean_array_uget(x_6, x_8);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(x_1, x_2, x_3, x_24, x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_29 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_27, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; size_t x_35; size_t x_36; 
lean_free_object(x_22);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec_ref(x_31);
x_35 = 1;
x_36 = lean_usize_add(x_8, x_35);
lean_inc_ref(x_4);
{
size_t _tmp_7 = x_36;
lean_object* _tmp_8 = x_4;
lean_object* _tmp_18 = x_34;
x_8 = _tmp_7;
x_9 = _tmp_8;
x_19 = _tmp_18;
}
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_31, 0);
lean_dec(x_39);
x_40 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 0, x_40);
lean_ctor_set(x_31, 0, x_22);
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_dec(x_31);
x_42 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 0, x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_22);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_free_object(x_22);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_22);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_29);
if (x_48 == 0)
{
return x_29;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_29);
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
lean_free_object(x_22);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_26);
if (x_52 == 0)
{
return x_26;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_26, 0);
x_54 = lean_ctor_get(x_26, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_26);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_22, 0);
x_57 = lean_ctor_get(x_22, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_22);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(x_1, x_2, x_3, x_56, x_57, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_61 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_59, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; size_t x_67; size_t x_68; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec_ref(x_63);
x_67 = 1;
x_68 = lean_usize_add(x_8, x_67);
lean_inc_ref(x_4);
{
size_t _tmp_7 = x_68;
lean_object* _tmp_8 = x_4;
lean_object* _tmp_18 = x_66;
x_8 = _tmp_7;
x_9 = _tmp_8;
x_19 = _tmp_18;
}
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
x_72 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_5);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_ctor_get(x_63, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_63, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_77 = x_63;
} else {
 lean_dec_ref(x_63);
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
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_ctor_get(x_61, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_61, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_81 = x_61;
} else {
 lean_dec_ref(x_61);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_ctor_get(x_58, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_58, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_85 = x_58;
} else {
 lean_dec_ref(x_58);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0() {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_box(0);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0;
x_17 = lean_array_size(x_4);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(x_1, x_2, x_3, x_16, x_15, x_4, x_17, x_18, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec_ref(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec_ref(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_21 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_20, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec_ref(x_6);
return x_22;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_array_uget(x_5, x_7);
lean_inc(x_11);
lean_inc(x_2);
x_14 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_13, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_11);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_4);
x_17 = 1;
x_18 = lean_usize_add(x_7, x_17);
x_7 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_array_uget(x_5, x_7);
lean_inc(x_20);
lean_inc(x_2);
x_22 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_21, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_2);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_20);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
lean_inc(x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_7, x_27);
x_7 = x_28;
x_8 = x_26;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_array_uget(x_4, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = l_Lean_Grind_Linarith_Poly_coeff(x_22, x_2);
lean_dec(x_22);
lean_inc(x_3);
x_24 = lean_nat_to_int(x_3);
x_25 = lean_int_dec_eq(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_23);
x_26 = lean_array_push(x_20, x_7);
lean_ctor_set(x_16, 1, x_26);
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
lean_free_object(x_7);
x_27 = l_Lean_PersistentArray_push___redArg(x_19, x_21);
lean_ctor_set(x_16, 0, x_27);
x_8 = x_16;
goto block_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_array_uget(x_4, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = l_Lean_Grind_Linarith_Poly_coeff(x_31, x_2);
lean_dec(x_31);
lean_inc(x_3);
x_33 = lean_nat_to_int(x_3);
x_34 = lean_int_dec_eq(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_32);
x_35 = lean_array_push(x_29, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_8 = x_36;
goto block_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_free_object(x_7);
x_37 = l_Lean_PersistentArray_push___redArg(x_28, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
x_8 = x_38;
goto block_13;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_dec(x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_array_uget(x_4, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = l_Lean_Grind_Linarith_Poly_coeff(x_44, x_2);
lean_dec(x_44);
lean_inc(x_3);
x_46 = lean_nat_to_int(x_3);
x_47 = lean_int_dec_eq(x_45, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_43);
x_49 = lean_array_push(x_41, x_48);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_42;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_8 = x_50;
goto block_13;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_51 = l_Lean_PersistentArray_push___redArg(x_40, x_43);
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_8 = x_52;
goto block_13;
}
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_6, x_10);
x_6 = x_11;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_array_uget(x_4, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = l_Lean_Grind_Linarith_Poly_coeff(x_22, x_1);
lean_dec(x_22);
lean_inc(x_2);
x_24 = lean_nat_to_int(x_2);
x_25 = lean_int_dec_eq(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_23);
x_26 = lean_array_push(x_20, x_7);
lean_ctor_set(x_16, 1, x_26);
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
lean_free_object(x_7);
x_27 = l_Lean_PersistentArray_push___redArg(x_19, x_21);
lean_ctor_set(x_16, 0, x_27);
x_8 = x_16;
goto block_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_array_uget(x_4, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = l_Lean_Grind_Linarith_Poly_coeff(x_31, x_1);
lean_dec(x_31);
lean_inc(x_2);
x_33 = lean_nat_to_int(x_2);
x_34 = lean_int_dec_eq(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_32);
x_35 = lean_array_push(x_29, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_8 = x_36;
goto block_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_free_object(x_7);
x_37 = l_Lean_PersistentArray_push___redArg(x_28, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
x_8 = x_38;
goto block_13;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_dec(x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_array_uget(x_4, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = l_Lean_Grind_Linarith_Poly_coeff(x_44, x_1);
lean_dec(x_44);
lean_inc(x_2);
x_46 = lean_nat_to_int(x_2);
x_47 = lean_int_dec_eq(x_45, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_43);
x_49 = lean_array_push(x_41, x_48);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_42;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_8 = x_50;
goto block_13;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_51 = l_Lean_PersistentArray_push___redArg(x_40, x_43);
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_8 = x_52;
goto block_13;
}
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_6, x_10);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1_spec__1(x_3, x_1, x_2, x_4, x_5, x_11, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_array_size(x_7);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_8, x_7, x_10, x_11, x_9);
lean_dec_ref(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_12);
lean_free_object(x_4);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_array_size(x_16);
x_20 = 0;
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_17, x_16, x_19, x_20, x_18);
lean_dec_ref(x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec_ref(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
x_30 = lean_array_size(x_27);
x_31 = 0;
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_28, x_27, x_30, x_31, x_29);
lean_dec_ref(x_27);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
lean_ctor_set(x_4, 0, x_34);
return x_4;
}
else
{
lean_object* x_35; 
lean_dec_ref(x_32);
lean_free_object(x_4);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec_ref(x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
lean_dec(x_4);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
x_39 = lean_array_size(x_36);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_37, x_36, x_39, x_40, x_38);
lean_dec_ref(x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec_ref(x_41);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec_ref(x_42);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_array_uget(x_4, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = l_Lean_Grind_Linarith_Poly_coeff(x_22, x_2);
lean_dec(x_22);
lean_inc(x_3);
x_24 = lean_nat_to_int(x_3);
x_25 = lean_int_dec_eq(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_23);
x_26 = lean_array_push(x_20, x_7);
lean_ctor_set(x_16, 1, x_26);
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
lean_free_object(x_7);
x_27 = l_Lean_PersistentArray_push___redArg(x_19, x_21);
lean_ctor_set(x_16, 0, x_27);
x_8 = x_16;
goto block_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_array_uget(x_4, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = l_Lean_Grind_Linarith_Poly_coeff(x_31, x_2);
lean_dec(x_31);
lean_inc(x_3);
x_33 = lean_nat_to_int(x_3);
x_34 = lean_int_dec_eq(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_32);
x_35 = lean_array_push(x_29, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_8 = x_36;
goto block_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_free_object(x_7);
x_37 = l_Lean_PersistentArray_push___redArg(x_28, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
x_8 = x_38;
goto block_13;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_dec(x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_array_uget(x_4, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = l_Lean_Grind_Linarith_Poly_coeff(x_44, x_2);
lean_dec(x_44);
lean_inc(x_3);
x_46 = lean_nat_to_int(x_3);
x_47 = lean_int_dec_eq(x_45, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_43);
x_49 = lean_array_push(x_41, x_48);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_42;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_8 = x_50;
goto block_13;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_51 = l_Lean_PersistentArray_push___redArg(x_40, x_43);
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_8 = x_52;
goto block_13;
}
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_6, x_10);
x_6 = x_11;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_array_uget(x_4, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = l_Lean_Grind_Linarith_Poly_coeff(x_22, x_1);
lean_dec(x_22);
lean_inc(x_2);
x_24 = lean_nat_to_int(x_2);
x_25 = lean_int_dec_eq(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_23);
x_26 = lean_array_push(x_20, x_7);
lean_ctor_set(x_16, 1, x_26);
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
lean_free_object(x_7);
x_27 = l_Lean_PersistentArray_push___redArg(x_19, x_21);
lean_ctor_set(x_16, 0, x_27);
x_8 = x_16;
goto block_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_array_uget(x_4, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = l_Lean_Grind_Linarith_Poly_coeff(x_31, x_1);
lean_dec(x_31);
lean_inc(x_2);
x_33 = lean_nat_to_int(x_2);
x_34 = lean_int_dec_eq(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_32);
x_35 = lean_array_push(x_29, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_8 = x_36;
goto block_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_free_object(x_7);
x_37 = l_Lean_PersistentArray_push___redArg(x_28, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
x_8 = x_38;
goto block_13;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_dec(x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_array_uget(x_4, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = l_Lean_Grind_Linarith_Poly_coeff(x_44, x_1);
lean_dec(x_44);
lean_inc(x_2);
x_46 = lean_nat_to_int(x_2);
x_47 = lean_int_dec_eq(x_45, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_43);
x_49 = lean_array_push(x_41, x_48);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_42;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_8 = x_50;
goto block_13;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_51 = l_Lean_PersistentArray_push___redArg(x_40, x_43);
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_8 = x_52;
goto block_13;
}
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_6, x_10);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__4_spec__4(x_3, x_1, x_2, x_4, x_5, x_11, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
lean_inc_ref(x_4);
lean_inc(x_2);
x_7 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0(x_1, x_2, x_4, x_5, x_4);
lean_dec_ref(x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_array_size(x_6);
x_13 = 0;
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__4(x_1, x_2, x_10, x_6, x_12, x_13, x_11);
lean_dec_ref(x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__4;
x_5 = l_Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(x_1, x_3, x_2, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__4_spec__4(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__4(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_46; 
x_46 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec_ref(x_46);
x_50 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_142 = lean_ctor_get(x_51, 32);
lean_inc_ref(x_142);
lean_dec(x_51);
x_143 = lean_ctor_get(x_142, 2);
x_144 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
x_145 = lean_nat_dec_lt(x_4, x_143);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec_ref(x_142);
x_146 = l_outOfBounds___redArg(x_144);
x_53 = x_146;
goto block_141;
}
else
{
lean_object* x_147; 
x_147 = l_Lean_PersistentArray_get_x21___redArg(x_144, x_142, x_4);
x_53 = x_147;
goto block_141;
}
block_141:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_54 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(x_2, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = lean_st_ref_take(x_6, x_52);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 14);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_59, 3);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec_ref(x_57);
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_58, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 3);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_58, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_58, 5);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_58, 6);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_58, 7);
lean_inc_ref(x_69);
x_70 = lean_ctor_get_uint8(x_58, sizeof(void*)*16);
x_71 = lean_ctor_get(x_58, 8);
lean_inc(x_71);
x_72 = lean_ctor_get(x_58, 9);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_58, 10);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_58, 11);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_58, 12);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_58, 13);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_58, 15);
lean_inc_ref(x_77);
lean_dec(x_58);
x_78 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_59, 2);
lean_inc_ref(x_80);
lean_dec_ref(x_59);
x_81 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_60, 2);
lean_inc_ref(x_83);
lean_dec_ref(x_60);
x_84 = lean_array_get_size(x_81);
x_85 = lean_nat_dec_lt(x_5, x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_dec(x_55);
x_15 = x_71;
x_16 = x_74;
x_17 = x_75;
x_18 = x_65;
x_19 = x_68;
x_20 = x_73;
x_21 = x_66;
x_22 = x_69;
x_23 = x_56;
x_24 = x_76;
x_25 = x_78;
x_26 = x_64;
x_27 = x_77;
x_28 = x_67;
x_29 = x_61;
x_30 = x_82;
x_31 = x_83;
x_32 = x_63;
x_33 = x_70;
x_34 = x_80;
x_35 = x_79;
x_36 = x_62;
x_37 = x_72;
x_38 = x_81;
goto block_45;
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_array_fget(x_81, x_5);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_86, 32);
x_89 = lean_box(0);
x_90 = lean_array_fset(x_81, x_5, x_89);
x_91 = l_Lean_PersistentArray_set___redArg(x_88, x_4, x_55);
lean_ctor_set(x_86, 32, x_91);
x_92 = lean_array_fset(x_90, x_5, x_86);
x_15 = x_71;
x_16 = x_74;
x_17 = x_75;
x_18 = x_65;
x_19 = x_68;
x_20 = x_73;
x_21 = x_66;
x_22 = x_69;
x_23 = x_56;
x_24 = x_76;
x_25 = x_78;
x_26 = x_64;
x_27 = x_77;
x_28 = x_67;
x_29 = x_61;
x_30 = x_82;
x_31 = x_83;
x_32 = x_63;
x_33 = x_70;
x_34 = x_80;
x_35 = x_79;
x_36 = x_62;
x_37 = x_72;
x_38 = x_92;
goto block_45;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_93 = lean_ctor_get(x_86, 0);
x_94 = lean_ctor_get(x_86, 1);
x_95 = lean_ctor_get(x_86, 2);
x_96 = lean_ctor_get(x_86, 3);
x_97 = lean_ctor_get(x_86, 4);
x_98 = lean_ctor_get(x_86, 5);
x_99 = lean_ctor_get(x_86, 6);
x_100 = lean_ctor_get(x_86, 7);
x_101 = lean_ctor_get(x_86, 8);
x_102 = lean_ctor_get(x_86, 9);
x_103 = lean_ctor_get(x_86, 10);
x_104 = lean_ctor_get(x_86, 11);
x_105 = lean_ctor_get(x_86, 12);
x_106 = lean_ctor_get(x_86, 13);
x_107 = lean_ctor_get(x_86, 14);
x_108 = lean_ctor_get(x_86, 15);
x_109 = lean_ctor_get(x_86, 16);
x_110 = lean_ctor_get(x_86, 17);
x_111 = lean_ctor_get(x_86, 18);
x_112 = lean_ctor_get(x_86, 19);
x_113 = lean_ctor_get(x_86, 20);
x_114 = lean_ctor_get(x_86, 21);
x_115 = lean_ctor_get(x_86, 22);
x_116 = lean_ctor_get(x_86, 23);
x_117 = lean_ctor_get(x_86, 24);
x_118 = lean_ctor_get(x_86, 25);
x_119 = lean_ctor_get(x_86, 26);
x_120 = lean_ctor_get(x_86, 27);
x_121 = lean_ctor_get(x_86, 28);
x_122 = lean_ctor_get(x_86, 29);
x_123 = lean_ctor_get(x_86, 30);
x_124 = lean_ctor_get(x_86, 31);
x_125 = lean_ctor_get(x_86, 32);
x_126 = lean_ctor_get(x_86, 33);
x_127 = lean_ctor_get(x_86, 34);
x_128 = lean_ctor_get(x_86, 35);
x_129 = lean_ctor_get_uint8(x_86, sizeof(void*)*42);
x_130 = lean_ctor_get(x_86, 36);
x_131 = lean_ctor_get(x_86, 37);
x_132 = lean_ctor_get(x_86, 38);
x_133 = lean_ctor_get(x_86, 39);
x_134 = lean_ctor_get(x_86, 40);
x_135 = lean_ctor_get(x_86, 41);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_86);
x_136 = lean_box(0);
x_137 = lean_array_fset(x_81, x_5, x_136);
x_138 = l_Lean_PersistentArray_set___redArg(x_125, x_4, x_55);
x_139 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_139, 0, x_93);
lean_ctor_set(x_139, 1, x_94);
lean_ctor_set(x_139, 2, x_95);
lean_ctor_set(x_139, 3, x_96);
lean_ctor_set(x_139, 4, x_97);
lean_ctor_set(x_139, 5, x_98);
lean_ctor_set(x_139, 6, x_99);
lean_ctor_set(x_139, 7, x_100);
lean_ctor_set(x_139, 8, x_101);
lean_ctor_set(x_139, 9, x_102);
lean_ctor_set(x_139, 10, x_103);
lean_ctor_set(x_139, 11, x_104);
lean_ctor_set(x_139, 12, x_105);
lean_ctor_set(x_139, 13, x_106);
lean_ctor_set(x_139, 14, x_107);
lean_ctor_set(x_139, 15, x_108);
lean_ctor_set(x_139, 16, x_109);
lean_ctor_set(x_139, 17, x_110);
lean_ctor_set(x_139, 18, x_111);
lean_ctor_set(x_139, 19, x_112);
lean_ctor_set(x_139, 20, x_113);
lean_ctor_set(x_139, 21, x_114);
lean_ctor_set(x_139, 22, x_115);
lean_ctor_set(x_139, 23, x_116);
lean_ctor_set(x_139, 24, x_117);
lean_ctor_set(x_139, 25, x_118);
lean_ctor_set(x_139, 26, x_119);
lean_ctor_set(x_139, 27, x_120);
lean_ctor_set(x_139, 28, x_121);
lean_ctor_set(x_139, 29, x_122);
lean_ctor_set(x_139, 30, x_123);
lean_ctor_set(x_139, 31, x_124);
lean_ctor_set(x_139, 32, x_138);
lean_ctor_set(x_139, 33, x_126);
lean_ctor_set(x_139, 34, x_127);
lean_ctor_set(x_139, 35, x_128);
lean_ctor_set(x_139, 36, x_130);
lean_ctor_set(x_139, 37, x_131);
lean_ctor_set(x_139, 38, x_132);
lean_ctor_set(x_139, 39, x_133);
lean_ctor_set(x_139, 40, x_134);
lean_ctor_set(x_139, 41, x_135);
lean_ctor_set_uint8(x_139, sizeof(void*)*42, x_129);
x_140 = lean_array_fset(x_137, x_5, x_139);
x_15 = x_71;
x_16 = x_74;
x_17 = x_75;
x_18 = x_65;
x_19 = x_68;
x_20 = x_73;
x_21 = x_66;
x_22 = x_69;
x_23 = x_56;
x_24 = x_76;
x_25 = x_78;
x_26 = x_64;
x_27 = x_77;
x_28 = x_67;
x_29 = x_61;
x_30 = x_82;
x_31 = x_83;
x_32 = x_63;
x_33 = x_70;
x_34 = x_80;
x_35 = x_79;
x_36 = x_62;
x_37 = x_72;
x_38 = x_140;
goto block_45;
}
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_50);
if (x_148 == 0)
{
return x_50;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_50, 0);
x_150 = lean_ctor_get(x_50, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_50);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_46);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_46, 0);
lean_dec(x_153);
x_154 = lean_box(0);
lean_ctor_set(x_46, 0, x_154);
return x_46;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_46, 1);
lean_inc(x_155);
lean_dec(x_46);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_46);
if (x_158 == 0)
{
return x_46;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_46, 0);
x_160 = lean_ctor_get(x_46, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_46);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
block_45:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_39, 2, x_31);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_34);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_26);
lean_ctor_set(x_41, 3, x_18);
lean_ctor_set(x_41, 4, x_21);
lean_ctor_set(x_41, 5, x_28);
lean_ctor_set(x_41, 6, x_19);
lean_ctor_set(x_41, 7, x_22);
lean_ctor_set(x_41, 8, x_15);
lean_ctor_set(x_41, 9, x_37);
lean_ctor_set(x_41, 10, x_20);
lean_ctor_set(x_41, 11, x_16);
lean_ctor_set(x_41, 12, x_17);
lean_ctor_set(x_41, 13, x_24);
lean_ctor_set(x_41, 14, x_40);
lean_ctor_set(x_41, 15, x_27);
lean_ctor_set_uint8(x_41, sizeof(void*)*16, x_33);
x_42 = lean_st_ref_set(x_6, x_41, x_29);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_1, x_2, x_3, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_43);
lean_dec_ref(x_23);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_46; 
x_46 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec_ref(x_46);
x_50 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_142 = lean_ctor_get(x_51, 33);
lean_inc_ref(x_142);
lean_dec(x_51);
x_143 = lean_ctor_get(x_142, 2);
x_144 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
x_145 = lean_nat_dec_lt(x_4, x_143);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec_ref(x_142);
x_146 = l_outOfBounds___redArg(x_144);
x_53 = x_146;
goto block_141;
}
else
{
lean_object* x_147; 
x_147 = l_Lean_PersistentArray_get_x21___redArg(x_144, x_142, x_4);
x_53 = x_147;
goto block_141;
}
block_141:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_54 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(x_2, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = lean_st_ref_take(x_6, x_52);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 14);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_59, 3);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec_ref(x_57);
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_58, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 3);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_58, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_58, 5);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_58, 6);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_58, 7);
lean_inc_ref(x_69);
x_70 = lean_ctor_get_uint8(x_58, sizeof(void*)*16);
x_71 = lean_ctor_get(x_58, 8);
lean_inc(x_71);
x_72 = lean_ctor_get(x_58, 9);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_58, 10);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_58, 11);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_58, 12);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_58, 13);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_58, 15);
lean_inc_ref(x_77);
lean_dec(x_58);
x_78 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_59, 2);
lean_inc_ref(x_80);
lean_dec_ref(x_59);
x_81 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_60, 2);
lean_inc_ref(x_83);
lean_dec_ref(x_60);
x_84 = lean_array_get_size(x_81);
x_85 = lean_nat_dec_lt(x_5, x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_dec(x_55);
x_15 = x_67;
x_16 = x_70;
x_17 = x_64;
x_18 = x_69;
x_19 = x_68;
x_20 = x_56;
x_21 = x_76;
x_22 = x_73;
x_23 = x_74;
x_24 = x_77;
x_25 = x_65;
x_26 = x_82;
x_27 = x_83;
x_28 = x_80;
x_29 = x_62;
x_30 = x_78;
x_31 = x_71;
x_32 = x_72;
x_33 = x_79;
x_34 = x_66;
x_35 = x_75;
x_36 = x_63;
x_37 = x_61;
x_38 = x_81;
goto block_45;
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_array_fget(x_81, x_5);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_86, 33);
x_89 = lean_box(0);
x_90 = lean_array_fset(x_81, x_5, x_89);
x_91 = l_Lean_PersistentArray_set___redArg(x_88, x_4, x_55);
lean_ctor_set(x_86, 33, x_91);
x_92 = lean_array_fset(x_90, x_5, x_86);
x_15 = x_67;
x_16 = x_70;
x_17 = x_64;
x_18 = x_69;
x_19 = x_68;
x_20 = x_56;
x_21 = x_76;
x_22 = x_73;
x_23 = x_74;
x_24 = x_77;
x_25 = x_65;
x_26 = x_82;
x_27 = x_83;
x_28 = x_80;
x_29 = x_62;
x_30 = x_78;
x_31 = x_71;
x_32 = x_72;
x_33 = x_79;
x_34 = x_66;
x_35 = x_75;
x_36 = x_63;
x_37 = x_61;
x_38 = x_92;
goto block_45;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_93 = lean_ctor_get(x_86, 0);
x_94 = lean_ctor_get(x_86, 1);
x_95 = lean_ctor_get(x_86, 2);
x_96 = lean_ctor_get(x_86, 3);
x_97 = lean_ctor_get(x_86, 4);
x_98 = lean_ctor_get(x_86, 5);
x_99 = lean_ctor_get(x_86, 6);
x_100 = lean_ctor_get(x_86, 7);
x_101 = lean_ctor_get(x_86, 8);
x_102 = lean_ctor_get(x_86, 9);
x_103 = lean_ctor_get(x_86, 10);
x_104 = lean_ctor_get(x_86, 11);
x_105 = lean_ctor_get(x_86, 12);
x_106 = lean_ctor_get(x_86, 13);
x_107 = lean_ctor_get(x_86, 14);
x_108 = lean_ctor_get(x_86, 15);
x_109 = lean_ctor_get(x_86, 16);
x_110 = lean_ctor_get(x_86, 17);
x_111 = lean_ctor_get(x_86, 18);
x_112 = lean_ctor_get(x_86, 19);
x_113 = lean_ctor_get(x_86, 20);
x_114 = lean_ctor_get(x_86, 21);
x_115 = lean_ctor_get(x_86, 22);
x_116 = lean_ctor_get(x_86, 23);
x_117 = lean_ctor_get(x_86, 24);
x_118 = lean_ctor_get(x_86, 25);
x_119 = lean_ctor_get(x_86, 26);
x_120 = lean_ctor_get(x_86, 27);
x_121 = lean_ctor_get(x_86, 28);
x_122 = lean_ctor_get(x_86, 29);
x_123 = lean_ctor_get(x_86, 30);
x_124 = lean_ctor_get(x_86, 31);
x_125 = lean_ctor_get(x_86, 32);
x_126 = lean_ctor_get(x_86, 33);
x_127 = lean_ctor_get(x_86, 34);
x_128 = lean_ctor_get(x_86, 35);
x_129 = lean_ctor_get_uint8(x_86, sizeof(void*)*42);
x_130 = lean_ctor_get(x_86, 36);
x_131 = lean_ctor_get(x_86, 37);
x_132 = lean_ctor_get(x_86, 38);
x_133 = lean_ctor_get(x_86, 39);
x_134 = lean_ctor_get(x_86, 40);
x_135 = lean_ctor_get(x_86, 41);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_86);
x_136 = lean_box(0);
x_137 = lean_array_fset(x_81, x_5, x_136);
x_138 = l_Lean_PersistentArray_set___redArg(x_126, x_4, x_55);
x_139 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_139, 0, x_93);
lean_ctor_set(x_139, 1, x_94);
lean_ctor_set(x_139, 2, x_95);
lean_ctor_set(x_139, 3, x_96);
lean_ctor_set(x_139, 4, x_97);
lean_ctor_set(x_139, 5, x_98);
lean_ctor_set(x_139, 6, x_99);
lean_ctor_set(x_139, 7, x_100);
lean_ctor_set(x_139, 8, x_101);
lean_ctor_set(x_139, 9, x_102);
lean_ctor_set(x_139, 10, x_103);
lean_ctor_set(x_139, 11, x_104);
lean_ctor_set(x_139, 12, x_105);
lean_ctor_set(x_139, 13, x_106);
lean_ctor_set(x_139, 14, x_107);
lean_ctor_set(x_139, 15, x_108);
lean_ctor_set(x_139, 16, x_109);
lean_ctor_set(x_139, 17, x_110);
lean_ctor_set(x_139, 18, x_111);
lean_ctor_set(x_139, 19, x_112);
lean_ctor_set(x_139, 20, x_113);
lean_ctor_set(x_139, 21, x_114);
lean_ctor_set(x_139, 22, x_115);
lean_ctor_set(x_139, 23, x_116);
lean_ctor_set(x_139, 24, x_117);
lean_ctor_set(x_139, 25, x_118);
lean_ctor_set(x_139, 26, x_119);
lean_ctor_set(x_139, 27, x_120);
lean_ctor_set(x_139, 28, x_121);
lean_ctor_set(x_139, 29, x_122);
lean_ctor_set(x_139, 30, x_123);
lean_ctor_set(x_139, 31, x_124);
lean_ctor_set(x_139, 32, x_125);
lean_ctor_set(x_139, 33, x_138);
lean_ctor_set(x_139, 34, x_127);
lean_ctor_set(x_139, 35, x_128);
lean_ctor_set(x_139, 36, x_130);
lean_ctor_set(x_139, 37, x_131);
lean_ctor_set(x_139, 38, x_132);
lean_ctor_set(x_139, 39, x_133);
lean_ctor_set(x_139, 40, x_134);
lean_ctor_set(x_139, 41, x_135);
lean_ctor_set_uint8(x_139, sizeof(void*)*42, x_129);
x_140 = lean_array_fset(x_137, x_5, x_139);
x_15 = x_67;
x_16 = x_70;
x_17 = x_64;
x_18 = x_69;
x_19 = x_68;
x_20 = x_56;
x_21 = x_76;
x_22 = x_73;
x_23 = x_74;
x_24 = x_77;
x_25 = x_65;
x_26 = x_82;
x_27 = x_83;
x_28 = x_80;
x_29 = x_62;
x_30 = x_78;
x_31 = x_71;
x_32 = x_72;
x_33 = x_79;
x_34 = x_66;
x_35 = x_75;
x_36 = x_63;
x_37 = x_61;
x_38 = x_140;
goto block_45;
}
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_50);
if (x_148 == 0)
{
return x_50;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_50, 0);
x_150 = lean_ctor_get(x_50, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_50);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_46);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_46, 0);
lean_dec(x_153);
x_154 = lean_box(0);
lean_ctor_set(x_46, 0, x_154);
return x_46;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_46, 1);
lean_inc(x_155);
lean_dec(x_46);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_46);
if (x_158 == 0)
{
return x_46;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_46, 0);
x_160 = lean_ctor_get(x_46, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_46);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
block_45:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_27);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_33);
lean_ctor_set(x_40, 2, x_28);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_17);
lean_ctor_set(x_41, 3, x_25);
lean_ctor_set(x_41, 4, x_34);
lean_ctor_set(x_41, 5, x_15);
lean_ctor_set(x_41, 6, x_19);
lean_ctor_set(x_41, 7, x_18);
lean_ctor_set(x_41, 8, x_31);
lean_ctor_set(x_41, 9, x_32);
lean_ctor_set(x_41, 10, x_22);
lean_ctor_set(x_41, 11, x_23);
lean_ctor_set(x_41, 12, x_35);
lean_ctor_set(x_41, 13, x_21);
lean_ctor_set(x_41, 14, x_40);
lean_ctor_set(x_41, 15, x_24);
lean_ctor_set_uint8(x_41, sizeof(void*)*16, x_16);
x_42 = lean_st_ref_set(x_6, x_41, x_37);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_1, x_2, x_3, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_43);
lean_dec_ref(x_20);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ignored", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2;
x_150 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_149, x_9, x_11);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec_ref(x_150);
x_47 = x_2;
x_48 = x_3;
x_49 = x_4;
x_50 = x_5;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_9;
x_55 = x_10;
x_56 = x_153;
goto block_148;
}
else
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_150);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_150, 1);
x_156 = lean_ctor_get(x_150, 0);
lean_dec(x_156);
x_157 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_155);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec_ref(x_157);
x_160 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_161 = l_Lean_MessageData_ofExpr(x_158);
lean_ctor_set_tag(x_150, 7);
lean_ctor_set(x_150, 1, x_161);
lean_ctor_set(x_150, 0, x_160);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_150);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_149, x_162, x_7, x_8, x_9, x_10, x_159);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec_ref(x_163);
x_47 = x_2;
x_48 = x_3;
x_49 = x_4;
x_50 = x_5;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_9;
x_55 = x_10;
x_56 = x_164;
goto block_148;
}
else
{
uint8_t x_165; 
lean_free_object(x_150);
x_165 = !lean_is_exclusive(x_157);
if (x_165 == 0)
{
return x_157;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_157, 0);
x_167 = lean_ctor_get(x_157, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_157);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_150, 1);
lean_inc(x_169);
lean_dec(x_150);
x_170 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec_ref(x_170);
x_173 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_174 = l_Lean_MessageData_ofExpr(x_171);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
x_177 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_149, x_176, x_7, x_8, x_9, x_10, x_172);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec_ref(x_177);
x_47 = x_2;
x_48 = x_3;
x_49 = x_4;
x_50 = x_5;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_9;
x_55 = x_10;
x_56 = x_178;
goto block_148;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_170, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_170, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_181 = x_170;
} else {
 lean_dec_ref(x_170);
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
}
block_46:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
lean_ctor_set(x_36, 2, x_29);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_14);
lean_ctor_set(x_38, 2, x_21);
lean_ctor_set(x_38, 3, x_25);
lean_ctor_set(x_38, 4, x_22);
lean_ctor_set(x_38, 5, x_23);
lean_ctor_set(x_38, 6, x_15);
lean_ctor_set(x_38, 7, x_20);
lean_ctor_set(x_38, 8, x_24);
lean_ctor_set(x_38, 9, x_27);
lean_ctor_set(x_38, 10, x_13);
lean_ctor_set(x_38, 11, x_19);
lean_ctor_set(x_38, 12, x_18);
lean_ctor_set(x_38, 13, x_26);
lean_ctor_set(x_38, 14, x_37);
lean_ctor_set(x_38, 15, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*16, x_34);
x_39 = lean_st_ref_set(x_31, x_38, x_16);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
block_148:
{
lean_object* x_57; 
x_57 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_47, x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_55, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_st_ref_take(x_48, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 14);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_62, 3);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec_ref(x_60);
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_61, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 3);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_61, 4);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_61, 5);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_61, 6);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_61, 7);
lean_inc_ref(x_72);
x_73 = lean_ctor_get_uint8(x_61, sizeof(void*)*16);
x_74 = lean_ctor_get(x_61, 8);
lean_inc(x_74);
x_75 = lean_ctor_get(x_61, 9);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_61, 10);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_61, 11);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_61, 12);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_61, 13);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_61, 15);
lean_inc_ref(x_80);
lean_dec(x_61);
x_81 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_62, 2);
lean_inc_ref(x_83);
lean_dec_ref(x_62);
x_84 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_86);
lean_dec_ref(x_63);
x_87 = lean_array_get_size(x_84);
x_88 = lean_nat_dec_lt(x_47, x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_dec(x_58);
x_12 = x_65;
x_13 = x_76;
x_14 = x_66;
x_15 = x_71;
x_16 = x_64;
x_17 = x_81;
x_18 = x_78;
x_19 = x_77;
x_20 = x_72;
x_21 = x_67;
x_22 = x_69;
x_23 = x_70;
x_24 = x_74;
x_25 = x_68;
x_26 = x_79;
x_27 = x_75;
x_28 = x_85;
x_29 = x_86;
x_30 = x_83;
x_31 = x_48;
x_32 = x_80;
x_33 = x_82;
x_34 = x_73;
x_35 = x_84;
goto block_46;
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_array_fget(x_84, x_47);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_89, 41);
x_92 = lean_box(0);
x_93 = lean_array_fset(x_84, x_47, x_92);
x_94 = l_Lean_PersistentArray_push___redArg(x_91, x_58);
lean_ctor_set(x_89, 41, x_94);
x_95 = lean_array_fset(x_93, x_47, x_89);
x_12 = x_65;
x_13 = x_76;
x_14 = x_66;
x_15 = x_71;
x_16 = x_64;
x_17 = x_81;
x_18 = x_78;
x_19 = x_77;
x_20 = x_72;
x_21 = x_67;
x_22 = x_69;
x_23 = x_70;
x_24 = x_74;
x_25 = x_68;
x_26 = x_79;
x_27 = x_75;
x_28 = x_85;
x_29 = x_86;
x_30 = x_83;
x_31 = x_48;
x_32 = x_80;
x_33 = x_82;
x_34 = x_73;
x_35 = x_95;
goto block_46;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_96 = lean_ctor_get(x_89, 0);
x_97 = lean_ctor_get(x_89, 1);
x_98 = lean_ctor_get(x_89, 2);
x_99 = lean_ctor_get(x_89, 3);
x_100 = lean_ctor_get(x_89, 4);
x_101 = lean_ctor_get(x_89, 5);
x_102 = lean_ctor_get(x_89, 6);
x_103 = lean_ctor_get(x_89, 7);
x_104 = lean_ctor_get(x_89, 8);
x_105 = lean_ctor_get(x_89, 9);
x_106 = lean_ctor_get(x_89, 10);
x_107 = lean_ctor_get(x_89, 11);
x_108 = lean_ctor_get(x_89, 12);
x_109 = lean_ctor_get(x_89, 13);
x_110 = lean_ctor_get(x_89, 14);
x_111 = lean_ctor_get(x_89, 15);
x_112 = lean_ctor_get(x_89, 16);
x_113 = lean_ctor_get(x_89, 17);
x_114 = lean_ctor_get(x_89, 18);
x_115 = lean_ctor_get(x_89, 19);
x_116 = lean_ctor_get(x_89, 20);
x_117 = lean_ctor_get(x_89, 21);
x_118 = lean_ctor_get(x_89, 22);
x_119 = lean_ctor_get(x_89, 23);
x_120 = lean_ctor_get(x_89, 24);
x_121 = lean_ctor_get(x_89, 25);
x_122 = lean_ctor_get(x_89, 26);
x_123 = lean_ctor_get(x_89, 27);
x_124 = lean_ctor_get(x_89, 28);
x_125 = lean_ctor_get(x_89, 29);
x_126 = lean_ctor_get(x_89, 30);
x_127 = lean_ctor_get(x_89, 31);
x_128 = lean_ctor_get(x_89, 32);
x_129 = lean_ctor_get(x_89, 33);
x_130 = lean_ctor_get(x_89, 34);
x_131 = lean_ctor_get(x_89, 35);
x_132 = lean_ctor_get_uint8(x_89, sizeof(void*)*42);
x_133 = lean_ctor_get(x_89, 36);
x_134 = lean_ctor_get(x_89, 37);
x_135 = lean_ctor_get(x_89, 38);
x_136 = lean_ctor_get(x_89, 39);
x_137 = lean_ctor_get(x_89, 40);
x_138 = lean_ctor_get(x_89, 41);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_89);
x_139 = lean_box(0);
x_140 = lean_array_fset(x_84, x_47, x_139);
x_141 = l_Lean_PersistentArray_push___redArg(x_138, x_58);
x_142 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_142, 0, x_96);
lean_ctor_set(x_142, 1, x_97);
lean_ctor_set(x_142, 2, x_98);
lean_ctor_set(x_142, 3, x_99);
lean_ctor_set(x_142, 4, x_100);
lean_ctor_set(x_142, 5, x_101);
lean_ctor_set(x_142, 6, x_102);
lean_ctor_set(x_142, 7, x_103);
lean_ctor_set(x_142, 8, x_104);
lean_ctor_set(x_142, 9, x_105);
lean_ctor_set(x_142, 10, x_106);
lean_ctor_set(x_142, 11, x_107);
lean_ctor_set(x_142, 12, x_108);
lean_ctor_set(x_142, 13, x_109);
lean_ctor_set(x_142, 14, x_110);
lean_ctor_set(x_142, 15, x_111);
lean_ctor_set(x_142, 16, x_112);
lean_ctor_set(x_142, 17, x_113);
lean_ctor_set(x_142, 18, x_114);
lean_ctor_set(x_142, 19, x_115);
lean_ctor_set(x_142, 20, x_116);
lean_ctor_set(x_142, 21, x_117);
lean_ctor_set(x_142, 22, x_118);
lean_ctor_set(x_142, 23, x_119);
lean_ctor_set(x_142, 24, x_120);
lean_ctor_set(x_142, 25, x_121);
lean_ctor_set(x_142, 26, x_122);
lean_ctor_set(x_142, 27, x_123);
lean_ctor_set(x_142, 28, x_124);
lean_ctor_set(x_142, 29, x_125);
lean_ctor_set(x_142, 30, x_126);
lean_ctor_set(x_142, 31, x_127);
lean_ctor_set(x_142, 32, x_128);
lean_ctor_set(x_142, 33, x_129);
lean_ctor_set(x_142, 34, x_130);
lean_ctor_set(x_142, 35, x_131);
lean_ctor_set(x_142, 36, x_133);
lean_ctor_set(x_142, 37, x_134);
lean_ctor_set(x_142, 38, x_135);
lean_ctor_set(x_142, 39, x_136);
lean_ctor_set(x_142, 40, x_137);
lean_ctor_set(x_142, 41, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*42, x_132);
x_143 = lean_array_fset(x_140, x_47, x_142);
x_12 = x_65;
x_13 = x_76;
x_14 = x_66;
x_15 = x_71;
x_16 = x_64;
x_17 = x_81;
x_18 = x_78;
x_19 = x_77;
x_20 = x_72;
x_21 = x_67;
x_22 = x_69;
x_23 = x_70;
x_24 = x_74;
x_25 = x_68;
x_26 = x_79;
x_27 = x_75;
x_28 = x_85;
x_29 = x_86;
x_30 = x_83;
x_31 = x_48;
x_32 = x_80;
x_33 = x_82;
x_34 = x_73;
x_35 = x_143;
goto block_46;
}
}
}
else
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_57);
if (x_144 == 0)
{
return x_57;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_57, 0);
x_146 = lean_ctor_get(x_57, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_57);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
x_15 = lean_ctor_get(x_9, 2);
x_16 = lean_ctor_get(x_9, 3);
x_17 = lean_ctor_get(x_9, 4);
x_18 = lean_ctor_get(x_9, 5);
x_19 = lean_ctor_get(x_9, 6);
x_20 = lean_ctor_get(x_9, 7);
x_21 = lean_ctor_get(x_9, 8);
x_22 = lean_ctor_get(x_9, 9);
x_23 = lean_ctor_get(x_9, 10);
x_24 = lean_ctor_get(x_9, 11);
x_25 = lean_ctor_get(x_9, 12);
x_26 = lean_nat_dec_eq(x_16, x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_16, x_28);
lean_dec(x_16);
lean_ctor_set(x_9, 3, x_29);
x_30 = l_Lean_Grind_Linarith_Poly_findVarToSubst(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec_ref(x_9);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
lean_dec_ref(x_31);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_dec_ref(x_30);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_ctor_get(x_40, 0);
x_45 = l_Lean_Grind_Linarith_Poly_coeff(x_44, x_43);
lean_inc_ref(x_1);
x_46 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_45, x_43, x_40, x_42, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_43);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_46, 1);
lean_inc(x_58);
lean_dec_ref(x_46);
x_59 = lean_ctor_get(x_47, 0);
lean_inc(x_59);
lean_dec_ref(x_47);
x_1 = x_59;
x_11 = x_58;
goto _start;
}
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_1);
return x_46;
}
}
}
else
{
uint8_t x_61; 
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_61 = !lean_is_exclusive(x_30);
if (x_61 == 0)
{
return x_30;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_30, 0);
x_63 = lean_ctor_get(x_30, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_30);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; 
lean_free_object(x_9);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_1);
x_65 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_18, x_11);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; uint8_t x_81; 
x_66 = lean_ctor_get(x_9, 0);
x_67 = lean_ctor_get(x_9, 1);
x_68 = lean_ctor_get(x_9, 2);
x_69 = lean_ctor_get(x_9, 3);
x_70 = lean_ctor_get(x_9, 4);
x_71 = lean_ctor_get(x_9, 5);
x_72 = lean_ctor_get(x_9, 6);
x_73 = lean_ctor_get(x_9, 7);
x_74 = lean_ctor_get(x_9, 8);
x_75 = lean_ctor_get(x_9, 9);
x_76 = lean_ctor_get(x_9, 10);
x_77 = lean_ctor_get_uint8(x_9, sizeof(void*)*13);
x_78 = lean_ctor_get(x_9, 11);
x_79 = lean_ctor_get_uint8(x_9, sizeof(void*)*13 + 1);
x_80 = lean_ctor_get(x_9, 12);
lean_inc(x_80);
lean_inc(x_78);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_9);
x_81 = lean_nat_dec_eq(x_69, x_70);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_1, 0);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_add(x_69, x_83);
lean_dec(x_69);
x_85 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_85, 0, x_66);
lean_ctor_set(x_85, 1, x_67);
lean_ctor_set(x_85, 2, x_68);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_70);
lean_ctor_set(x_85, 5, x_71);
lean_ctor_set(x_85, 6, x_72);
lean_ctor_set(x_85, 7, x_73);
lean_ctor_set(x_85, 8, x_74);
lean_ctor_set(x_85, 9, x_75);
lean_ctor_set(x_85, 10, x_76);
lean_ctor_set(x_85, 11, x_78);
lean_ctor_set(x_85, 12, x_80);
lean_ctor_set_uint8(x_85, sizeof(void*)*13, x_77);
lean_ctor_set_uint8(x_85, sizeof(void*)*13 + 1, x_79);
x_86 = l_Lean_Grind_Linarith_Poly_findVarToSubst(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_85, x_10, x_11);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_85);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_1);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
lean_dec_ref(x_87);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
lean_dec_ref(x_86);
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_ctor_get(x_94, 0);
x_99 = l_Lean_Grind_Linarith_Poly_coeff(x_98, x_97);
lean_inc_ref(x_1);
x_100 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_99, x_97, x_94, x_96, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_85, x_10, x_95);
lean_dec(x_97);
lean_dec(x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
x_103 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_85, x_10, x_102);
lean_dec_ref(x_85);
lean_dec_ref(x_1);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
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
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
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
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_1);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
lean_dec_ref(x_100);
x_112 = lean_ctor_get(x_101, 0);
lean_inc(x_112);
lean_dec_ref(x_101);
x_1 = x_112;
x_9 = x_85;
x_11 = x_111;
goto _start;
}
}
else
{
lean_dec_ref(x_85);
lean_dec_ref(x_1);
return x_100;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_85);
lean_dec_ref(x_1);
x_114 = lean_ctor_get(x_86, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_86, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_116 = x_86;
} else {
 lean_dec_ref(x_86);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; 
lean_dec_ref(x_80);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_1);
x_118 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_71, x_11);
return x_118;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_1);
return x_2;
}
else
{
uint8_t x_10; 
lean_inc_ref(x_5);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
lean_ctor_set(x_2, 0, x_22);
return x_2;
}
else
{
size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_23 = 1;
x_24 = lean_usize_shift_left(x_23, x_4);
x_25 = lean_usize_sub(x_24, x_23);
x_26 = lean_usize_land(x_3, x_25);
x_27 = 5;
x_28 = lean_usize_sub(x_4, x_27);
x_29 = lean_array_fget(x_5, x_7);
x_30 = lean_box(0);
x_31 = lean_array_fset(x_5, x_7, x_30);
x_32 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(x_1, x_29, x_26, x_28);
x_33 = lean_array_fset(x_31, x_7, x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_usize_to_nat(x_3);
x_37 = lean_array_get_size(x_35);
x_38 = lean_nat_dec_lt(x_36, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec_ref(x_1);
return x_2;
}
else
{
uint8_t x_39; 
lean_inc_ref(x_35);
x_39 = !lean_is_exclusive(x_2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_2, 0);
lean_dec(x_40);
x_41 = lean_array_fget(x_35, x_36);
x_42 = lean_box(0);
x_43 = lean_array_fset(x_35, x_36, x_42);
x_44 = l_Lean_PersistentArray_push___redArg(x_41, x_1);
x_45 = lean_array_fset(x_43, x_36, x_44);
lean_dec(x_36);
lean_ctor_set(x_2, 0, x_45);
return x_2;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
x_46 = lean_array_fget(x_35, x_36);
x_47 = lean_box(0);
x_48 = lean_array_fset(x_35, x_36, x_47);
x_49 = l_Lean_PersistentArray_push___redArg(x_46, x_1);
x_50 = lean_array_fset(x_48, x_36, x_49);
lean_dec(x_36);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_10 = lean_nat_dec_le(x_9, x_4);
if (x_10 == 0)
{
size_t x_11; lean_object* x_12; 
x_11 = lean_usize_of_nat(x_4);
x_12 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(x_1, x_6, x_11, x_8);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_nat_sub(x_4, x_9);
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_7, x_13);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_7, x_13, x_17);
x_19 = l_Lean_PersistentArray_push___redArg(x_16, x_1);
x_20 = lean_array_fset(x_18, x_13, x_19);
lean_dec(x_13);
lean_ctor_set(x_3, 1, x_20);
return x_3;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get_usize(x_3, 4);
x_25 = lean_ctor_get(x_3, 3);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_26 = lean_nat_dec_le(x_25, x_4);
if (x_26 == 0)
{
size_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_usize_of_nat(x_4);
x_28 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(x_1, x_21, x_27, x_24);
x_29 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set_usize(x_29, 4, x_24);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_nat_sub(x_4, x_25);
x_31 = lean_array_get_size(x_22);
x_32 = lean_nat_dec_lt(x_30, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec_ref(x_1);
x_33 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_23);
lean_ctor_set(x_33, 3, x_25);
lean_ctor_set_usize(x_33, 4, x_24);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_array_fget(x_22, x_30);
x_35 = lean_box(0);
x_36 = lean_array_fset(x_22, x_30, x_35);
x_37 = l_Lean_PersistentArray_push___redArg(x_34, x_1);
x_38 = lean_array_fset(x_36, x_30, x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_23);
lean_ctor_set(x_39, 3, x_25);
lean_ctor_set_usize(x_39, 4, x_24);
return x_39;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_289; 
x_87 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0;
x_88 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_87, x_9, x_11);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1;
x_289 = lean_unbox(x_89);
lean_dec(x_89);
if (x_289 == 0)
{
x_193 = x_2;
x_194 = x_3;
x_195 = x_4;
x_196 = x_5;
x_197 = x_6;
x_198 = x_7;
x_199 = x_8;
x_200 = x_9;
x_201 = x_10;
x_202 = x_90;
goto block_288;
}
else
{
lean_object* x_290; 
x_290 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_90);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec_ref(x_290);
x_293 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_294 = l_Lean_MessageData_ofExpr(x_291);
x_295 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_293);
x_297 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_87, x_296, x_7, x_8, x_9, x_10, x_292);
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
lean_dec_ref(x_297);
x_193 = x_2;
x_194 = x_3;
x_195 = x_4;
x_196 = x_5;
x_197 = x_6;
x_198 = x_7;
x_199 = x_8;
x_200 = x_9;
x_201 = x_10;
x_202 = x_298;
goto block_288;
}
else
{
uint8_t x_299; 
lean_dec(x_91);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_299 = !lean_is_exclusive(x_290);
if (x_299 == 0)
{
return x_290;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_290, 0);
x_301 = lean_ctor_get(x_290, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_290);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
}
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_12);
x_24 = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(x_23, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
return x_24;
}
block_86:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_37);
lean_ctor_set(x_60, 2, x_38);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_30);
lean_ctor_set(x_61, 1, x_29);
lean_ctor_set(x_61, 2, x_39);
lean_ctor_set(x_61, 3, x_60);
x_62 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_62, 0, x_36);
lean_ctor_set(x_62, 1, x_49);
lean_ctor_set(x_62, 2, x_26);
lean_ctor_set(x_62, 3, x_35);
lean_ctor_set(x_62, 4, x_32);
lean_ctor_set(x_62, 5, x_53);
lean_ctor_set(x_62, 6, x_57);
lean_ctor_set(x_62, 7, x_28);
lean_ctor_set(x_62, 8, x_33);
lean_ctor_set(x_62, 9, x_56);
lean_ctor_set(x_62, 10, x_31);
lean_ctor_set(x_62, 11, x_41);
lean_ctor_set(x_62, 12, x_54);
lean_ctor_set(x_62, 13, x_46);
lean_ctor_set(x_62, 14, x_61);
lean_ctor_set(x_62, 15, x_47);
lean_ctor_set_uint8(x_62, sizeof(void*)*16, x_58);
x_63 = lean_st_ref_set(x_51, x_62, x_34);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(x_50, x_42, x_51, x_52, x_48, x_55, x_45, x_44, x_27, x_40, x_64);
lean_dec(x_40);
lean_dec_ref(x_27);
lean_dec(x_44);
lean_dec_ref(x_45);
lean_dec(x_55);
lean_dec_ref(x_48);
lean_dec(x_52);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
x_69 = 0;
x_70 = lean_unbox(x_67);
lean_dec(x_67);
x_71 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_20_(x_70, x_69);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_51);
lean_dec(x_43);
lean_dec(x_42);
x_72 = lean_box(0);
lean_ctor_set(x_65, 0, x_72);
return x_65;
}
else
{
lean_object* x_73; 
lean_free_object(x_65);
x_73 = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(x_43, x_42, x_51, x_68);
lean_dec(x_51);
lean_dec(x_42);
lean_dec(x_43);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_65, 0);
x_75 = lean_ctor_get(x_65, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_65);
x_76 = 0;
x_77 = lean_unbox(x_74);
lean_dec(x_74);
x_78 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_20_(x_77, x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_51);
lean_dec(x_43);
lean_dec(x_42);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
else
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(x_43, x_42, x_51, x_75);
lean_dec(x_51);
lean_dec(x_42);
lean_dec(x_43);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_51);
lean_dec(x_43);
lean_dec(x_42);
x_82 = !lean_is_exclusive(x_65);
if (x_82 == 0)
{
return x_65;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_65, 0);
x_84 = lean_ctor_get(x_65, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_65);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
block_192:
{
lean_object* x_106; 
x_106 = l_Lean_Grind_Linarith_Poly_updateOccs(x_93, x_96, x_97, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = lean_st_ref_take(x_97, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 14);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_110, 3);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec_ref(x_108);
x_113 = lean_ctor_get(x_109, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 1);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_109, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 3);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_109, 4);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_109, 5);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_109, 6);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_109, 7);
lean_inc_ref(x_120);
x_121 = lean_ctor_get_uint8(x_109, sizeof(void*)*16);
x_122 = lean_ctor_get(x_109, 8);
lean_inc(x_122);
x_123 = lean_ctor_get(x_109, 9);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_109, 10);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_109, 11);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_109, 12);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_109, 13);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_109, 15);
lean_inc_ref(x_128);
lean_dec(x_109);
x_129 = lean_ctor_get(x_110, 0);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_110, 1);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_110, 2);
lean_inc_ref(x_131);
lean_dec_ref(x_110);
x_132 = lean_ctor_get(x_111, 0);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_111, 1);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_111, 2);
lean_inc_ref(x_134);
lean_dec_ref(x_111);
x_135 = lean_array_get_size(x_132);
x_136 = lean_nat_dec_lt(x_96, x_135);
lean_dec(x_135);
if (x_136 == 0)
{
x_26 = x_115;
x_27 = x_103;
x_28 = x_120;
x_29 = x_130;
x_30 = x_129;
x_31 = x_124;
x_32 = x_117;
x_33 = x_122;
x_34 = x_112;
x_35 = x_116;
x_36 = x_113;
x_37 = x_133;
x_38 = x_134;
x_39 = x_131;
x_40 = x_104;
x_41 = x_125;
x_42 = x_96;
x_43 = x_94;
x_44 = x_102;
x_45 = x_101;
x_46 = x_127;
x_47 = x_128;
x_48 = x_99;
x_49 = x_114;
x_50 = x_95;
x_51 = x_97;
x_52 = x_98;
x_53 = x_118;
x_54 = x_126;
x_55 = x_100;
x_56 = x_123;
x_57 = x_119;
x_58 = x_121;
x_59 = x_132;
goto block_86;
}
else
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_array_fget(x_132, x_96);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_137, 34);
x_140 = lean_box(0);
x_141 = lean_array_fset(x_132, x_96, x_140);
lean_inc_ref(x_95);
x_142 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(x_95, x_92, x_139, x_94);
lean_ctor_set(x_137, 34, x_142);
x_143 = lean_array_fset(x_141, x_96, x_137);
x_26 = x_115;
x_27 = x_103;
x_28 = x_120;
x_29 = x_130;
x_30 = x_129;
x_31 = x_124;
x_32 = x_117;
x_33 = x_122;
x_34 = x_112;
x_35 = x_116;
x_36 = x_113;
x_37 = x_133;
x_38 = x_134;
x_39 = x_131;
x_40 = x_104;
x_41 = x_125;
x_42 = x_96;
x_43 = x_94;
x_44 = x_102;
x_45 = x_101;
x_46 = x_127;
x_47 = x_128;
x_48 = x_99;
x_49 = x_114;
x_50 = x_95;
x_51 = x_97;
x_52 = x_98;
x_53 = x_118;
x_54 = x_126;
x_55 = x_100;
x_56 = x_123;
x_57 = x_119;
x_58 = x_121;
x_59 = x_143;
goto block_86;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_144 = lean_ctor_get(x_137, 0);
x_145 = lean_ctor_get(x_137, 1);
x_146 = lean_ctor_get(x_137, 2);
x_147 = lean_ctor_get(x_137, 3);
x_148 = lean_ctor_get(x_137, 4);
x_149 = lean_ctor_get(x_137, 5);
x_150 = lean_ctor_get(x_137, 6);
x_151 = lean_ctor_get(x_137, 7);
x_152 = lean_ctor_get(x_137, 8);
x_153 = lean_ctor_get(x_137, 9);
x_154 = lean_ctor_get(x_137, 10);
x_155 = lean_ctor_get(x_137, 11);
x_156 = lean_ctor_get(x_137, 12);
x_157 = lean_ctor_get(x_137, 13);
x_158 = lean_ctor_get(x_137, 14);
x_159 = lean_ctor_get(x_137, 15);
x_160 = lean_ctor_get(x_137, 16);
x_161 = lean_ctor_get(x_137, 17);
x_162 = lean_ctor_get(x_137, 18);
x_163 = lean_ctor_get(x_137, 19);
x_164 = lean_ctor_get(x_137, 20);
x_165 = lean_ctor_get(x_137, 21);
x_166 = lean_ctor_get(x_137, 22);
x_167 = lean_ctor_get(x_137, 23);
x_168 = lean_ctor_get(x_137, 24);
x_169 = lean_ctor_get(x_137, 25);
x_170 = lean_ctor_get(x_137, 26);
x_171 = lean_ctor_get(x_137, 27);
x_172 = lean_ctor_get(x_137, 28);
x_173 = lean_ctor_get(x_137, 29);
x_174 = lean_ctor_get(x_137, 30);
x_175 = lean_ctor_get(x_137, 31);
x_176 = lean_ctor_get(x_137, 32);
x_177 = lean_ctor_get(x_137, 33);
x_178 = lean_ctor_get(x_137, 34);
x_179 = lean_ctor_get(x_137, 35);
x_180 = lean_ctor_get_uint8(x_137, sizeof(void*)*42);
x_181 = lean_ctor_get(x_137, 36);
x_182 = lean_ctor_get(x_137, 37);
x_183 = lean_ctor_get(x_137, 38);
x_184 = lean_ctor_get(x_137, 39);
x_185 = lean_ctor_get(x_137, 40);
x_186 = lean_ctor_get(x_137, 41);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_137);
x_187 = lean_box(0);
x_188 = lean_array_fset(x_132, x_96, x_187);
lean_inc_ref(x_95);
x_189 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(x_95, x_92, x_178, x_94);
x_190 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_190, 0, x_144);
lean_ctor_set(x_190, 1, x_145);
lean_ctor_set(x_190, 2, x_146);
lean_ctor_set(x_190, 3, x_147);
lean_ctor_set(x_190, 4, x_148);
lean_ctor_set(x_190, 5, x_149);
lean_ctor_set(x_190, 6, x_150);
lean_ctor_set(x_190, 7, x_151);
lean_ctor_set(x_190, 8, x_152);
lean_ctor_set(x_190, 9, x_153);
lean_ctor_set(x_190, 10, x_154);
lean_ctor_set(x_190, 11, x_155);
lean_ctor_set(x_190, 12, x_156);
lean_ctor_set(x_190, 13, x_157);
lean_ctor_set(x_190, 14, x_158);
lean_ctor_set(x_190, 15, x_159);
lean_ctor_set(x_190, 16, x_160);
lean_ctor_set(x_190, 17, x_161);
lean_ctor_set(x_190, 18, x_162);
lean_ctor_set(x_190, 19, x_163);
lean_ctor_set(x_190, 20, x_164);
lean_ctor_set(x_190, 21, x_165);
lean_ctor_set(x_190, 22, x_166);
lean_ctor_set(x_190, 23, x_167);
lean_ctor_set(x_190, 24, x_168);
lean_ctor_set(x_190, 25, x_169);
lean_ctor_set(x_190, 26, x_170);
lean_ctor_set(x_190, 27, x_171);
lean_ctor_set(x_190, 28, x_172);
lean_ctor_set(x_190, 29, x_173);
lean_ctor_set(x_190, 30, x_174);
lean_ctor_set(x_190, 31, x_175);
lean_ctor_set(x_190, 32, x_176);
lean_ctor_set(x_190, 33, x_177);
lean_ctor_set(x_190, 34, x_189);
lean_ctor_set(x_190, 35, x_179);
lean_ctor_set(x_190, 36, x_181);
lean_ctor_set(x_190, 37, x_182);
lean_ctor_set(x_190, 38, x_183);
lean_ctor_set(x_190, 39, x_184);
lean_ctor_set(x_190, 40, x_185);
lean_ctor_set(x_190, 41, x_186);
lean_ctor_set_uint8(x_190, sizeof(void*)*42, x_180);
x_191 = lean_array_fset(x_188, x_96, x_190);
x_26 = x_115;
x_27 = x_103;
x_28 = x_120;
x_29 = x_130;
x_30 = x_129;
x_31 = x_124;
x_32 = x_117;
x_33 = x_122;
x_34 = x_112;
x_35 = x_116;
x_36 = x_113;
x_37 = x_133;
x_38 = x_134;
x_39 = x_131;
x_40 = x_104;
x_41 = x_125;
x_42 = x_96;
x_43 = x_94;
x_44 = x_102;
x_45 = x_101;
x_46 = x_127;
x_47 = x_128;
x_48 = x_99;
x_49 = x_114;
x_50 = x_95;
x_51 = x_97;
x_52 = x_98;
x_53 = x_118;
x_54 = x_126;
x_55 = x_100;
x_56 = x_123;
x_57 = x_119;
x_58 = x_121;
x_59 = x_191;
goto block_86;
}
}
}
else
{
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
return x_106;
}
}
block_288:
{
lean_object* x_203; 
lean_inc_ref(x_200);
x_203 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(x_1, x_193, x_194, x_195, x_196, x_197, x_198, x_199, x_200, x_201, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_205; 
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_91);
x_205 = !lean_is_exclusive(x_203);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_203, 0);
lean_dec(x_206);
x_207 = lean_box(0);
lean_ctor_set(x_203, 0, x_207);
return x_203;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_203, 1);
lean_inc(x_208);
lean_dec(x_203);
x_209 = lean_box(0);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_204, 0);
lean_inc(x_211);
lean_dec_ref(x_204);
x_212 = lean_ctor_get(x_211, 0);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_213 = lean_ctor_get(x_203, 1);
lean_inc(x_213);
lean_dec_ref(x_203);
x_214 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3;
x_215 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_214, x_200, x_213);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_unbox(x_216);
lean_dec(x_216);
if (x_217 == 0)
{
lean_object* x_218; 
lean_dec(x_91);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_dec_ref(x_215);
x_12 = x_211;
x_13 = x_193;
x_14 = x_194;
x_15 = x_195;
x_16 = x_196;
x_17 = x_197;
x_18 = x_198;
x_19 = x_199;
x_20 = x_200;
x_21 = x_201;
x_22 = x_218;
goto block_25;
}
else
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_215);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_215, 1);
x_221 = lean_ctor_get(x_215, 0);
lean_dec(x_221);
x_222 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_211, x_193, x_194, x_195, x_196, x_197, x_198, x_199, x_200, x_201, x_220);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec_ref(x_222);
x_225 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_226 = l_Lean_MessageData_ofExpr(x_223);
lean_ctor_set_tag(x_215, 7);
lean_ctor_set(x_215, 1, x_226);
lean_ctor_set(x_215, 0, x_225);
if (lean_is_scalar(x_91)) {
 x_227 = lean_alloc_ctor(7, 2, 0);
} else {
 x_227 = x_91;
 lean_ctor_set_tag(x_227, 7);
}
lean_ctor_set(x_227, 0, x_215);
lean_ctor_set(x_227, 1, x_225);
x_228 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_214, x_227, x_198, x_199, x_200, x_201, x_224);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec_ref(x_228);
x_12 = x_211;
x_13 = x_193;
x_14 = x_194;
x_15 = x_195;
x_16 = x_196;
x_17 = x_197;
x_18 = x_198;
x_19 = x_199;
x_20 = x_200;
x_21 = x_201;
x_22 = x_229;
goto block_25;
}
else
{
uint8_t x_230; 
lean_free_object(x_215);
lean_dec(x_211);
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_91);
x_230 = !lean_is_exclusive(x_222);
if (x_230 == 0)
{
return x_222;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_222, 0);
x_232 = lean_ctor_get(x_222, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_222);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_215, 1);
lean_inc(x_234);
lean_dec(x_215);
x_235 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_211, x_193, x_194, x_195, x_196, x_197, x_198, x_199, x_200, x_201, x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec_ref(x_235);
x_238 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_239 = l_Lean_MessageData_ofExpr(x_236);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
if (lean_is_scalar(x_91)) {
 x_241 = lean_alloc_ctor(7, 2, 0);
} else {
 x_241 = x_91;
 lean_ctor_set_tag(x_241, 7);
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_238);
x_242 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_214, x_241, x_198, x_199, x_200, x_201, x_237);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec_ref(x_242);
x_12 = x_211;
x_13 = x_193;
x_14 = x_194;
x_15 = x_195;
x_16 = x_196;
x_17 = x_197;
x_18 = x_198;
x_19 = x_199;
x_20 = x_200;
x_21 = x_201;
x_22 = x_243;
goto block_25;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_211);
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_91);
x_244 = lean_ctor_get(x_235, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_235, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_246 = x_235;
} else {
 lean_dec_ref(x_235);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
lean_inc_ref(x_212);
x_248 = lean_ctor_get(x_203, 1);
lean_inc(x_248);
lean_dec_ref(x_203);
x_249 = lean_ctor_get(x_212, 1);
lean_inc(x_249);
x_250 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5;
x_251 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_250, x_200, x_248);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_unbox(x_252);
lean_dec(x_252);
if (x_253 == 0)
{
lean_object* x_254; 
lean_dec(x_91);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec_ref(x_251);
x_93 = x_212;
x_94 = x_249;
x_95 = x_211;
x_96 = x_193;
x_97 = x_194;
x_98 = x_195;
x_99 = x_196;
x_100 = x_197;
x_101 = x_198;
x_102 = x_199;
x_103 = x_200;
x_104 = x_201;
x_105 = x_254;
goto block_192;
}
else
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_251);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_251, 1);
x_257 = lean_ctor_get(x_251, 0);
lean_dec(x_257);
x_258 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_211, x_193, x_194, x_195, x_196, x_197, x_198, x_199, x_200, x_201, x_256);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec_ref(x_258);
x_261 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_262 = l_Lean_MessageData_ofExpr(x_259);
lean_ctor_set_tag(x_251, 7);
lean_ctor_set(x_251, 1, x_262);
lean_ctor_set(x_251, 0, x_261);
if (lean_is_scalar(x_91)) {
 x_263 = lean_alloc_ctor(7, 2, 0);
} else {
 x_263 = x_91;
 lean_ctor_set_tag(x_263, 7);
}
lean_ctor_set(x_263, 0, x_251);
lean_ctor_set(x_263, 1, x_261);
x_264 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_250, x_263, x_198, x_199, x_200, x_201, x_260);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec_ref(x_264);
x_93 = x_212;
x_94 = x_249;
x_95 = x_211;
x_96 = x_193;
x_97 = x_194;
x_98 = x_195;
x_99 = x_196;
x_100 = x_197;
x_101 = x_198;
x_102 = x_199;
x_103 = x_200;
x_104 = x_201;
x_105 = x_265;
goto block_192;
}
else
{
uint8_t x_266; 
lean_free_object(x_251);
lean_dec(x_249);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_91);
x_266 = !lean_is_exclusive(x_258);
if (x_266 == 0)
{
return x_258;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_258, 0);
x_268 = lean_ctor_get(x_258, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_258);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_251, 1);
lean_inc(x_270);
lean_dec(x_251);
x_271 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_211, x_193, x_194, x_195, x_196, x_197, x_198, x_199, x_200, x_201, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec_ref(x_271);
x_274 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_275 = l_Lean_MessageData_ofExpr(x_272);
x_276 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
if (lean_is_scalar(x_91)) {
 x_277 = lean_alloc_ctor(7, 2, 0);
} else {
 x_277 = x_91;
 lean_ctor_set_tag(x_277, 7);
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_274);
x_278 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_250, x_277, x_198, x_199, x_200, x_201, x_273);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec_ref(x_278);
x_93 = x_212;
x_94 = x_249;
x_95 = x_211;
x_96 = x_193;
x_97 = x_194;
x_98 = x_195;
x_99 = x_196;
x_100 = x_197;
x_101 = x_198;
x_102 = x_199;
x_103 = x_200;
x_104 = x_201;
x_105 = x_279;
goto block_192;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_249);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_91);
x_280 = lean_ctor_get(x_271, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_271, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_282 = x_271;
} else {
 lean_dec_ref(x_271);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
}
}
}
}
else
{
uint8_t x_284; 
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_91);
x_284 = !lean_is_exclusive(x_203);
if (x_284 == 0)
{
return x_203;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_203, 0);
x_286 = lean_ctor_get(x_203, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_203);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_array_uget(x_5, x_7);
lean_inc(x_11);
lean_inc(x_2);
x_14 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_13, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_11);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_4);
x_17 = 1;
x_18 = lean_usize_add(x_7, x_17);
x_7 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_array_uget(x_5, x_7);
lean_inc(x_20);
lean_inc(x_2);
x_22 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_21, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_2);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_20);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
lean_inc(x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_7, x_27);
x_7 = x_28;
x_8 = x_26;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_array_uget(x_4, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = l_Lean_Grind_Linarith_Poly_coeff(x_22, x_2);
lean_dec(x_22);
lean_inc(x_3);
x_24 = lean_nat_to_int(x_3);
x_25 = lean_int_dec_eq(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_23);
x_26 = lean_array_push(x_20, x_7);
lean_ctor_set(x_16, 1, x_26);
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
lean_free_object(x_7);
x_27 = l_Lean_PersistentArray_push___redArg(x_19, x_21);
lean_ctor_set(x_16, 0, x_27);
x_8 = x_16;
goto block_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_array_uget(x_4, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = l_Lean_Grind_Linarith_Poly_coeff(x_31, x_2);
lean_dec(x_31);
lean_inc(x_3);
x_33 = lean_nat_to_int(x_3);
x_34 = lean_int_dec_eq(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_32);
x_35 = lean_array_push(x_29, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_8 = x_36;
goto block_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_free_object(x_7);
x_37 = l_Lean_PersistentArray_push___redArg(x_28, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
x_8 = x_38;
goto block_13;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_dec(x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_array_uget(x_4, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = l_Lean_Grind_Linarith_Poly_coeff(x_44, x_2);
lean_dec(x_44);
lean_inc(x_3);
x_46 = lean_nat_to_int(x_3);
x_47 = lean_int_dec_eq(x_45, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_43);
x_49 = lean_array_push(x_41, x_48);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_42;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_8 = x_50;
goto block_13;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_51 = l_Lean_PersistentArray_push___redArg(x_40, x_43);
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_8 = x_52;
goto block_13;
}
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_6, x_10);
x_6 = x_11;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_array_uget(x_4, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = l_Lean_Grind_Linarith_Poly_coeff(x_22, x_1);
lean_dec(x_22);
lean_inc(x_2);
x_24 = lean_nat_to_int(x_2);
x_25 = lean_int_dec_eq(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_23);
x_26 = lean_array_push(x_20, x_7);
lean_ctor_set(x_16, 1, x_26);
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
lean_free_object(x_7);
x_27 = l_Lean_PersistentArray_push___redArg(x_19, x_21);
lean_ctor_set(x_16, 0, x_27);
x_8 = x_16;
goto block_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_array_uget(x_4, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = l_Lean_Grind_Linarith_Poly_coeff(x_31, x_1);
lean_dec(x_31);
lean_inc(x_2);
x_33 = lean_nat_to_int(x_2);
x_34 = lean_int_dec_eq(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_32);
x_35 = lean_array_push(x_29, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_8 = x_36;
goto block_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_free_object(x_7);
x_37 = l_Lean_PersistentArray_push___redArg(x_28, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
x_8 = x_38;
goto block_13;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_dec(x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_array_uget(x_4, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = l_Lean_Grind_Linarith_Poly_coeff(x_44, x_1);
lean_dec(x_44);
lean_inc(x_2);
x_46 = lean_nat_to_int(x_2);
x_47 = lean_int_dec_eq(x_45, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_43);
x_49 = lean_array_push(x_41, x_48);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_42;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_8 = x_50;
goto block_13;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_51 = l_Lean_PersistentArray_push___redArg(x_40, x_43);
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_8 = x_52;
goto block_13;
}
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_6, x_10);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1_spec__1(x_3, x_1, x_2, x_4, x_5, x_11, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_array_size(x_7);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_8, x_7, x_10, x_11, x_9);
lean_dec_ref(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_12);
lean_free_object(x_4);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_array_size(x_16);
x_20 = 0;
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_17, x_16, x_19, x_20, x_18);
lean_dec_ref(x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec_ref(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
x_30 = lean_array_size(x_27);
x_31 = 0;
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_28, x_27, x_30, x_31, x_29);
lean_dec_ref(x_27);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
lean_ctor_set(x_4, 0, x_34);
return x_4;
}
else
{
lean_object* x_35; 
lean_dec_ref(x_32);
lean_free_object(x_4);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec_ref(x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
lean_dec(x_4);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
x_39 = lean_array_size(x_36);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_37, x_36, x_39, x_40, x_38);
lean_dec_ref(x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec_ref(x_41);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec_ref(x_42);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_array_uget(x_4, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = l_Lean_Grind_Linarith_Poly_coeff(x_22, x_2);
lean_dec(x_22);
lean_inc(x_3);
x_24 = lean_nat_to_int(x_3);
x_25 = lean_int_dec_eq(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_23);
x_26 = lean_array_push(x_20, x_7);
lean_ctor_set(x_16, 1, x_26);
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
lean_free_object(x_7);
x_27 = l_Lean_PersistentArray_push___redArg(x_19, x_21);
lean_ctor_set(x_16, 0, x_27);
x_8 = x_16;
goto block_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_array_uget(x_4, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = l_Lean_Grind_Linarith_Poly_coeff(x_31, x_2);
lean_dec(x_31);
lean_inc(x_3);
x_33 = lean_nat_to_int(x_3);
x_34 = lean_int_dec_eq(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_32);
x_35 = lean_array_push(x_29, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_8 = x_36;
goto block_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_free_object(x_7);
x_37 = l_Lean_PersistentArray_push___redArg(x_28, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
x_8 = x_38;
goto block_13;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_dec(x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_array_uget(x_4, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = l_Lean_Grind_Linarith_Poly_coeff(x_44, x_2);
lean_dec(x_44);
lean_inc(x_3);
x_46 = lean_nat_to_int(x_3);
x_47 = lean_int_dec_eq(x_45, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_43);
x_49 = lean_array_push(x_41, x_48);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_42;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_8 = x_50;
goto block_13;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_51 = l_Lean_PersistentArray_push___redArg(x_40, x_43);
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_8 = x_52;
goto block_13;
}
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_6, x_10);
x_6 = x_11;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_array_uget(x_4, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = l_Lean_Grind_Linarith_Poly_coeff(x_22, x_1);
lean_dec(x_22);
lean_inc(x_2);
x_24 = lean_nat_to_int(x_2);
x_25 = lean_int_dec_eq(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_23);
x_26 = lean_array_push(x_20, x_7);
lean_ctor_set(x_16, 1, x_26);
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
lean_free_object(x_7);
x_27 = l_Lean_PersistentArray_push___redArg(x_19, x_21);
lean_ctor_set(x_16, 0, x_27);
x_8 = x_16;
goto block_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_array_uget(x_4, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = l_Lean_Grind_Linarith_Poly_coeff(x_31, x_1);
lean_dec(x_31);
lean_inc(x_2);
x_33 = lean_nat_to_int(x_2);
x_34 = lean_int_dec_eq(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_32);
x_35 = lean_array_push(x_29, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_8 = x_36;
goto block_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_free_object(x_7);
x_37 = l_Lean_PersistentArray_push___redArg(x_28, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
x_8 = x_38;
goto block_13;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_dec(x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_array_uget(x_4, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = l_Lean_Grind_Linarith_Poly_coeff(x_44, x_1);
lean_dec(x_44);
lean_inc(x_2);
x_46 = lean_nat_to_int(x_2);
x_47 = lean_int_dec_eq(x_45, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_43);
x_49 = lean_array_push(x_41, x_48);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_42;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_8 = x_50;
goto block_13;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_51 = l_Lean_PersistentArray_push___redArg(x_40, x_43);
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_8 = x_52;
goto block_13;
}
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_6, x_10);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__4_spec__4(x_3, x_1, x_2, x_4, x_5, x_11, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
lean_inc_ref(x_4);
lean_inc(x_2);
x_7 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0(x_1, x_2, x_4, x_5, x_4);
lean_dec_ref(x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_array_size(x_6);
x_13 = 0;
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__4(x_1, x_2, x_10, x_6, x_12, x_13, x_11);
lean_dec_ref(x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__4;
x_5 = l_Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(x_1, x_3, x_2, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__4_spec__4(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__4(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forIn___at___Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; uint8_t x_26; 
x_26 = lean_usize_dec_lt(x_8, x_7);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_dec_ref(x_9);
x_28 = lean_array_uget(x_6, x_8);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc_ref(x_3);
x_32 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_1, x_2, x_3, x_30, x_31, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_free_object(x_28);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_31, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_34);
lean_dec(x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc_ref(x_4);
x_20 = x_4;
x_21 = x_36;
goto block_25;
}
else
{
uint8_t x_37; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_31);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec_ref(x_32);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec_ref(x_33);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_43 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_42, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_free_object(x_28);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec_ref(x_45);
lean_inc_ref(x_4);
x_20 = x_4;
x_21 = x_48;
goto block_25;
}
else
{
uint8_t x_49; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_45, 0);
lean_dec(x_50);
x_51 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 0, x_51);
lean_ctor_set(x_45, 0, x_28);
return x_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 0, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_28);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_free_object(x_28);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_55 = !lean_is_exclusive(x_45);
if (x_55 == 0)
{
return x_45;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_45, 0);
x_57 = lean_ctor_get(x_45, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_45);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_free_object(x_28);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_59 = !lean_is_exclusive(x_43);
if (x_59 == 0)
{
return x_43;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_43, 0);
x_61 = lean_ctor_get(x_43, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_43);
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
lean_free_object(x_28);
lean_dec(x_31);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
return x_32;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_32, 0);
x_65 = lean_ctor_get(x_32, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_32);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_28, 0);
x_68 = lean_ctor_get(x_28, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_28);
lean_inc(x_68);
lean_inc_ref(x_3);
x_69 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_1, x_2, x_3, x_67, x_68, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_68, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_71);
lean_dec(x_68);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec_ref(x_72);
lean_inc_ref(x_4);
x_20 = x_4;
x_21 = x_73;
goto block_25;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
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
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_68);
x_78 = lean_ctor_get(x_69, 1);
lean_inc(x_78);
lean_dec_ref(x_69);
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
lean_dec_ref(x_70);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_80 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_79, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec_ref(x_82);
lean_inc_ref(x_4);
x_20 = x_4;
x_21 = x_85;
goto block_25;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_87 = x_82;
} else {
 lean_dec_ref(x_82);
 x_87 = lean_box(0);
}
x_88 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_5);
if (lean_is_scalar(x_87)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_87;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_91 = lean_ctor_get(x_82, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_93 = x_82;
} else {
 lean_dec_ref(x_82);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_95 = lean_ctor_get(x_80, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_80, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_97 = x_80;
} else {
 lean_dec_ref(x_80);
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
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_68);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_99 = lean_ctor_get(x_69, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_69, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_101 = x_69;
} else {
 lean_dec_ref(x_69);
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
block_25:
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = lean_usize_add(x_8, x_22);
x_8 = x_23;
x_9 = x_20;
x_19 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_66; 
x_66 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec_ref(x_66);
x_70 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec_ref(x_70);
x_162 = lean_ctor_get(x_71, 34);
lean_inc_ref(x_162);
lean_dec(x_71);
x_163 = lean_ctor_get(x_162, 2);
x_164 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1;
x_165 = lean_nat_dec_lt(x_4, x_163);
if (x_165 == 0)
{
lean_object* x_166; 
lean_dec_ref(x_162);
x_166 = l_outOfBounds___redArg(x_164);
x_73 = x_166;
goto block_161;
}
else
{
lean_object* x_167; 
x_167 = l_Lean_PersistentArray_get_x21___redArg(x_164, x_162, x_4);
x_73 = x_167;
goto block_161;
}
block_161:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_74 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(x_2, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = lean_st_ref_take(x_6, x_72);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 14);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_79, 3);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec_ref(x_77);
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 1);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_78, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 3);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_78, 4);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_78, 5);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_78, 6);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_78, 7);
lean_inc_ref(x_89);
x_90 = lean_ctor_get_uint8(x_78, sizeof(void*)*16);
x_91 = lean_ctor_get(x_78, 8);
lean_inc(x_91);
x_92 = lean_ctor_get(x_78, 9);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_78, 10);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_78, 11);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_78, 12);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_78, 13);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_78, 15);
lean_inc_ref(x_97);
lean_dec(x_78);
x_98 = lean_ctor_get(x_79, 0);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_79, 1);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_79, 2);
lean_inc_ref(x_100);
lean_dec_ref(x_79);
x_101 = lean_ctor_get(x_80, 0);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_80, 1);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_80, 2);
lean_inc_ref(x_103);
lean_dec_ref(x_80);
x_104 = lean_array_get_size(x_101);
x_105 = lean_nat_dec_lt(x_5, x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_dec(x_75);
x_15 = x_96;
x_16 = x_76;
x_17 = x_98;
x_18 = x_86;
x_19 = x_95;
x_20 = x_90;
x_21 = x_94;
x_22 = x_83;
x_23 = x_84;
x_24 = x_82;
x_25 = x_92;
x_26 = x_91;
x_27 = x_87;
x_28 = x_97;
x_29 = x_85;
x_30 = x_81;
x_31 = x_100;
x_32 = x_99;
x_33 = x_102;
x_34 = x_103;
x_35 = x_88;
x_36 = x_89;
x_37 = x_93;
x_38 = x_101;
goto block_65;
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_array_fget(x_101, x_5);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_106, 34);
x_109 = lean_box(0);
x_110 = lean_array_fset(x_101, x_5, x_109);
x_111 = l_Lean_PersistentArray_set___redArg(x_108, x_4, x_75);
lean_ctor_set(x_106, 34, x_111);
x_112 = lean_array_fset(x_110, x_5, x_106);
x_15 = x_96;
x_16 = x_76;
x_17 = x_98;
x_18 = x_86;
x_19 = x_95;
x_20 = x_90;
x_21 = x_94;
x_22 = x_83;
x_23 = x_84;
x_24 = x_82;
x_25 = x_92;
x_26 = x_91;
x_27 = x_87;
x_28 = x_97;
x_29 = x_85;
x_30 = x_81;
x_31 = x_100;
x_32 = x_99;
x_33 = x_102;
x_34 = x_103;
x_35 = x_88;
x_36 = x_89;
x_37 = x_93;
x_38 = x_112;
goto block_65;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_113 = lean_ctor_get(x_106, 0);
x_114 = lean_ctor_get(x_106, 1);
x_115 = lean_ctor_get(x_106, 2);
x_116 = lean_ctor_get(x_106, 3);
x_117 = lean_ctor_get(x_106, 4);
x_118 = lean_ctor_get(x_106, 5);
x_119 = lean_ctor_get(x_106, 6);
x_120 = lean_ctor_get(x_106, 7);
x_121 = lean_ctor_get(x_106, 8);
x_122 = lean_ctor_get(x_106, 9);
x_123 = lean_ctor_get(x_106, 10);
x_124 = lean_ctor_get(x_106, 11);
x_125 = lean_ctor_get(x_106, 12);
x_126 = lean_ctor_get(x_106, 13);
x_127 = lean_ctor_get(x_106, 14);
x_128 = lean_ctor_get(x_106, 15);
x_129 = lean_ctor_get(x_106, 16);
x_130 = lean_ctor_get(x_106, 17);
x_131 = lean_ctor_get(x_106, 18);
x_132 = lean_ctor_get(x_106, 19);
x_133 = lean_ctor_get(x_106, 20);
x_134 = lean_ctor_get(x_106, 21);
x_135 = lean_ctor_get(x_106, 22);
x_136 = lean_ctor_get(x_106, 23);
x_137 = lean_ctor_get(x_106, 24);
x_138 = lean_ctor_get(x_106, 25);
x_139 = lean_ctor_get(x_106, 26);
x_140 = lean_ctor_get(x_106, 27);
x_141 = lean_ctor_get(x_106, 28);
x_142 = lean_ctor_get(x_106, 29);
x_143 = lean_ctor_get(x_106, 30);
x_144 = lean_ctor_get(x_106, 31);
x_145 = lean_ctor_get(x_106, 32);
x_146 = lean_ctor_get(x_106, 33);
x_147 = lean_ctor_get(x_106, 34);
x_148 = lean_ctor_get(x_106, 35);
x_149 = lean_ctor_get_uint8(x_106, sizeof(void*)*42);
x_150 = lean_ctor_get(x_106, 36);
x_151 = lean_ctor_get(x_106, 37);
x_152 = lean_ctor_get(x_106, 38);
x_153 = lean_ctor_get(x_106, 39);
x_154 = lean_ctor_get(x_106, 40);
x_155 = lean_ctor_get(x_106, 41);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_106);
x_156 = lean_box(0);
x_157 = lean_array_fset(x_101, x_5, x_156);
x_158 = l_Lean_PersistentArray_set___redArg(x_147, x_4, x_75);
x_159 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_159, 0, x_113);
lean_ctor_set(x_159, 1, x_114);
lean_ctor_set(x_159, 2, x_115);
lean_ctor_set(x_159, 3, x_116);
lean_ctor_set(x_159, 4, x_117);
lean_ctor_set(x_159, 5, x_118);
lean_ctor_set(x_159, 6, x_119);
lean_ctor_set(x_159, 7, x_120);
lean_ctor_set(x_159, 8, x_121);
lean_ctor_set(x_159, 9, x_122);
lean_ctor_set(x_159, 10, x_123);
lean_ctor_set(x_159, 11, x_124);
lean_ctor_set(x_159, 12, x_125);
lean_ctor_set(x_159, 13, x_126);
lean_ctor_set(x_159, 14, x_127);
lean_ctor_set(x_159, 15, x_128);
lean_ctor_set(x_159, 16, x_129);
lean_ctor_set(x_159, 17, x_130);
lean_ctor_set(x_159, 18, x_131);
lean_ctor_set(x_159, 19, x_132);
lean_ctor_set(x_159, 20, x_133);
lean_ctor_set(x_159, 21, x_134);
lean_ctor_set(x_159, 22, x_135);
lean_ctor_set(x_159, 23, x_136);
lean_ctor_set(x_159, 24, x_137);
lean_ctor_set(x_159, 25, x_138);
lean_ctor_set(x_159, 26, x_139);
lean_ctor_set(x_159, 27, x_140);
lean_ctor_set(x_159, 28, x_141);
lean_ctor_set(x_159, 29, x_142);
lean_ctor_set(x_159, 30, x_143);
lean_ctor_set(x_159, 31, x_144);
lean_ctor_set(x_159, 32, x_145);
lean_ctor_set(x_159, 33, x_146);
lean_ctor_set(x_159, 34, x_158);
lean_ctor_set(x_159, 35, x_148);
lean_ctor_set(x_159, 36, x_150);
lean_ctor_set(x_159, 37, x_151);
lean_ctor_set(x_159, 38, x_152);
lean_ctor_set(x_159, 39, x_153);
lean_ctor_set(x_159, 40, x_154);
lean_ctor_set(x_159, 41, x_155);
lean_ctor_set_uint8(x_159, sizeof(void*)*42, x_149);
x_160 = lean_array_fset(x_157, x_5, x_159);
x_15 = x_96;
x_16 = x_76;
x_17 = x_98;
x_18 = x_86;
x_19 = x_95;
x_20 = x_90;
x_21 = x_94;
x_22 = x_83;
x_23 = x_84;
x_24 = x_82;
x_25 = x_92;
x_26 = x_91;
x_27 = x_87;
x_28 = x_97;
x_29 = x_85;
x_30 = x_81;
x_31 = x_100;
x_32 = x_99;
x_33 = x_102;
x_34 = x_103;
x_35 = x_88;
x_36 = x_89;
x_37 = x_93;
x_38 = x_160;
goto block_65;
}
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_168 = !lean_is_exclusive(x_70);
if (x_168 == 0)
{
return x_70;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_70, 0);
x_170 = lean_ctor_get(x_70, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_70);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_172 = !lean_is_exclusive(x_66);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_66, 0);
lean_dec(x_173);
x_174 = lean_box(0);
lean_ctor_set(x_66, 0, x_174);
return x_66;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_66, 1);
lean_inc(x_175);
lean_dec(x_66);
x_176 = lean_box(0);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_178 = !lean_is_exclusive(x_66);
if (x_178 == 0)
{
return x_66;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_66, 0);
x_180 = lean_ctor_get(x_66, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_66);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
block_65:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_31);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_41, 0, x_24);
lean_ctor_set(x_41, 1, x_22);
lean_ctor_set(x_41, 2, x_23);
lean_ctor_set(x_41, 3, x_29);
lean_ctor_set(x_41, 4, x_18);
lean_ctor_set(x_41, 5, x_27);
lean_ctor_set(x_41, 6, x_35);
lean_ctor_set(x_41, 7, x_36);
lean_ctor_set(x_41, 8, x_26);
lean_ctor_set(x_41, 9, x_25);
lean_ctor_set(x_41, 10, x_37);
lean_ctor_set(x_41, 11, x_21);
lean_ctor_set(x_41, 12, x_19);
lean_ctor_set(x_41, 13, x_15);
lean_ctor_set(x_41, 14, x_40);
lean_ctor_set(x_41, 15, x_28);
lean_ctor_set_uint8(x_41, sizeof(void*)*16, x_20);
x_42 = lean_st_ref_set(x_6, x_41, x_30);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_box(0);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0;
x_46 = lean_array_size(x_16);
x_47 = 0;
x_48 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(x_1, x_2, x_3, x_45, x_44, x_16, x_46, x_47, x_45, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_43);
lean_dec_ref(x_16);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_48, 0);
lean_dec(x_52);
lean_ctor_set(x_48, 0, x_44);
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_dec(x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_48, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
lean_dec_ref(x_50);
lean_ctor_set(x_48, 0, x_57);
return x_48;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_ctor_get(x_50, 0);
lean_inc(x_59);
lean_dec_ref(x_50);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_48);
if (x_61 == 0)
{
return x_48;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_48, 0);
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_48);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_21 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_20, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_nat_to_int(x_1);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
lean_dec(x_2);
lean_dec(x_19);
return x_20;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 3);
x_19 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_21);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(x_1, x_2, x_3, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec_ref(x_23);
{
lean_object* _tmp_4 = x_4;
lean_object* _tmp_5 = x_19;
lean_object* _tmp_15 = x_24;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_16 = _tmp_15;
}
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_5);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_16);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_56; 
x_56 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_147 = lean_ctor_get(x_57, 40);
lean_inc_ref(x_147);
lean_dec(x_57);
x_148 = lean_ctor_get(x_147, 2);
x_149 = lean_box(1);
x_150 = lean_nat_dec_lt(x_2, x_148);
if (x_150 == 0)
{
lean_object* x_151; 
lean_dec_ref(x_147);
x_151 = l_outOfBounds___redArg(x_149);
x_59 = x_151;
goto block_146;
}
else
{
lean_object* x_152; 
x_152 = l_Lean_PersistentArray_get_x21___redArg(x_149, x_147, x_2);
x_59 = x_152;
goto block_146;
}
block_146:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_60 = lean_st_ref_take(x_5, x_58);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 14);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_62, 3);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec_ref(x_60);
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_61, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 3);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_61, 4);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_61, 5);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_61, 6);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_61, 7);
lean_inc_ref(x_72);
x_73 = lean_ctor_get_uint8(x_61, sizeof(void*)*16);
x_74 = lean_ctor_get(x_61, 8);
lean_inc(x_74);
x_75 = lean_ctor_get(x_61, 9);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_61, 10);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_61, 11);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_61, 12);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_61, 13);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_61, 15);
lean_inc_ref(x_80);
lean_dec(x_61);
x_81 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_62, 2);
lean_inc_ref(x_83);
lean_dec_ref(x_62);
x_84 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_86);
lean_dec_ref(x_63);
x_87 = lean_array_get_size(x_84);
x_88 = lean_nat_dec_lt(x_4, x_87);
lean_dec(x_87);
if (x_88 == 0)
{
x_14 = x_65;
x_15 = x_74;
x_16 = x_68;
x_17 = x_64;
x_18 = x_59;
x_19 = x_78;
x_20 = x_67;
x_21 = x_80;
x_22 = x_69;
x_23 = x_83;
x_24 = x_85;
x_25 = x_86;
x_26 = x_73;
x_27 = x_77;
x_28 = x_82;
x_29 = x_76;
x_30 = x_75;
x_31 = x_81;
x_32 = x_66;
x_33 = x_72;
x_34 = x_70;
x_35 = x_71;
x_36 = x_79;
x_37 = x_84;
goto block_55;
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_array_fget(x_84, x_4);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_89, 40);
x_92 = lean_box(0);
x_93 = lean_array_fset(x_84, x_4, x_92);
x_94 = lean_box(1);
x_95 = l_Lean_PersistentArray_set___redArg(x_91, x_2, x_94);
lean_ctor_set(x_89, 40, x_95);
x_96 = lean_array_fset(x_93, x_4, x_89);
x_14 = x_65;
x_15 = x_74;
x_16 = x_68;
x_17 = x_64;
x_18 = x_59;
x_19 = x_78;
x_20 = x_67;
x_21 = x_80;
x_22 = x_69;
x_23 = x_83;
x_24 = x_85;
x_25 = x_86;
x_26 = x_73;
x_27 = x_77;
x_28 = x_82;
x_29 = x_76;
x_30 = x_75;
x_31 = x_81;
x_32 = x_66;
x_33 = x_72;
x_34 = x_70;
x_35 = x_71;
x_36 = x_79;
x_37 = x_96;
goto block_55;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_97 = lean_ctor_get(x_89, 0);
x_98 = lean_ctor_get(x_89, 1);
x_99 = lean_ctor_get(x_89, 2);
x_100 = lean_ctor_get(x_89, 3);
x_101 = lean_ctor_get(x_89, 4);
x_102 = lean_ctor_get(x_89, 5);
x_103 = lean_ctor_get(x_89, 6);
x_104 = lean_ctor_get(x_89, 7);
x_105 = lean_ctor_get(x_89, 8);
x_106 = lean_ctor_get(x_89, 9);
x_107 = lean_ctor_get(x_89, 10);
x_108 = lean_ctor_get(x_89, 11);
x_109 = lean_ctor_get(x_89, 12);
x_110 = lean_ctor_get(x_89, 13);
x_111 = lean_ctor_get(x_89, 14);
x_112 = lean_ctor_get(x_89, 15);
x_113 = lean_ctor_get(x_89, 16);
x_114 = lean_ctor_get(x_89, 17);
x_115 = lean_ctor_get(x_89, 18);
x_116 = lean_ctor_get(x_89, 19);
x_117 = lean_ctor_get(x_89, 20);
x_118 = lean_ctor_get(x_89, 21);
x_119 = lean_ctor_get(x_89, 22);
x_120 = lean_ctor_get(x_89, 23);
x_121 = lean_ctor_get(x_89, 24);
x_122 = lean_ctor_get(x_89, 25);
x_123 = lean_ctor_get(x_89, 26);
x_124 = lean_ctor_get(x_89, 27);
x_125 = lean_ctor_get(x_89, 28);
x_126 = lean_ctor_get(x_89, 29);
x_127 = lean_ctor_get(x_89, 30);
x_128 = lean_ctor_get(x_89, 31);
x_129 = lean_ctor_get(x_89, 32);
x_130 = lean_ctor_get(x_89, 33);
x_131 = lean_ctor_get(x_89, 34);
x_132 = lean_ctor_get(x_89, 35);
x_133 = lean_ctor_get_uint8(x_89, sizeof(void*)*42);
x_134 = lean_ctor_get(x_89, 36);
x_135 = lean_ctor_get(x_89, 37);
x_136 = lean_ctor_get(x_89, 38);
x_137 = lean_ctor_get(x_89, 39);
x_138 = lean_ctor_get(x_89, 40);
x_139 = lean_ctor_get(x_89, 41);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_89);
x_140 = lean_box(0);
x_141 = lean_array_fset(x_84, x_4, x_140);
x_142 = lean_box(1);
x_143 = l_Lean_PersistentArray_set___redArg(x_138, x_2, x_142);
x_144 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_144, 0, x_97);
lean_ctor_set(x_144, 1, x_98);
lean_ctor_set(x_144, 2, x_99);
lean_ctor_set(x_144, 3, x_100);
lean_ctor_set(x_144, 4, x_101);
lean_ctor_set(x_144, 5, x_102);
lean_ctor_set(x_144, 6, x_103);
lean_ctor_set(x_144, 7, x_104);
lean_ctor_set(x_144, 8, x_105);
lean_ctor_set(x_144, 9, x_106);
lean_ctor_set(x_144, 10, x_107);
lean_ctor_set(x_144, 11, x_108);
lean_ctor_set(x_144, 12, x_109);
lean_ctor_set(x_144, 13, x_110);
lean_ctor_set(x_144, 14, x_111);
lean_ctor_set(x_144, 15, x_112);
lean_ctor_set(x_144, 16, x_113);
lean_ctor_set(x_144, 17, x_114);
lean_ctor_set(x_144, 18, x_115);
lean_ctor_set(x_144, 19, x_116);
lean_ctor_set(x_144, 20, x_117);
lean_ctor_set(x_144, 21, x_118);
lean_ctor_set(x_144, 22, x_119);
lean_ctor_set(x_144, 23, x_120);
lean_ctor_set(x_144, 24, x_121);
lean_ctor_set(x_144, 25, x_122);
lean_ctor_set(x_144, 26, x_123);
lean_ctor_set(x_144, 27, x_124);
lean_ctor_set(x_144, 28, x_125);
lean_ctor_set(x_144, 29, x_126);
lean_ctor_set(x_144, 30, x_127);
lean_ctor_set(x_144, 31, x_128);
lean_ctor_set(x_144, 32, x_129);
lean_ctor_set(x_144, 33, x_130);
lean_ctor_set(x_144, 34, x_131);
lean_ctor_set(x_144, 35, x_132);
lean_ctor_set(x_144, 36, x_134);
lean_ctor_set(x_144, 37, x_135);
lean_ctor_set(x_144, 38, x_136);
lean_ctor_set(x_144, 39, x_137);
lean_ctor_set(x_144, 40, x_143);
lean_ctor_set(x_144, 41, x_139);
lean_ctor_set_uint8(x_144, sizeof(void*)*42, x_133);
x_145 = lean_array_fset(x_141, x_4, x_144);
x_14 = x_65;
x_15 = x_74;
x_16 = x_68;
x_17 = x_64;
x_18 = x_59;
x_19 = x_78;
x_20 = x_67;
x_21 = x_80;
x_22 = x_69;
x_23 = x_83;
x_24 = x_85;
x_25 = x_86;
x_26 = x_73;
x_27 = x_77;
x_28 = x_82;
x_29 = x_76;
x_30 = x_75;
x_31 = x_81;
x_32 = x_66;
x_33 = x_72;
x_34 = x_70;
x_35 = x_71;
x_36 = x_79;
x_37 = x_145;
goto block_55;
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_56);
if (x_153 == 0)
{
return x_56;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_56, 0);
x_155 = lean_ctor_get(x_56, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_56);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
block_55:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_24);
lean_ctor_set(x_38, 2, x_25);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set(x_39, 2, x_23);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_40, 0, x_14);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_20);
lean_ctor_set(x_40, 3, x_16);
lean_ctor_set(x_40, 4, x_22);
lean_ctor_set(x_40, 5, x_34);
lean_ctor_set(x_40, 6, x_35);
lean_ctor_set(x_40, 7, x_33);
lean_ctor_set(x_40, 8, x_15);
lean_ctor_set(x_40, 9, x_30);
lean_ctor_set(x_40, 10, x_29);
lean_ctor_set(x_40, 11, x_27);
lean_ctor_set(x_40, 12, x_19);
lean_ctor_set(x_40, 13, x_36);
lean_ctor_set(x_40, 14, x_39);
lean_ctor_set(x_40, 15, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*16, x_26);
x_41 = lean_st_ref_set(x_5, x_40, x_17);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(x_1, x_2, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_box(0);
x_46 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(x_1, x_2, x_3, x_45, x_45, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_44);
lean_dec(x_18);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_46);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
return x_17;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(">> ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; 
x_492 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0;
x_493 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_492, x_9, x_11);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_unbox(x_494);
lean_dec(x_494);
if (x_495 == 0)
{
lean_object* x_496; 
x_496 = lean_ctor_get(x_493, 1);
lean_inc(x_496);
lean_dec_ref(x_493);
x_286 = x_2;
x_287 = x_3;
x_288 = x_4;
x_289 = x_5;
x_290 = x_6;
x_291 = x_7;
x_292 = x_8;
x_293 = x_9;
x_294 = x_10;
x_295 = x_496;
goto block_491;
}
else
{
uint8_t x_497; 
x_497 = !lean_is_exclusive(x_493);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_493, 1);
x_499 = lean_ctor_get(x_493, 0);
lean_dec(x_499);
x_500 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_498);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec_ref(x_500);
x_503 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_504 = l_Lean_MessageData_ofExpr(x_501);
lean_ctor_set_tag(x_493, 7);
lean_ctor_set(x_493, 1, x_504);
lean_ctor_set(x_493, 0, x_503);
x_505 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_505, 0, x_493);
lean_ctor_set(x_505, 1, x_503);
x_506 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_492, x_505, x_7, x_8, x_9, x_10, x_502);
x_507 = lean_ctor_get(x_506, 1);
lean_inc(x_507);
lean_dec_ref(x_506);
x_286 = x_2;
x_287 = x_3;
x_288 = x_4;
x_289 = x_5;
x_290 = x_6;
x_291 = x_7;
x_292 = x_8;
x_293 = x_9;
x_294 = x_10;
x_295 = x_507;
goto block_491;
}
else
{
uint8_t x_508; 
lean_free_object(x_493);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_508 = !lean_is_exclusive(x_500);
if (x_508 == 0)
{
return x_500;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_500, 0);
x_510 = lean_ctor_get(x_500, 1);
lean_inc(x_510);
lean_inc(x_509);
lean_dec(x_500);
x_511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_510);
return x_511;
}
}
}
else
{
lean_object* x_512; lean_object* x_513; 
x_512 = lean_ctor_get(x_493, 1);
lean_inc(x_512);
lean_dec(x_493);
x_513 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_512);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec_ref(x_513);
x_516 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_517 = l_Lean_MessageData_ofExpr(x_514);
x_518 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
x_519 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_516);
x_520 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_492, x_519, x_7, x_8, x_9, x_10, x_515);
x_521 = lean_ctor_get(x_520, 1);
lean_inc(x_521);
lean_dec_ref(x_520);
x_286 = x_2;
x_287 = x_3;
x_288 = x_4;
x_289 = x_5;
x_290 = x_6;
x_291 = x_7;
x_292 = x_8;
x_293 = x_9;
x_294 = x_10;
x_295 = x_521;
goto block_491;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_522 = lean_ctor_get(x_513, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_513, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_524 = x_513;
} else {
 lean_dec_ref(x_513);
 x_524 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 2, 0);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_522);
lean_ctor_set(x_525, 1, x_523);
return x_525;
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_57:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set(x_51, 2, x_47);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_29);
lean_ctor_set(x_52, 1, x_37);
lean_ctor_set(x_52, 2, x_28);
lean_ctor_set(x_52, 3, x_51);
x_53 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_25);
lean_ctor_set(x_53, 3, x_34);
lean_ctor_set(x_53, 4, x_42);
lean_ctor_set(x_53, 5, x_30);
lean_ctor_set(x_53, 6, x_40);
lean_ctor_set(x_53, 7, x_16);
lean_ctor_set(x_53, 8, x_36);
lean_ctor_set(x_53, 9, x_27);
lean_ctor_set(x_53, 10, x_26);
lean_ctor_set(x_53, 11, x_39);
lean_ctor_set(x_53, 12, x_43);
lean_ctor_set(x_53, 13, x_44);
lean_ctor_set(x_53, 14, x_52);
lean_ctor_set(x_53, 15, x_32);
lean_ctor_set_uint8(x_53, sizeof(void*)*16, x_38);
x_54 = lean_st_ref_set(x_31, x_53, x_17);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_21, x_22, x_19, x_33, x_31, x_35, x_18, x_24, x_41, x_23, x_20, x_45, x_55);
return x_56;
}
block_237:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_st_ref_take(x_62, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 14);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_73, 3);
lean_inc_ref(x_74);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_76 = lean_ctor_get(x_71, 1);
x_77 = lean_ctor_get(x_71, 0);
lean_dec(x_77);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_72, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 3);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_72, 4);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_72, 5);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_72, 6);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_72, 7);
lean_inc_ref(x_85);
x_86 = lean_ctor_get_uint8(x_72, sizeof(void*)*16);
x_87 = lean_ctor_get(x_72, 8);
lean_inc(x_87);
x_88 = lean_ctor_get(x_72, 9);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_72, 10);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_72, 11);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_72, 12);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_72, 13);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_72, 15);
lean_inc_ref(x_93);
lean_dec(x_72);
x_94 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_73, 1);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_73, 2);
lean_inc_ref(x_96);
lean_dec_ref(x_73);
x_97 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_74, 1);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_74, 2);
lean_inc_ref(x_99);
lean_dec_ref(x_74);
x_100 = lean_array_get_size(x_97);
x_101 = lean_nat_dec_lt(x_61, x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_free_object(x_71);
x_16 = x_85;
x_17 = x_76;
x_18 = x_64;
x_19 = x_58;
x_20 = x_68;
x_21 = x_59;
x_22 = x_60;
x_23 = x_67;
x_24 = x_65;
x_25 = x_80;
x_26 = x_89;
x_27 = x_88;
x_28 = x_96;
x_29 = x_94;
x_30 = x_83;
x_31 = x_62;
x_32 = x_93;
x_33 = x_61;
x_34 = x_81;
x_35 = x_63;
x_36 = x_87;
x_37 = x_95;
x_38 = x_86;
x_39 = x_90;
x_40 = x_84;
x_41 = x_66;
x_42 = x_82;
x_43 = x_91;
x_44 = x_92;
x_45 = x_69;
x_46 = x_98;
x_47 = x_99;
x_48 = x_79;
x_49 = x_78;
x_50 = x_97;
goto block_57;
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_array_fget(x_97, x_61);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_102, 38);
x_105 = lean_ctor_get(x_102, 39);
x_106 = lean_box(0);
x_107 = lean_array_fset(x_97, x_61, x_106);
lean_inc_ref(x_58);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_58);
x_109 = l_Lean_PersistentArray_set___redArg(x_104, x_60, x_108);
lean_inc(x_60);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_105);
lean_ctor_set(x_71, 0, x_60);
lean_ctor_set(x_102, 39, x_71);
lean_ctor_set(x_102, 38, x_109);
x_110 = lean_array_fset(x_107, x_61, x_102);
x_16 = x_85;
x_17 = x_76;
x_18 = x_64;
x_19 = x_58;
x_20 = x_68;
x_21 = x_59;
x_22 = x_60;
x_23 = x_67;
x_24 = x_65;
x_25 = x_80;
x_26 = x_89;
x_27 = x_88;
x_28 = x_96;
x_29 = x_94;
x_30 = x_83;
x_31 = x_62;
x_32 = x_93;
x_33 = x_61;
x_34 = x_81;
x_35 = x_63;
x_36 = x_87;
x_37 = x_95;
x_38 = x_86;
x_39 = x_90;
x_40 = x_84;
x_41 = x_66;
x_42 = x_82;
x_43 = x_91;
x_44 = x_92;
x_45 = x_69;
x_46 = x_98;
x_47 = x_99;
x_48 = x_79;
x_49 = x_78;
x_50 = x_110;
goto block_57;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_111 = lean_ctor_get(x_102, 0);
x_112 = lean_ctor_get(x_102, 1);
x_113 = lean_ctor_get(x_102, 2);
x_114 = lean_ctor_get(x_102, 3);
x_115 = lean_ctor_get(x_102, 4);
x_116 = lean_ctor_get(x_102, 5);
x_117 = lean_ctor_get(x_102, 6);
x_118 = lean_ctor_get(x_102, 7);
x_119 = lean_ctor_get(x_102, 8);
x_120 = lean_ctor_get(x_102, 9);
x_121 = lean_ctor_get(x_102, 10);
x_122 = lean_ctor_get(x_102, 11);
x_123 = lean_ctor_get(x_102, 12);
x_124 = lean_ctor_get(x_102, 13);
x_125 = lean_ctor_get(x_102, 14);
x_126 = lean_ctor_get(x_102, 15);
x_127 = lean_ctor_get(x_102, 16);
x_128 = lean_ctor_get(x_102, 17);
x_129 = lean_ctor_get(x_102, 18);
x_130 = lean_ctor_get(x_102, 19);
x_131 = lean_ctor_get(x_102, 20);
x_132 = lean_ctor_get(x_102, 21);
x_133 = lean_ctor_get(x_102, 22);
x_134 = lean_ctor_get(x_102, 23);
x_135 = lean_ctor_get(x_102, 24);
x_136 = lean_ctor_get(x_102, 25);
x_137 = lean_ctor_get(x_102, 26);
x_138 = lean_ctor_get(x_102, 27);
x_139 = lean_ctor_get(x_102, 28);
x_140 = lean_ctor_get(x_102, 29);
x_141 = lean_ctor_get(x_102, 30);
x_142 = lean_ctor_get(x_102, 31);
x_143 = lean_ctor_get(x_102, 32);
x_144 = lean_ctor_get(x_102, 33);
x_145 = lean_ctor_get(x_102, 34);
x_146 = lean_ctor_get(x_102, 35);
x_147 = lean_ctor_get_uint8(x_102, sizeof(void*)*42);
x_148 = lean_ctor_get(x_102, 36);
x_149 = lean_ctor_get(x_102, 37);
x_150 = lean_ctor_get(x_102, 38);
x_151 = lean_ctor_get(x_102, 39);
x_152 = lean_ctor_get(x_102, 40);
x_153 = lean_ctor_get(x_102, 41);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_102);
x_154 = lean_box(0);
x_155 = lean_array_fset(x_97, x_61, x_154);
lean_inc_ref(x_58);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_58);
x_157 = l_Lean_PersistentArray_set___redArg(x_150, x_60, x_156);
lean_inc(x_60);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_151);
lean_ctor_set(x_71, 0, x_60);
x_158 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_158, 0, x_111);
lean_ctor_set(x_158, 1, x_112);
lean_ctor_set(x_158, 2, x_113);
lean_ctor_set(x_158, 3, x_114);
lean_ctor_set(x_158, 4, x_115);
lean_ctor_set(x_158, 5, x_116);
lean_ctor_set(x_158, 6, x_117);
lean_ctor_set(x_158, 7, x_118);
lean_ctor_set(x_158, 8, x_119);
lean_ctor_set(x_158, 9, x_120);
lean_ctor_set(x_158, 10, x_121);
lean_ctor_set(x_158, 11, x_122);
lean_ctor_set(x_158, 12, x_123);
lean_ctor_set(x_158, 13, x_124);
lean_ctor_set(x_158, 14, x_125);
lean_ctor_set(x_158, 15, x_126);
lean_ctor_set(x_158, 16, x_127);
lean_ctor_set(x_158, 17, x_128);
lean_ctor_set(x_158, 18, x_129);
lean_ctor_set(x_158, 19, x_130);
lean_ctor_set(x_158, 20, x_131);
lean_ctor_set(x_158, 21, x_132);
lean_ctor_set(x_158, 22, x_133);
lean_ctor_set(x_158, 23, x_134);
lean_ctor_set(x_158, 24, x_135);
lean_ctor_set(x_158, 25, x_136);
lean_ctor_set(x_158, 26, x_137);
lean_ctor_set(x_158, 27, x_138);
lean_ctor_set(x_158, 28, x_139);
lean_ctor_set(x_158, 29, x_140);
lean_ctor_set(x_158, 30, x_141);
lean_ctor_set(x_158, 31, x_142);
lean_ctor_set(x_158, 32, x_143);
lean_ctor_set(x_158, 33, x_144);
lean_ctor_set(x_158, 34, x_145);
lean_ctor_set(x_158, 35, x_146);
lean_ctor_set(x_158, 36, x_148);
lean_ctor_set(x_158, 37, x_149);
lean_ctor_set(x_158, 38, x_157);
lean_ctor_set(x_158, 39, x_71);
lean_ctor_set(x_158, 40, x_152);
lean_ctor_set(x_158, 41, x_153);
lean_ctor_set_uint8(x_158, sizeof(void*)*42, x_147);
x_159 = lean_array_fset(x_155, x_61, x_158);
x_16 = x_85;
x_17 = x_76;
x_18 = x_64;
x_19 = x_58;
x_20 = x_68;
x_21 = x_59;
x_22 = x_60;
x_23 = x_67;
x_24 = x_65;
x_25 = x_80;
x_26 = x_89;
x_27 = x_88;
x_28 = x_96;
x_29 = x_94;
x_30 = x_83;
x_31 = x_62;
x_32 = x_93;
x_33 = x_61;
x_34 = x_81;
x_35 = x_63;
x_36 = x_87;
x_37 = x_95;
x_38 = x_86;
x_39 = x_90;
x_40 = x_84;
x_41 = x_66;
x_42 = x_82;
x_43 = x_91;
x_44 = x_92;
x_45 = x_69;
x_46 = x_98;
x_47 = x_99;
x_48 = x_79;
x_49 = x_78;
x_50 = x_159;
goto block_57;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_160 = lean_ctor_get(x_71, 1);
lean_inc(x_160);
lean_dec(x_71);
x_161 = lean_ctor_get(x_72, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_72, 1);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_72, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_72, 3);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_72, 4);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_72, 5);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_72, 6);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_72, 7);
lean_inc_ref(x_168);
x_169 = lean_ctor_get_uint8(x_72, sizeof(void*)*16);
x_170 = lean_ctor_get(x_72, 8);
lean_inc(x_170);
x_171 = lean_ctor_get(x_72, 9);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_72, 10);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_72, 11);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_72, 12);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_72, 13);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_72, 15);
lean_inc_ref(x_176);
lean_dec(x_72);
x_177 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_177);
x_178 = lean_ctor_get(x_73, 1);
lean_inc_ref(x_178);
x_179 = lean_ctor_get(x_73, 2);
lean_inc_ref(x_179);
lean_dec_ref(x_73);
x_180 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_180);
x_181 = lean_ctor_get(x_74, 1);
lean_inc_ref(x_181);
x_182 = lean_ctor_get(x_74, 2);
lean_inc_ref(x_182);
lean_dec_ref(x_74);
x_183 = lean_array_get_size(x_180);
x_184 = lean_nat_dec_lt(x_61, x_183);
lean_dec(x_183);
if (x_184 == 0)
{
x_16 = x_168;
x_17 = x_160;
x_18 = x_64;
x_19 = x_58;
x_20 = x_68;
x_21 = x_59;
x_22 = x_60;
x_23 = x_67;
x_24 = x_65;
x_25 = x_163;
x_26 = x_172;
x_27 = x_171;
x_28 = x_179;
x_29 = x_177;
x_30 = x_166;
x_31 = x_62;
x_32 = x_176;
x_33 = x_61;
x_34 = x_164;
x_35 = x_63;
x_36 = x_170;
x_37 = x_178;
x_38 = x_169;
x_39 = x_173;
x_40 = x_167;
x_41 = x_66;
x_42 = x_165;
x_43 = x_174;
x_44 = x_175;
x_45 = x_69;
x_46 = x_181;
x_47 = x_182;
x_48 = x_162;
x_49 = x_161;
x_50 = x_180;
goto block_57;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_185 = lean_array_fget(x_180, x_61);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 2);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_185, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_185, 4);
lean_inc_ref(x_190);
x_191 = lean_ctor_get(x_185, 5);
lean_inc(x_191);
x_192 = lean_ctor_get(x_185, 6);
lean_inc(x_192);
x_193 = lean_ctor_get(x_185, 7);
lean_inc(x_193);
x_194 = lean_ctor_get(x_185, 8);
lean_inc(x_194);
x_195 = lean_ctor_get(x_185, 9);
lean_inc(x_195);
x_196 = lean_ctor_get(x_185, 10);
lean_inc(x_196);
x_197 = lean_ctor_get(x_185, 11);
lean_inc(x_197);
x_198 = lean_ctor_get(x_185, 12);
lean_inc(x_198);
x_199 = lean_ctor_get(x_185, 13);
lean_inc(x_199);
x_200 = lean_ctor_get(x_185, 14);
lean_inc(x_200);
x_201 = lean_ctor_get(x_185, 15);
lean_inc(x_201);
x_202 = lean_ctor_get(x_185, 16);
lean_inc(x_202);
x_203 = lean_ctor_get(x_185, 17);
lean_inc_ref(x_203);
x_204 = lean_ctor_get(x_185, 18);
lean_inc_ref(x_204);
x_205 = lean_ctor_get(x_185, 19);
lean_inc(x_205);
x_206 = lean_ctor_get(x_185, 20);
lean_inc(x_206);
x_207 = lean_ctor_get(x_185, 21);
lean_inc(x_207);
x_208 = lean_ctor_get(x_185, 22);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_185, 23);
lean_inc_ref(x_209);
x_210 = lean_ctor_get(x_185, 24);
lean_inc_ref(x_210);
x_211 = lean_ctor_get(x_185, 25);
lean_inc(x_211);
x_212 = lean_ctor_get(x_185, 26);
lean_inc(x_212);
x_213 = lean_ctor_get(x_185, 27);
lean_inc(x_213);
x_214 = lean_ctor_get(x_185, 28);
lean_inc_ref(x_214);
x_215 = lean_ctor_get(x_185, 29);
lean_inc_ref(x_215);
x_216 = lean_ctor_get(x_185, 30);
lean_inc_ref(x_216);
x_217 = lean_ctor_get(x_185, 31);
lean_inc_ref(x_217);
x_218 = lean_ctor_get(x_185, 32);
lean_inc_ref(x_218);
x_219 = lean_ctor_get(x_185, 33);
lean_inc_ref(x_219);
x_220 = lean_ctor_get(x_185, 34);
lean_inc_ref(x_220);
x_221 = lean_ctor_get(x_185, 35);
lean_inc_ref(x_221);
x_222 = lean_ctor_get_uint8(x_185, sizeof(void*)*42);
x_223 = lean_ctor_get(x_185, 36);
lean_inc(x_223);
x_224 = lean_ctor_get(x_185, 37);
lean_inc_ref(x_224);
x_225 = lean_ctor_get(x_185, 38);
lean_inc_ref(x_225);
x_226 = lean_ctor_get(x_185, 39);
lean_inc(x_226);
x_227 = lean_ctor_get(x_185, 40);
lean_inc_ref(x_227);
x_228 = lean_ctor_get(x_185, 41);
lean_inc_ref(x_228);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 lean_ctor_release(x_185, 4);
 lean_ctor_release(x_185, 5);
 lean_ctor_release(x_185, 6);
 lean_ctor_release(x_185, 7);
 lean_ctor_release(x_185, 8);
 lean_ctor_release(x_185, 9);
 lean_ctor_release(x_185, 10);
 lean_ctor_release(x_185, 11);
 lean_ctor_release(x_185, 12);
 lean_ctor_release(x_185, 13);
 lean_ctor_release(x_185, 14);
 lean_ctor_release(x_185, 15);
 lean_ctor_release(x_185, 16);
 lean_ctor_release(x_185, 17);
 lean_ctor_release(x_185, 18);
 lean_ctor_release(x_185, 19);
 lean_ctor_release(x_185, 20);
 lean_ctor_release(x_185, 21);
 lean_ctor_release(x_185, 22);
 lean_ctor_release(x_185, 23);
 lean_ctor_release(x_185, 24);
 lean_ctor_release(x_185, 25);
 lean_ctor_release(x_185, 26);
 lean_ctor_release(x_185, 27);
 lean_ctor_release(x_185, 28);
 lean_ctor_release(x_185, 29);
 lean_ctor_release(x_185, 30);
 lean_ctor_release(x_185, 31);
 lean_ctor_release(x_185, 32);
 lean_ctor_release(x_185, 33);
 lean_ctor_release(x_185, 34);
 lean_ctor_release(x_185, 35);
 lean_ctor_release(x_185, 36);
 lean_ctor_release(x_185, 37);
 lean_ctor_release(x_185, 38);
 lean_ctor_release(x_185, 39);
 lean_ctor_release(x_185, 40);
 lean_ctor_release(x_185, 41);
 x_229 = x_185;
} else {
 lean_dec_ref(x_185);
 x_229 = lean_box(0);
}
x_230 = lean_box(0);
x_231 = lean_array_fset(x_180, x_61, x_230);
lean_inc_ref(x_58);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_58);
x_233 = l_Lean_PersistentArray_set___redArg(x_225, x_60, x_232);
lean_inc(x_60);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_60);
lean_ctor_set(x_234, 1, x_226);
if (lean_is_scalar(x_229)) {
 x_235 = lean_alloc_ctor(0, 42, 1);
} else {
 x_235 = x_229;
}
lean_ctor_set(x_235, 0, x_186);
lean_ctor_set(x_235, 1, x_187);
lean_ctor_set(x_235, 2, x_188);
lean_ctor_set(x_235, 3, x_189);
lean_ctor_set(x_235, 4, x_190);
lean_ctor_set(x_235, 5, x_191);
lean_ctor_set(x_235, 6, x_192);
lean_ctor_set(x_235, 7, x_193);
lean_ctor_set(x_235, 8, x_194);
lean_ctor_set(x_235, 9, x_195);
lean_ctor_set(x_235, 10, x_196);
lean_ctor_set(x_235, 11, x_197);
lean_ctor_set(x_235, 12, x_198);
lean_ctor_set(x_235, 13, x_199);
lean_ctor_set(x_235, 14, x_200);
lean_ctor_set(x_235, 15, x_201);
lean_ctor_set(x_235, 16, x_202);
lean_ctor_set(x_235, 17, x_203);
lean_ctor_set(x_235, 18, x_204);
lean_ctor_set(x_235, 19, x_205);
lean_ctor_set(x_235, 20, x_206);
lean_ctor_set(x_235, 21, x_207);
lean_ctor_set(x_235, 22, x_208);
lean_ctor_set(x_235, 23, x_209);
lean_ctor_set(x_235, 24, x_210);
lean_ctor_set(x_235, 25, x_211);
lean_ctor_set(x_235, 26, x_212);
lean_ctor_set(x_235, 27, x_213);
lean_ctor_set(x_235, 28, x_214);
lean_ctor_set(x_235, 29, x_215);
lean_ctor_set(x_235, 30, x_216);
lean_ctor_set(x_235, 31, x_217);
lean_ctor_set(x_235, 32, x_218);
lean_ctor_set(x_235, 33, x_219);
lean_ctor_set(x_235, 34, x_220);
lean_ctor_set(x_235, 35, x_221);
lean_ctor_set(x_235, 36, x_223);
lean_ctor_set(x_235, 37, x_224);
lean_ctor_set(x_235, 38, x_233);
lean_ctor_set(x_235, 39, x_234);
lean_ctor_set(x_235, 40, x_227);
lean_ctor_set(x_235, 41, x_228);
lean_ctor_set_uint8(x_235, sizeof(void*)*42, x_222);
x_236 = lean_array_fset(x_231, x_61, x_235);
x_16 = x_168;
x_17 = x_160;
x_18 = x_64;
x_19 = x_58;
x_20 = x_68;
x_21 = x_59;
x_22 = x_60;
x_23 = x_67;
x_24 = x_65;
x_25 = x_163;
x_26 = x_172;
x_27 = x_171;
x_28 = x_179;
x_29 = x_177;
x_30 = x_166;
x_31 = x_62;
x_32 = x_176;
x_33 = x_61;
x_34 = x_164;
x_35 = x_63;
x_36 = x_170;
x_37 = x_178;
x_38 = x_169;
x_39 = x_173;
x_40 = x_167;
x_41 = x_66;
x_42 = x_165;
x_43 = x_174;
x_44 = x_175;
x_45 = x_69;
x_46 = x_181;
x_47 = x_182;
x_48 = x_162;
x_49 = x_161;
x_50 = x_236;
goto block_57;
}
}
}
block_285:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_251 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5;
x_252 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_251, x_248, x_250);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_unbox(x_253);
lean_dec(x_253);
if (x_254 == 0)
{
lean_object* x_255; 
x_255 = lean_ctor_get(x_252, 1);
lean_inc(x_255);
lean_dec_ref(x_252);
x_58 = x_238;
x_59 = x_239;
x_60 = x_240;
x_61 = x_241;
x_62 = x_242;
x_63 = x_243;
x_64 = x_244;
x_65 = x_245;
x_66 = x_246;
x_67 = x_247;
x_68 = x_248;
x_69 = x_249;
x_70 = x_255;
goto block_237;
}
else
{
uint8_t x_256; 
x_256 = !lean_is_exclusive(x_252);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_252, 1);
x_258 = lean_ctor_get(x_252, 0);
lean_dec(x_258);
x_259 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_238, x_241, x_242, x_243, x_244, x_245, x_246, x_247, x_248, x_249, x_257);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec_ref(x_259);
x_262 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_263 = l_Lean_MessageData_ofExpr(x_260);
lean_ctor_set_tag(x_252, 7);
lean_ctor_set(x_252, 1, x_263);
lean_ctor_set(x_252, 0, x_262);
x_264 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_264, 0, x_252);
lean_ctor_set(x_264, 1, x_262);
x_265 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_251, x_264, x_246, x_247, x_248, x_249, x_261);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec_ref(x_265);
x_58 = x_238;
x_59 = x_239;
x_60 = x_240;
x_61 = x_241;
x_62 = x_242;
x_63 = x_243;
x_64 = x_244;
x_65 = x_245;
x_66 = x_246;
x_67 = x_247;
x_68 = x_248;
x_69 = x_249;
x_70 = x_266;
goto block_237;
}
else
{
uint8_t x_267; 
lean_free_object(x_252);
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
x_267 = !lean_is_exclusive(x_259);
if (x_267 == 0)
{
return x_259;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_259, 0);
x_269 = lean_ctor_get(x_259, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_259);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_252, 1);
lean_inc(x_271);
lean_dec(x_252);
x_272 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_238, x_241, x_242, x_243, x_244, x_245, x_246, x_247, x_248, x_249, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec_ref(x_272);
x_275 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_276 = l_Lean_MessageData_ofExpr(x_273);
x_277 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_275);
x_279 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_251, x_278, x_246, x_247, x_248, x_249, x_274);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec_ref(x_279);
x_58 = x_238;
x_59 = x_239;
x_60 = x_240;
x_61 = x_241;
x_62 = x_242;
x_63 = x_243;
x_64 = x_244;
x_65 = x_245;
x_66 = x_246;
x_67 = x_247;
x_68 = x_248;
x_69 = x_249;
x_70 = x_280;
goto block_237;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
x_281 = lean_ctor_get(x_272, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_272, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_283 = x_272;
} else {
 lean_dec_ref(x_272);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
}
}
block_491:
{
lean_object* x_296; 
lean_inc_ref(x_293);
x_296 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(x_1, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_293, x_294, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec_ref(x_296);
x_299 = lean_ctor_get(x_297, 0);
x_300 = lean_box(0);
x_301 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_958_(x_299, x_300);
if (x_301 == 0)
{
lean_object* x_302; 
lean_inc(x_294);
lean_inc_ref(x_293);
lean_inc(x_292);
lean_inc_ref(x_291);
lean_inc(x_290);
lean_inc_ref(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
x_302 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(x_297, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_293, x_294, x_298);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_302, 1);
lean_inc(x_305);
lean_dec_ref(x_302);
x_306 = !lean_is_exclusive(x_303);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_307 = lean_ctor_get(x_303, 0);
x_308 = lean_ctor_get(x_303, 1);
lean_dec(x_308);
x_309 = !lean_is_exclusive(x_304);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_310 = lean_ctor_get(x_304, 0);
x_311 = lean_ctor_get(x_304, 1);
x_312 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_313 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_312, x_293, x_305);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_unbox(x_314);
lean_dec(x_314);
if (x_315 == 0)
{
lean_object* x_316; 
lean_free_object(x_304);
lean_free_object(x_303);
x_316 = lean_ctor_get(x_313, 1);
lean_inc(x_316);
lean_dec_ref(x_313);
x_238 = x_311;
x_239 = x_307;
x_240 = x_310;
x_241 = x_286;
x_242 = x_287;
x_243 = x_288;
x_244 = x_289;
x_245 = x_290;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_316;
goto block_285;
}
else
{
uint8_t x_317; 
x_317 = !lean_is_exclusive(x_313);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_313, 1);
x_319 = lean_ctor_get(x_313, 0);
lean_dec(x_319);
x_320 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_310, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_293, x_294, x_318);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec_ref(x_320);
x_323 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_311, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_293, x_294, x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec_ref(x_323);
x_326 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
x_327 = l_Lean_MessageData_ofExpr(x_321);
lean_ctor_set_tag(x_313, 7);
lean_ctor_set(x_313, 1, x_327);
lean_ctor_set(x_313, 0, x_326);
x_328 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_304, 7);
lean_ctor_set(x_304, 1, x_328);
lean_ctor_set(x_304, 0, x_313);
x_329 = l_Lean_MessageData_ofExpr(x_324);
lean_ctor_set_tag(x_303, 7);
lean_ctor_set(x_303, 1, x_329);
lean_ctor_set(x_303, 0, x_304);
x_330 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_331 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_331, 0, x_303);
lean_ctor_set(x_331, 1, x_330);
x_332 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_312, x_331, x_291, x_292, x_293, x_294, x_325);
x_333 = lean_ctor_get(x_332, 1);
lean_inc(x_333);
lean_dec_ref(x_332);
x_238 = x_311;
x_239 = x_307;
x_240 = x_310;
x_241 = x_286;
x_242 = x_287;
x_243 = x_288;
x_244 = x_289;
x_245 = x_290;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_333;
goto block_285;
}
else
{
uint8_t x_334; 
lean_dec(x_321);
lean_free_object(x_313);
lean_free_object(x_304);
lean_dec(x_311);
lean_dec(x_310);
lean_free_object(x_303);
lean_dec(x_307);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
x_334 = !lean_is_exclusive(x_323);
if (x_334 == 0)
{
return x_323;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_323, 0);
x_336 = lean_ctor_get(x_323, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_323);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
return x_337;
}
}
}
else
{
uint8_t x_338; 
lean_free_object(x_313);
lean_free_object(x_304);
lean_dec(x_311);
lean_dec(x_310);
lean_free_object(x_303);
lean_dec(x_307);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
x_338 = !lean_is_exclusive(x_320);
if (x_338 == 0)
{
return x_320;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_320, 0);
x_340 = lean_ctor_get(x_320, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_320);
x_341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
return x_341;
}
}
}
else
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_313, 1);
lean_inc(x_342);
lean_dec(x_313);
x_343 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_310, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_293, x_294, x_342);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec_ref(x_343);
x_346 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_311, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_293, x_294, x_345);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec_ref(x_346);
x_349 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
x_350 = l_Lean_MessageData_ofExpr(x_344);
x_351 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
x_352 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_304, 7);
lean_ctor_set(x_304, 1, x_352);
lean_ctor_set(x_304, 0, x_351);
x_353 = l_Lean_MessageData_ofExpr(x_347);
lean_ctor_set_tag(x_303, 7);
lean_ctor_set(x_303, 1, x_353);
lean_ctor_set(x_303, 0, x_304);
x_354 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_355 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_355, 0, x_303);
lean_ctor_set(x_355, 1, x_354);
x_356 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_312, x_355, x_291, x_292, x_293, x_294, x_348);
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
lean_dec_ref(x_356);
x_238 = x_311;
x_239 = x_307;
x_240 = x_310;
x_241 = x_286;
x_242 = x_287;
x_243 = x_288;
x_244 = x_289;
x_245 = x_290;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_357;
goto block_285;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_344);
lean_free_object(x_304);
lean_dec(x_311);
lean_dec(x_310);
lean_free_object(x_303);
lean_dec(x_307);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
x_358 = lean_ctor_get(x_346, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_346, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_360 = x_346;
} else {
 lean_dec_ref(x_346);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_free_object(x_304);
lean_dec(x_311);
lean_dec(x_310);
lean_free_object(x_303);
lean_dec(x_307);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
x_362 = lean_ctor_get(x_343, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_343, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_364 = x_343;
} else {
 lean_dec_ref(x_343);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_362);
lean_ctor_set(x_365, 1, x_363);
return x_365;
}
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_366 = lean_ctor_get(x_304, 0);
x_367 = lean_ctor_get(x_304, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_304);
x_368 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_369 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_368, x_293, x_305);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_unbox(x_370);
lean_dec(x_370);
if (x_371 == 0)
{
lean_object* x_372; 
lean_free_object(x_303);
x_372 = lean_ctor_get(x_369, 1);
lean_inc(x_372);
lean_dec_ref(x_369);
x_238 = x_367;
x_239 = x_307;
x_240 = x_366;
x_241 = x_286;
x_242 = x_287;
x_243 = x_288;
x_244 = x_289;
x_245 = x_290;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_372;
goto block_285;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_369, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_374 = x_369;
} else {
 lean_dec_ref(x_369);
 x_374 = lean_box(0);
}
x_375 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_366, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_293, x_294, x_373);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec_ref(x_375);
x_378 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_367, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_293, x_294, x_377);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec_ref(x_378);
x_381 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
x_382 = l_Lean_MessageData_ofExpr(x_376);
if (lean_is_scalar(x_374)) {
 x_383 = lean_alloc_ctor(7, 2, 0);
} else {
 x_383 = x_374;
 lean_ctor_set_tag(x_383, 7);
}
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
x_384 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_385 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
x_386 = l_Lean_MessageData_ofExpr(x_379);
lean_ctor_set_tag(x_303, 7);
lean_ctor_set(x_303, 1, x_386);
lean_ctor_set(x_303, 0, x_385);
x_387 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_388 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_388, 0, x_303);
lean_ctor_set(x_388, 1, x_387);
x_389 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_368, x_388, x_291, x_292, x_293, x_294, x_380);
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
lean_dec_ref(x_389);
x_238 = x_367;
x_239 = x_307;
x_240 = x_366;
x_241 = x_286;
x_242 = x_287;
x_243 = x_288;
x_244 = x_289;
x_245 = x_290;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_390;
goto block_285;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_376);
lean_dec(x_374);
lean_dec(x_367);
lean_dec(x_366);
lean_free_object(x_303);
lean_dec(x_307);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
x_391 = lean_ctor_get(x_378, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_378, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_393 = x_378;
} else {
 lean_dec_ref(x_378);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_392);
return x_394;
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_374);
lean_dec(x_367);
lean_dec(x_366);
lean_free_object(x_303);
lean_dec(x_307);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
x_395 = lean_ctor_get(x_375, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_375, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_397 = x_375;
} else {
 lean_dec_ref(x_375);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
}
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_399 = lean_ctor_get(x_303, 0);
lean_inc(x_399);
lean_dec(x_303);
x_400 = lean_ctor_get(x_304, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_304, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_402 = x_304;
} else {
 lean_dec_ref(x_304);
 x_402 = lean_box(0);
}
x_403 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_404 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_403, x_293, x_305);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_unbox(x_405);
lean_dec(x_405);
if (x_406 == 0)
{
lean_object* x_407; 
lean_dec(x_402);
x_407 = lean_ctor_get(x_404, 1);
lean_inc(x_407);
lean_dec_ref(x_404);
x_238 = x_401;
x_239 = x_399;
x_240 = x_400;
x_241 = x_286;
x_242 = x_287;
x_243 = x_288;
x_244 = x_289;
x_245 = x_290;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_407;
goto block_285;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_404, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_409 = x_404;
} else {
 lean_dec_ref(x_404);
 x_409 = lean_box(0);
}
x_410 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_400, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_293, x_294, x_408);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec_ref(x_410);
x_413 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_401, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_293, x_294, x_412);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec_ref(x_413);
x_416 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
x_417 = l_Lean_MessageData_ofExpr(x_411);
if (lean_is_scalar(x_409)) {
 x_418 = lean_alloc_ctor(7, 2, 0);
} else {
 x_418 = x_409;
 lean_ctor_set_tag(x_418, 7);
}
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
x_419 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
if (lean_is_scalar(x_402)) {
 x_420 = lean_alloc_ctor(7, 2, 0);
} else {
 x_420 = x_402;
 lean_ctor_set_tag(x_420, 7);
}
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
x_421 = l_Lean_MessageData_ofExpr(x_414);
x_422 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
x_423 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_424 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
x_425 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_403, x_424, x_291, x_292, x_293, x_294, x_415);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
lean_dec_ref(x_425);
x_238 = x_401;
x_239 = x_399;
x_240 = x_400;
x_241 = x_286;
x_242 = x_287;
x_243 = x_288;
x_244 = x_289;
x_245 = x_290;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_426;
goto block_285;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_411);
lean_dec(x_409);
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
x_427 = lean_ctor_get(x_413, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_413, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_429 = x_413;
} else {
 lean_dec_ref(x_413);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_429)) {
 x_430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_430 = x_429;
}
lean_ctor_set(x_430, 0, x_427);
lean_ctor_set(x_430, 1, x_428);
return x_430;
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_409);
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
x_431 = lean_ctor_get(x_410, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_410, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_433 = x_410;
} else {
 lean_dec_ref(x_410);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_434 = x_433;
}
lean_ctor_set(x_434, 0, x_431);
lean_ctor_set(x_434, 1, x_432);
return x_434;
}
}
}
}
else
{
uint8_t x_435; 
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
x_435 = !lean_is_exclusive(x_302);
if (x_435 == 0)
{
return x_302;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_302, 0);
x_437 = lean_ctor_get(x_302, 1);
lean_inc(x_437);
lean_inc(x_436);
lean_dec(x_302);
x_438 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
return x_438;
}
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
x_439 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3;
x_440 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_439, x_293, x_298);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_unbox(x_441);
lean_dec(x_441);
if (x_442 == 0)
{
lean_object* x_443; 
lean_dec(x_297);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
x_443 = lean_ctor_get(x_440, 1);
lean_inc(x_443);
lean_dec_ref(x_440);
x_12 = x_443;
goto block_15;
}
else
{
uint8_t x_444; 
x_444 = !lean_is_exclusive(x_440);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; 
x_445 = lean_ctor_get(x_440, 1);
x_446 = lean_ctor_get(x_440, 0);
lean_dec(x_446);
x_447 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_297, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_293, x_294, x_445);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
x_448 = !lean_is_exclusive(x_297);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_297, 1);
lean_dec(x_449);
x_450 = lean_ctor_get(x_297, 0);
lean_dec(x_450);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_451 = lean_ctor_get(x_447, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_447, 1);
lean_inc(x_452);
lean_dec_ref(x_447);
x_453 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_454 = l_Lean_MessageData_ofExpr(x_451);
lean_ctor_set_tag(x_440, 7);
lean_ctor_set(x_440, 1, x_454);
lean_ctor_set(x_440, 0, x_453);
lean_ctor_set_tag(x_297, 7);
lean_ctor_set(x_297, 1, x_453);
lean_ctor_set(x_297, 0, x_440);
x_455 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_439, x_297, x_291, x_292, x_293, x_294, x_452);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
x_456 = lean_ctor_get(x_455, 1);
lean_inc(x_456);
lean_dec_ref(x_455);
x_12 = x_456;
goto block_15;
}
else
{
uint8_t x_457; 
lean_free_object(x_297);
lean_free_object(x_440);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
x_457 = !lean_is_exclusive(x_447);
if (x_457 == 0)
{
return x_447;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_447, 0);
x_459 = lean_ctor_get(x_447, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_447);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
return x_460;
}
}
}
else
{
lean_dec(x_297);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_461 = lean_ctor_get(x_447, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_447, 1);
lean_inc(x_462);
lean_dec_ref(x_447);
x_463 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_464 = l_Lean_MessageData_ofExpr(x_461);
lean_ctor_set_tag(x_440, 7);
lean_ctor_set(x_440, 1, x_464);
lean_ctor_set(x_440, 0, x_463);
x_465 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_465, 0, x_440);
lean_ctor_set(x_465, 1, x_463);
x_466 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_439, x_465, x_291, x_292, x_293, x_294, x_462);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
lean_dec_ref(x_466);
x_12 = x_467;
goto block_15;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_free_object(x_440);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
x_468 = lean_ctor_get(x_447, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_447, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_470 = x_447;
} else {
 lean_dec_ref(x_447);
 x_470 = lean_box(0);
}
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_468);
lean_ctor_set(x_471, 1, x_469);
return x_471;
}
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_440, 1);
lean_inc(x_472);
lean_dec(x_440);
x_473 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_297, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_293, x_294, x_472);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_474 = x_297;
} else {
 lean_dec_ref(x_297);
 x_474 = lean_box(0);
}
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_475 = lean_ctor_get(x_473, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_473, 1);
lean_inc(x_476);
lean_dec_ref(x_473);
x_477 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_478 = l_Lean_MessageData_ofExpr(x_475);
x_479 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
if (lean_is_scalar(x_474)) {
 x_480 = lean_alloc_ctor(7, 2, 0);
} else {
 x_480 = x_474;
 lean_ctor_set_tag(x_480, 7);
}
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_477);
x_481 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_439, x_480, x_291, x_292, x_293, x_294, x_476);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
lean_dec_ref(x_481);
x_12 = x_482;
goto block_15;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_474);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
x_483 = lean_ctor_get(x_473, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_473, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_485 = x_473;
} else {
 lean_dec_ref(x_473);
 x_485 = lean_box(0);
}
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(1, 2, 0);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_484);
return x_486;
}
}
}
}
}
else
{
uint8_t x_487; 
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
x_487 = !lean_is_exclusive(x_296);
if (x_487 == 0)
{
return x_296;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_296, 0);
x_489 = lean_ctor_get(x_296, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_296);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1;
x_9 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_8, x_5, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec_ref(x_9);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_20 = l_Lean_MessageData_ofExpr(x_1);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_ofExpr(x_2);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
x_27 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_8, x_26, x_3, x_4, x_5, x_6, x_18);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_14 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec_ref(x_15);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_24 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_24, 1);
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec_ref(x_25);
lean_inc(x_35);
lean_inc(x_23);
x_36 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Grind_Linarith_Expr_norm(x_36);
x_38 = lean_box(0);
x_39 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_958_(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_24);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_2);
lean_ctor_set(x_40, 2, x_23);
lean_ctor_set(x_40, 3, x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_33);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = lean_box(0);
lean_ctor_set(x_24, 0, x_43);
return x_24;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_dec(x_24);
x_45 = lean_ctor_get(x_25, 0);
lean_inc(x_45);
lean_dec_ref(x_25);
lean_inc(x_45);
lean_inc(x_23);
x_46 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Grind_Linarith_Expr_norm(x_46);
x_48 = lean_box(0);
x_49 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_958_(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_2);
lean_ctor_set(x_50, 2, x_23);
lean_ctor_set(x_50, 3, x_45);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_44);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_55 = !lean_is_exclusive(x_24);
if (x_55 == 0)
{
return x_24;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_24, 0);
x_57 = lean_ctor_get(x_24, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_24);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_14);
if (x_59 == 0)
{
return x_14;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_14, 0);
x_61 = lean_ctor_get(x_14, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_14);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* lean_process_linarith_eq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_34; 
x_34 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_1, x_2);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(x_1, x_2, x_3, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec_ref(x_35);
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
lean_dec_ref(x_36);
x_45 = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec_ref(x_45);
x_49 = l_Lean_Meta_Grind_Arith_Linear_isCommRing(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec_ref(x_49);
x_53 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(x_1, x_2, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_44);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec_ref(x_49);
x_55 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_44);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 0);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_dec_ref(x_45);
x_61 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0;
x_62 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_61, x_9, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec_ref(x_62);
x_12 = x_44;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_65;
goto block_33;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_62, 1);
x_68 = lean_ctor_get(x_62, 0);
lean_dec(x_68);
x_69 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 1);
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_73 = l_Lean_Meta_mkEq(x_1, x_2, x_7, x_8, x_9, x_10, x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_77 = l_Lean_MessageData_ofExpr(x_74);
lean_ctor_set_tag(x_69, 7);
lean_ctor_set(x_69, 1, x_77);
lean_ctor_set(x_69, 0, x_76);
lean_ctor_set_tag(x_62, 7);
lean_ctor_set(x_62, 1, x_76);
lean_ctor_set(x_62, 0, x_69);
x_78 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_61, x_62, x_7, x_8, x_9, x_10, x_75);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
x_12 = x_44;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_79;
goto block_33;
}
else
{
uint8_t x_80; 
lean_free_object(x_69);
lean_free_object(x_62);
lean_dec(x_44);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_73);
if (x_80 == 0)
{
return x_73;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_73, 0);
x_82 = lean_ctor_get(x_73, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_73);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_69, 1);
lean_inc(x_84);
lean_dec(x_69);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_85 = l_Lean_Meta_mkEq(x_1, x_2, x_7, x_8, x_9, x_10, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_89 = l_Lean_MessageData_ofExpr(x_86);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set_tag(x_62, 7);
lean_ctor_set(x_62, 1, x_88);
lean_ctor_set(x_62, 0, x_90);
x_91 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_61, x_62, x_7, x_8, x_9, x_10, x_87);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec_ref(x_91);
x_12 = x_44;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_92;
goto block_33;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_free_object(x_62);
lean_dec(x_44);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_93 = lean_ctor_get(x_85, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_85, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_95 = x_85;
} else {
 lean_dec_ref(x_85);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_free_object(x_62);
lean_dec(x_44);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_69;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_62, 1);
lean_inc(x_97);
lean_dec(x_62);
x_98 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_101 = l_Lean_Meta_mkEq(x_1, x_2, x_7, x_8, x_9, x_10, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_105 = l_Lean_MessageData_ofExpr(x_102);
if (lean_is_scalar(x_100)) {
 x_106 = lean_alloc_ctor(7, 2, 0);
} else {
 x_106 = x_100;
 lean_ctor_set_tag(x_106, 7);
}
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
x_108 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_61, x_107, x_7, x_8, x_9, x_10, x_103);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec_ref(x_108);
x_12 = x_44;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_109;
goto block_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_100);
lean_dec(x_44);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_110 = lean_ctor_get(x_101, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_101, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_112 = x_101;
} else {
 lean_dec_ref(x_101);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_dec(x_44);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_98;
}
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_44);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_114 = !lean_is_exclusive(x_45);
if (x_114 == 0)
{
return x_45;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_45, 0);
x_116 = lean_ctor_get(x_45, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_45);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_118 = !lean_is_exclusive(x_35);
if (x_118 == 0)
{
return x_35;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_35, 0);
x_120 = lean_ctor_get(x_35, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_35);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_11);
return x_123;
}
block_33:
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Grind_Arith_Linear_isCommRing(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(x_1, x_2, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec_ref(x_22);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(x_1, x_2, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = 0;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_box(x_13);
lean_inc_ref(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 13, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec_ref(x_17);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec_ref(x_18);
x_27 = lean_box(x_13);
lean_inc_ref(x_2);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 13, 3);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_dec_ref(x_29);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec_ref(x_30);
x_39 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_74; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_74 = lean_nat_dec_le(x_40, x_43);
if (x_74 == 0)
{
lean_dec(x_43);
x_45 = x_40;
goto block_73;
}
else
{
lean_dec(x_40);
x_45 = x_43;
goto block_73;
}
block_73:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_38);
lean_inc(x_26);
x_46 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_46, 0, x_26);
lean_ctor_set(x_46, 1, x_38);
x_47 = l_Lean_Grind_CommRing_Expr_toPoly(x_46);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_47);
x_48 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_47, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_49, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
lean_dec_ref(x_47);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_51, 0, x_55);
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_dec_ref(x_51);
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
lean_dec_ref(x_52);
lean_inc(x_60);
x_61 = l_Lean_Grind_Linarith_Expr_norm(x_60);
x_62 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_2);
lean_ctor_set(x_62, 2, x_26);
lean_ctor_set(x_62, 3, x_38);
lean_ctor_set(x_62, 4, x_47);
lean_ctor_set(x_62, 5, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_59);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec_ref(x_47);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = !lean_is_exclusive(x_51);
if (x_65 == 0)
{
return x_51;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_51, 0);
x_67 = lean_ctor_get(x_51, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_51);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec_ref(x_47);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_69 = !lean_is_exclusive(x_48);
if (x_69 == 0)
{
return x_48;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_48, 0);
x_71 = lean_ctor_get(x_48, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_48);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_42);
if (x_75 == 0)
{
return x_42;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_42, 0);
x_77 = lean_ctor_get(x_42, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_42);
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
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_79 = !lean_is_exclusive(x_39);
if (x_79 == 0)
{
return x_39;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_39, 0);
x_81 = lean_ctor_get(x_39, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_39);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_83 = !lean_is_exclusive(x_29);
if (x_83 == 0)
{
return x_29;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_29, 0);
x_85 = lean_ctor_get(x_29, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_29);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_87 = !lean_is_exclusive(x_17);
if (x_87 == 0)
{
return x_17;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_17, 0);
x_89 = lean_ctor_get(x_17, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_17);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_14 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec_ref(x_15);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_24 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec_ref(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec_ref(x_25);
lean_inc(x_33);
lean_inc(x_23);
x_34 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Grind_Linarith_Expr_norm(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_2);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = !lean_is_exclusive(x_14);
if (x_43 == 0)
{
return x_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_14, 0);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_14);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* lean_process_linarith_diseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(x_1, x_2, x_3, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec_ref(x_13);
x_22 = l_Lean_Meta_Grind_Arith_Linear_isCommRing(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(x_1, x_2, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec_ref(x_22);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(x_1, x_2, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* initialize_Init_Grind_Ring_Poly(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Poly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___Lean_Grind_Linarith_Poly_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4_spec__4___closed__1);
l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__0 = _init_l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__0();
l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__1 = _init_l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__1);
l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__2 = _init_l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0 = _init_l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__1 = _init_l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__1();
lean_mark_persistent(l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__1);
l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__2 = _init_l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__2();
lean_mark_persistent(l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__2);
l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__3 = _init_l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__3();
lean_mark_persistent(l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__3);
l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__4 = _init_l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__4();
lean_mark_persistent(l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__4);
l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__5 = _init_l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__5();
lean_mark_persistent(l_panic___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__5);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__6);
l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___closed__0);
l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__0___closed__1);
l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0);
l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0);
l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0 = _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1 = _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2 = _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2);
l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3 = _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__4 = _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0 = _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1 = _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2 = _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2);
l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3 = _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__4 = _init_l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__4);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

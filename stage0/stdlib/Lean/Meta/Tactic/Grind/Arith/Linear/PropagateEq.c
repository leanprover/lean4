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
uint8_t l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith_2431311409____hygCtx___hyg_34_(lean_object*, lean_object*);
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
uint8_t l_Lean_beqLBool____x40_Lean_Data_LBool_27903016____hygCtx___hyg_9_(uint8_t, uint8_t);
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
x_5 = lean_ctor_get(x_2, 13);
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
x_20 = lean_ctor_get(x_19, 31);
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
x_23 = lean_ctor_get(x_16, 24);
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
x_44 = lean_ctor_get(x_43, 31);
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
x_23 = lean_ctor_get(x_18, 23);
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
x_15 = lean_ctor_get(x_14, 18);
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
x_18 = lean_ctor_get(x_16, 18);
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
x_19 = lean_ctor_get(x_17, 19);
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
x_19 = lean_ctor_get(x_17, 19);
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
x_65 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith_2431311409____hygCtx___hyg_34_(x_63, x_64);
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
x_102 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith_2431311409____hygCtx___hyg_34_(x_100, x_101);
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
x_39 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith_2431311409____hygCtx___hyg_34_(x_37, x_38);
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
x_55 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith_2431311409____hygCtx___hyg_34_(x_53, x_54);
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
x_12 = x_42;
x_13 = x_41;
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
x_12 = x_42;
x_13 = x_41;
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
x_12 = x_48;
x_13 = x_47;
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
x_12 = x_48;
x_13 = x_47;
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
x_12 = x_56;
x_13 = x_55;
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
x_12 = x_56;
x_13 = x_55;
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
x_16 = lean_nat_abs(x_13);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
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
x_26 = lean_ctor_get(x_9, 13);
x_27 = lean_nat_dec_eq(x_16, x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_16, x_29);
lean_dec(x_16);
lean_ctor_set(x_9, 3, x_30);
lean_inc(x_28);
x_31 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec_ref(x_9);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
lean_ctor_set(x_31, 0, x_1);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec_ref(x_32);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec_ref(x_31);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_dec(x_42);
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
x_60 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_61 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_60, x_9, x_39);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_free_object(x_37);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec_ref(x_61);
x_46 = x_2;
x_47 = x_3;
x_48 = x_4;
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_64;
goto block_59;
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 1);
x_67 = lean_ctor_get(x_61, 0);
lean_dec(x_67);
x_68 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_78 = l_Lean_MessageData_ofExpr(x_69);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_78);
lean_ctor_set(x_61, 0, x_77);
x_79 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_79);
lean_ctor_set(x_37, 0, x_61);
x_80 = l_Lean_MessageData_ofExpr(x_72);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_37);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
x_83 = l_Lean_MessageData_ofExpr(x_75);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_77);
x_86 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_60, x_85, x_7, x_8, x_9, x_10, x_76);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec_ref(x_86);
x_46 = x_2;
x_47 = x_3;
x_48 = x_4;
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_87;
goto block_59;
}
else
{
uint8_t x_88; 
lean_dec(x_72);
lean_dec(x_69);
lean_free_object(x_61);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_88 = !lean_is_exclusive(x_74);
if (x_88 == 0)
{
return x_74;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_74, 0);
x_90 = lean_ctor_get(x_74, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_74);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_69);
lean_free_object(x_61);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_71);
if (x_92 == 0)
{
return x_71;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_71, 0);
x_94 = lean_ctor_get(x_71, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_71);
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
lean_free_object(x_61);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_96 = !lean_is_exclusive(x_68);
if (x_96 == 0)
{
return x_68;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_68, 0);
x_98 = lean_ctor_get(x_68, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_68);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_61, 1);
lean_inc(x_100);
lean_dec(x_61);
x_101 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec_ref(x_104);
x_107 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
x_110 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_111 = l_Lean_MessageData_ofExpr(x_102);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_113);
lean_ctor_set(x_37, 0, x_112);
x_114 = l_Lean_MessageData_ofExpr(x_105);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_37);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
x_117 = l_Lean_MessageData_ofExpr(x_108);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_110);
x_120 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_60, x_119, x_7, x_8, x_9, x_10, x_109);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec_ref(x_120);
x_46 = x_2;
x_47 = x_3;
x_48 = x_4;
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_121;
goto block_59;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_105);
lean_dec(x_102);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_122 = lean_ctor_get(x_107, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_107, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_124 = x_107;
} else {
 lean_dec_ref(x_107);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_102);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_126 = lean_ctor_get(x_104, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_104, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_128 = x_104;
} else {
 lean_dec_ref(x_104);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_130 = lean_ctor_get(x_101, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_101, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_132 = x_101;
} else {
 lean_dec_ref(x_101);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
block_59:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_43);
lean_ctor_set(x_56, 2, x_1);
if (lean_is_scalar(x_45)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_45;
}
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_56);
x_1 = x_57;
x_2 = x_46;
x_3 = x_47;
x_4 = x_48;
x_5 = x_49;
x_6 = x_50;
x_7 = x_51;
x_8 = x_52;
x_9 = x_53;
x_10 = x_54;
x_11 = x_55;
goto _start;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_134 = lean_ctor_get(x_37, 0);
lean_inc(x_134);
lean_dec(x_37);
x_135 = lean_ctor_get(x_38, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_38, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_137 = x_38;
} else {
 lean_dec_ref(x_38);
 x_137 = lean_box(0);
}
x_152 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_153 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_152, x_9, x_39);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec_ref(x_153);
x_138 = x_2;
x_139 = x_3;
x_140 = x_4;
x_141 = x_5;
x_142 = x_6;
x_143 = x_7;
x_144 = x_8;
x_145 = x_9;
x_146 = x_10;
x_147 = x_156;
goto block_151;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_158 = x_153;
} else {
 lean_dec_ref(x_153);
 x_158 = lean_box(0);
}
x_159 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_134, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_157);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
x_162 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec_ref(x_162);
x_165 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec_ref(x_165);
x_168 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_169 = l_Lean_MessageData_ofExpr(x_160);
if (lean_is_scalar(x_158)) {
 x_170 = lean_alloc_ctor(7, 2, 0);
} else {
 x_170 = x_158;
 lean_ctor_set_tag(x_170, 7);
}
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lean_MessageData_ofExpr(x_163);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_171);
x_176 = l_Lean_MessageData_ofExpr(x_166);
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_168);
x_179 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_152, x_178, x_7, x_8, x_9, x_10, x_167);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec_ref(x_179);
x_138 = x_2;
x_139 = x_3;
x_140 = x_4;
x_141 = x_5;
x_142 = x_6;
x_143 = x_7;
x_144 = x_8;
x_145 = x_9;
x_146 = x_10;
x_147 = x_180;
goto block_151;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_181 = lean_ctor_get(x_165, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_165, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_183 = x_165;
} else {
 lean_dec_ref(x_165);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_185 = lean_ctor_get(x_162, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_162, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_187 = x_162;
} else {
 lean_dec_ref(x_162);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_158);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_189 = lean_ctor_get(x_159, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_159, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_191 = x_159;
} else {
 lean_dec_ref(x_159);
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
block_151:
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_148, 0, x_134);
lean_ctor_set(x_148, 1, x_135);
lean_ctor_set(x_148, 2, x_1);
if (lean_is_scalar(x_137)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_137;
}
lean_ctor_set(x_149, 0, x_136);
lean_ctor_set(x_149, 1, x_148);
x_1 = x_149;
x_2 = x_138;
x_3 = x_139;
x_4 = x_140;
x_5 = x_141;
x_6 = x_142;
x_7 = x_143;
x_8 = x_144;
x_9 = x_145;
x_10 = x_146;
x_11 = x_147;
goto _start;
}
}
}
}
else
{
uint8_t x_193; 
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_193 = !lean_is_exclusive(x_31);
if (x_193 == 0)
{
return x_31;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_31, 0);
x_195 = lean_ctor_get(x_31, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_31);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
lean_object* x_197; 
lean_free_object(x_9);
lean_dec_ref(x_26);
lean_dec(x_25);
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
x_197 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_18, x_11);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; uint8_t x_214; 
x_198 = lean_ctor_get(x_9, 0);
x_199 = lean_ctor_get(x_9, 1);
x_200 = lean_ctor_get(x_9, 2);
x_201 = lean_ctor_get(x_9, 3);
x_202 = lean_ctor_get(x_9, 4);
x_203 = lean_ctor_get(x_9, 5);
x_204 = lean_ctor_get(x_9, 6);
x_205 = lean_ctor_get(x_9, 7);
x_206 = lean_ctor_get(x_9, 8);
x_207 = lean_ctor_get(x_9, 9);
x_208 = lean_ctor_get(x_9, 10);
x_209 = lean_ctor_get(x_9, 11);
x_210 = lean_ctor_get_uint8(x_9, sizeof(void*)*14);
x_211 = lean_ctor_get(x_9, 12);
x_212 = lean_ctor_get_uint8(x_9, sizeof(void*)*14 + 1);
x_213 = lean_ctor_get(x_9, 13);
lean_inc(x_213);
lean_inc(x_211);
lean_inc(x_209);
lean_inc(x_208);
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
lean_dec(x_9);
x_214 = lean_nat_dec_eq(x_201, x_202);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_1, 0);
x_216 = lean_unsigned_to_nat(1u);
x_217 = lean_nat_add(x_201, x_216);
lean_dec(x_201);
x_218 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_218, 0, x_198);
lean_ctor_set(x_218, 1, x_199);
lean_ctor_set(x_218, 2, x_200);
lean_ctor_set(x_218, 3, x_217);
lean_ctor_set(x_218, 4, x_202);
lean_ctor_set(x_218, 5, x_203);
lean_ctor_set(x_218, 6, x_204);
lean_ctor_set(x_218, 7, x_205);
lean_ctor_set(x_218, 8, x_206);
lean_ctor_set(x_218, 9, x_207);
lean_ctor_set(x_218, 10, x_208);
lean_ctor_set(x_218, 11, x_209);
lean_ctor_set(x_218, 12, x_211);
lean_ctor_set(x_218, 13, x_213);
lean_ctor_set_uint8(x_218, sizeof(void*)*14, x_210);
lean_ctor_set_uint8(x_218, sizeof(void*)*14 + 1, x_212);
lean_inc(x_215);
x_219 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(x_215, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_218, x_10, x_11);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec_ref(x_218);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_1);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_224 = lean_ctor_get(x_220, 0);
lean_inc(x_224);
lean_dec_ref(x_220);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_219, 1);
lean_inc(x_226);
lean_dec_ref(x_219);
x_227 = lean_ctor_get(x_224, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_228 = x_224;
} else {
 lean_dec_ref(x_224);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_225, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_231 = x_225;
} else {
 lean_dec_ref(x_225);
 x_231 = lean_box(0);
}
x_246 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_247 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_246, x_218, x_226);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_unbox(x_248);
lean_dec(x_248);
if (x_249 == 0)
{
lean_object* x_250; 
lean_dec(x_228);
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_dec_ref(x_247);
x_232 = x_2;
x_233 = x_3;
x_234 = x_4;
x_235 = x_5;
x_236 = x_6;
x_237 = x_7;
x_238 = x_8;
x_239 = x_218;
x_240 = x_10;
x_241 = x_250;
goto block_245;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_247, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_252 = x_247;
} else {
 lean_dec_ref(x_247);
 x_252 = lean_box(0);
}
x_253 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_227, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_218, x_10, x_251);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec_ref(x_253);
x_256 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_218, x_10, x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec_ref(x_256);
x_259 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_229, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_218, x_10, x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec_ref(x_259);
x_262 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_263 = l_Lean_MessageData_ofExpr(x_254);
if (lean_is_scalar(x_252)) {
 x_264 = lean_alloc_ctor(7, 2, 0);
} else {
 x_264 = x_252;
 lean_ctor_set_tag(x_264, 7);
}
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
if (lean_is_scalar(x_228)) {
 x_266 = lean_alloc_ctor(7, 2, 0);
} else {
 x_266 = x_228;
 lean_ctor_set_tag(x_266, 7);
}
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = l_Lean_MessageData_ofExpr(x_257);
x_268 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_265);
x_270 = l_Lean_MessageData_ofExpr(x_260);
x_271 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_262);
x_273 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_246, x_272, x_7, x_8, x_218, x_10, x_261);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec_ref(x_273);
x_232 = x_2;
x_233 = x_3;
x_234 = x_4;
x_235 = x_5;
x_236 = x_6;
x_237 = x_7;
x_238 = x_8;
x_239 = x_218;
x_240 = x_10;
x_241 = x_274;
goto block_245;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_257);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec_ref(x_218);
lean_dec_ref(x_1);
x_275 = lean_ctor_get(x_259, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_259, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_277 = x_259;
} else {
 lean_dec_ref(x_259);
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
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec_ref(x_218);
lean_dec_ref(x_1);
x_279 = lean_ctor_get(x_256, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_256, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_281 = x_256;
} else {
 lean_dec_ref(x_256);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_252);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec_ref(x_218);
lean_dec_ref(x_1);
x_283 = lean_ctor_get(x_253, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_253, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_285 = x_253;
} else {
 lean_dec_ref(x_253);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
block_245:
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_242, 0, x_227);
lean_ctor_set(x_242, 1, x_229);
lean_ctor_set(x_242, 2, x_1);
if (lean_is_scalar(x_231)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_231;
}
lean_ctor_set(x_243, 0, x_230);
lean_ctor_set(x_243, 1, x_242);
x_1 = x_243;
x_2 = x_232;
x_3 = x_233;
x_4 = x_234;
x_5 = x_235;
x_6 = x_236;
x_7 = x_237;
x_8 = x_238;
x_9 = x_239;
x_10 = x_240;
x_11 = x_241;
goto _start;
}
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec_ref(x_218);
lean_dec_ref(x_1);
x_287 = lean_ctor_get(x_219, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_219, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_289 = x_219;
} else {
 lean_dec_ref(x_219);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
}
else
{
lean_object* x_291; 
lean_dec_ref(x_213);
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_1);
x_291 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_203, x_11);
return x_291;
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
x_13 = lean_ctor_get(x_12, 21);
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
x_13 = lean_ctor_get(x_12, 22);
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
x_22 = lean_ctor_get(x_21, 19);
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
x_26 = lean_ctor_get(x_24, 19);
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
x_42 = lean_ctor_get(x_41, 19);
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
x_46 = lean_ctor_get(x_44, 19);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_47; 
x_47 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec_ref(x_47);
x_51 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_145 = lean_ctor_get(x_52, 33);
lean_inc_ref(x_145);
lean_dec(x_52);
x_146 = lean_ctor_get(x_145, 2);
x_147 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
x_148 = lean_nat_dec_lt(x_4, x_146);
if (x_148 == 0)
{
lean_object* x_149; 
lean_dec_ref(x_145);
x_149 = l_outOfBounds___redArg(x_147);
x_54 = x_149;
goto block_144;
}
else
{
lean_object* x_150; 
x_150 = l_Lean_PersistentArray_get_x21___redArg(x_147, x_145, x_4);
x_54 = x_150;
goto block_144;
}
block_144:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_55 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(x_2, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_st_ref_take(x_6, x_53);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 14);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_60, 3);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec_ref(x_58);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_59, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 3);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_59, 4);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_59, 5);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_59, 6);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_59, 7);
lean_inc_ref(x_70);
x_71 = lean_ctor_get_uint8(x_59, sizeof(void*)*17);
x_72 = lean_ctor_get(x_59, 8);
lean_inc(x_72);
x_73 = lean_ctor_get(x_59, 9);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_59, 10);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_59, 11);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_59, 12);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_59, 13);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_59, 15);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_59, 16);
lean_inc_ref(x_79);
lean_dec(x_59);
x_80 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_60, 2);
lean_inc_ref(x_82);
lean_dec_ref(x_60);
x_83 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_61, 2);
lean_inc_ref(x_85);
lean_dec_ref(x_61);
x_86 = lean_array_get_size(x_83);
x_87 = lean_nat_dec_lt(x_5, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_dec(x_56);
x_15 = x_64;
x_16 = x_57;
x_17 = x_80;
x_18 = x_79;
x_19 = x_73;
x_20 = x_72;
x_21 = x_84;
x_22 = x_85;
x_23 = x_78;
x_24 = x_69;
x_25 = x_70;
x_26 = x_75;
x_27 = x_74;
x_28 = x_66;
x_29 = x_76;
x_30 = x_82;
x_31 = x_68;
x_32 = x_81;
x_33 = x_62;
x_34 = x_71;
x_35 = x_77;
x_36 = x_63;
x_37 = x_65;
x_38 = x_67;
x_39 = x_83;
goto block_46;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_array_fget(x_83, x_5);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_88, 33);
x_91 = lean_box(0);
x_92 = lean_array_fset(x_83, x_5, x_91);
x_93 = l_Lean_PersistentArray_set___redArg(x_90, x_4, x_56);
lean_ctor_set(x_88, 33, x_93);
x_94 = lean_array_fset(x_92, x_5, x_88);
x_15 = x_64;
x_16 = x_57;
x_17 = x_80;
x_18 = x_79;
x_19 = x_73;
x_20 = x_72;
x_21 = x_84;
x_22 = x_85;
x_23 = x_78;
x_24 = x_69;
x_25 = x_70;
x_26 = x_75;
x_27 = x_74;
x_28 = x_66;
x_29 = x_76;
x_30 = x_82;
x_31 = x_68;
x_32 = x_81;
x_33 = x_62;
x_34 = x_71;
x_35 = x_77;
x_36 = x_63;
x_37 = x_65;
x_38 = x_67;
x_39 = x_94;
goto block_46;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_95 = lean_ctor_get(x_88, 0);
x_96 = lean_ctor_get(x_88, 1);
x_97 = lean_ctor_get(x_88, 2);
x_98 = lean_ctor_get(x_88, 3);
x_99 = lean_ctor_get(x_88, 4);
x_100 = lean_ctor_get(x_88, 5);
x_101 = lean_ctor_get(x_88, 6);
x_102 = lean_ctor_get(x_88, 7);
x_103 = lean_ctor_get(x_88, 8);
x_104 = lean_ctor_get(x_88, 9);
x_105 = lean_ctor_get(x_88, 10);
x_106 = lean_ctor_get(x_88, 11);
x_107 = lean_ctor_get(x_88, 12);
x_108 = lean_ctor_get(x_88, 13);
x_109 = lean_ctor_get(x_88, 14);
x_110 = lean_ctor_get(x_88, 15);
x_111 = lean_ctor_get(x_88, 16);
x_112 = lean_ctor_get(x_88, 17);
x_113 = lean_ctor_get(x_88, 18);
x_114 = lean_ctor_get(x_88, 19);
x_115 = lean_ctor_get(x_88, 20);
x_116 = lean_ctor_get(x_88, 21);
x_117 = lean_ctor_get(x_88, 22);
x_118 = lean_ctor_get(x_88, 23);
x_119 = lean_ctor_get(x_88, 24);
x_120 = lean_ctor_get(x_88, 25);
x_121 = lean_ctor_get(x_88, 26);
x_122 = lean_ctor_get(x_88, 27);
x_123 = lean_ctor_get(x_88, 28);
x_124 = lean_ctor_get(x_88, 29);
x_125 = lean_ctor_get(x_88, 30);
x_126 = lean_ctor_get(x_88, 31);
x_127 = lean_ctor_get(x_88, 32);
x_128 = lean_ctor_get(x_88, 33);
x_129 = lean_ctor_get(x_88, 34);
x_130 = lean_ctor_get(x_88, 35);
x_131 = lean_ctor_get(x_88, 36);
x_132 = lean_ctor_get_uint8(x_88, sizeof(void*)*43);
x_133 = lean_ctor_get(x_88, 37);
x_134 = lean_ctor_get(x_88, 38);
x_135 = lean_ctor_get(x_88, 39);
x_136 = lean_ctor_get(x_88, 40);
x_137 = lean_ctor_get(x_88, 41);
x_138 = lean_ctor_get(x_88, 42);
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
lean_inc(x_95);
lean_dec(x_88);
x_139 = lean_box(0);
x_140 = lean_array_fset(x_83, x_5, x_139);
x_141 = l_Lean_PersistentArray_set___redArg(x_128, x_4, x_56);
x_142 = lean_alloc_ctor(0, 43, 1);
lean_ctor_set(x_142, 0, x_95);
lean_ctor_set(x_142, 1, x_96);
lean_ctor_set(x_142, 2, x_97);
lean_ctor_set(x_142, 3, x_98);
lean_ctor_set(x_142, 4, x_99);
lean_ctor_set(x_142, 5, x_100);
lean_ctor_set(x_142, 6, x_101);
lean_ctor_set(x_142, 7, x_102);
lean_ctor_set(x_142, 8, x_103);
lean_ctor_set(x_142, 9, x_104);
lean_ctor_set(x_142, 10, x_105);
lean_ctor_set(x_142, 11, x_106);
lean_ctor_set(x_142, 12, x_107);
lean_ctor_set(x_142, 13, x_108);
lean_ctor_set(x_142, 14, x_109);
lean_ctor_set(x_142, 15, x_110);
lean_ctor_set(x_142, 16, x_111);
lean_ctor_set(x_142, 17, x_112);
lean_ctor_set(x_142, 18, x_113);
lean_ctor_set(x_142, 19, x_114);
lean_ctor_set(x_142, 20, x_115);
lean_ctor_set(x_142, 21, x_116);
lean_ctor_set(x_142, 22, x_117);
lean_ctor_set(x_142, 23, x_118);
lean_ctor_set(x_142, 24, x_119);
lean_ctor_set(x_142, 25, x_120);
lean_ctor_set(x_142, 26, x_121);
lean_ctor_set(x_142, 27, x_122);
lean_ctor_set(x_142, 28, x_123);
lean_ctor_set(x_142, 29, x_124);
lean_ctor_set(x_142, 30, x_125);
lean_ctor_set(x_142, 31, x_126);
lean_ctor_set(x_142, 32, x_127);
lean_ctor_set(x_142, 33, x_141);
lean_ctor_set(x_142, 34, x_129);
lean_ctor_set(x_142, 35, x_130);
lean_ctor_set(x_142, 36, x_131);
lean_ctor_set(x_142, 37, x_133);
lean_ctor_set(x_142, 38, x_134);
lean_ctor_set(x_142, 39, x_135);
lean_ctor_set(x_142, 40, x_136);
lean_ctor_set(x_142, 41, x_137);
lean_ctor_set(x_142, 42, x_138);
lean_ctor_set_uint8(x_142, sizeof(void*)*43, x_132);
x_143 = lean_array_fset(x_140, x_5, x_142);
x_15 = x_64;
x_16 = x_57;
x_17 = x_80;
x_18 = x_79;
x_19 = x_73;
x_20 = x_72;
x_21 = x_84;
x_22 = x_85;
x_23 = x_78;
x_24 = x_69;
x_25 = x_70;
x_26 = x_75;
x_27 = x_74;
x_28 = x_66;
x_29 = x_76;
x_30 = x_82;
x_31 = x_68;
x_32 = x_81;
x_33 = x_62;
x_34 = x_71;
x_35 = x_77;
x_36 = x_63;
x_37 = x_65;
x_38 = x_67;
x_39 = x_143;
goto block_46;
}
}
}
}
else
{
uint8_t x_151; 
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
x_151 = !lean_is_exclusive(x_51);
if (x_151 == 0)
{
return x_51;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_51, 0);
x_153 = lean_ctor_get(x_51, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_51);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
uint8_t x_155; 
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
x_155 = !lean_is_exclusive(x_47);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_47, 0);
lean_dec(x_156);
x_157 = lean_box(0);
lean_ctor_set(x_47, 0, x_157);
return x_47;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_47, 1);
lean_inc(x_158);
lean_dec(x_47);
x_159 = lean_box(0);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
else
{
uint8_t x_161; 
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
x_161 = !lean_is_exclusive(x_47);
if (x_161 == 0)
{
return x_47;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_47, 0);
x_163 = lean_ctor_get(x_47, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_47);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
block_46:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_21);
lean_ctor_set(x_40, 2, x_22);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_17);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_15);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_28);
lean_ctor_set(x_42, 4, x_38);
lean_ctor_set(x_42, 5, x_31);
lean_ctor_set(x_42, 6, x_24);
lean_ctor_set(x_42, 7, x_25);
lean_ctor_set(x_42, 8, x_20);
lean_ctor_set(x_42, 9, x_19);
lean_ctor_set(x_42, 10, x_27);
lean_ctor_set(x_42, 11, x_26);
lean_ctor_set(x_42, 12, x_29);
lean_ctor_set(x_42, 13, x_35);
lean_ctor_set(x_42, 14, x_41);
lean_ctor_set(x_42, 15, x_23);
lean_ctor_set(x_42, 16, x_18);
lean_ctor_set_uint8(x_42, sizeof(void*)*17, x_34);
x_43 = lean_st_ref_set(x_6, x_42, x_33);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_44);
lean_dec_ref(x_16);
return x_45;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_47; 
x_47 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec_ref(x_47);
x_51 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_145 = lean_ctor_get(x_52, 34);
lean_inc_ref(x_145);
lean_dec(x_52);
x_146 = lean_ctor_get(x_145, 2);
x_147 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
x_148 = lean_nat_dec_lt(x_4, x_146);
if (x_148 == 0)
{
lean_object* x_149; 
lean_dec_ref(x_145);
x_149 = l_outOfBounds___redArg(x_147);
x_54 = x_149;
goto block_144;
}
else
{
lean_object* x_150; 
x_150 = l_Lean_PersistentArray_get_x21___redArg(x_147, x_145, x_4);
x_54 = x_150;
goto block_144;
}
block_144:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_55 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(x_2, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_st_ref_take(x_6, x_53);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 14);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_60, 3);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec_ref(x_58);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_59, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 3);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_59, 4);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_59, 5);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_59, 6);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_59, 7);
lean_inc_ref(x_70);
x_71 = lean_ctor_get_uint8(x_59, sizeof(void*)*17);
x_72 = lean_ctor_get(x_59, 8);
lean_inc(x_72);
x_73 = lean_ctor_get(x_59, 9);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_59, 10);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_59, 11);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_59, 12);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_59, 13);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_59, 15);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_59, 16);
lean_inc_ref(x_79);
lean_dec(x_59);
x_80 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_60, 2);
lean_inc_ref(x_82);
lean_dec_ref(x_60);
x_83 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_61, 2);
lean_inc_ref(x_85);
lean_dec_ref(x_61);
x_86 = lean_array_get_size(x_83);
x_87 = lean_nat_dec_lt(x_5, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_dec(x_56);
x_15 = x_65;
x_16 = x_69;
x_17 = x_75;
x_18 = x_62;
x_19 = x_57;
x_20 = x_71;
x_21 = x_74;
x_22 = x_76;
x_23 = x_81;
x_24 = x_72;
x_25 = x_63;
x_26 = x_68;
x_27 = x_66;
x_28 = x_79;
x_29 = x_78;
x_30 = x_84;
x_31 = x_85;
x_32 = x_64;
x_33 = x_82;
x_34 = x_67;
x_35 = x_70;
x_36 = x_73;
x_37 = x_80;
x_38 = x_77;
x_39 = x_83;
goto block_46;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_array_fget(x_83, x_5);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_88, 34);
x_91 = lean_box(0);
x_92 = lean_array_fset(x_83, x_5, x_91);
x_93 = l_Lean_PersistentArray_set___redArg(x_90, x_4, x_56);
lean_ctor_set(x_88, 34, x_93);
x_94 = lean_array_fset(x_92, x_5, x_88);
x_15 = x_65;
x_16 = x_69;
x_17 = x_75;
x_18 = x_62;
x_19 = x_57;
x_20 = x_71;
x_21 = x_74;
x_22 = x_76;
x_23 = x_81;
x_24 = x_72;
x_25 = x_63;
x_26 = x_68;
x_27 = x_66;
x_28 = x_79;
x_29 = x_78;
x_30 = x_84;
x_31 = x_85;
x_32 = x_64;
x_33 = x_82;
x_34 = x_67;
x_35 = x_70;
x_36 = x_73;
x_37 = x_80;
x_38 = x_77;
x_39 = x_94;
goto block_46;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_95 = lean_ctor_get(x_88, 0);
x_96 = lean_ctor_get(x_88, 1);
x_97 = lean_ctor_get(x_88, 2);
x_98 = lean_ctor_get(x_88, 3);
x_99 = lean_ctor_get(x_88, 4);
x_100 = lean_ctor_get(x_88, 5);
x_101 = lean_ctor_get(x_88, 6);
x_102 = lean_ctor_get(x_88, 7);
x_103 = lean_ctor_get(x_88, 8);
x_104 = lean_ctor_get(x_88, 9);
x_105 = lean_ctor_get(x_88, 10);
x_106 = lean_ctor_get(x_88, 11);
x_107 = lean_ctor_get(x_88, 12);
x_108 = lean_ctor_get(x_88, 13);
x_109 = lean_ctor_get(x_88, 14);
x_110 = lean_ctor_get(x_88, 15);
x_111 = lean_ctor_get(x_88, 16);
x_112 = lean_ctor_get(x_88, 17);
x_113 = lean_ctor_get(x_88, 18);
x_114 = lean_ctor_get(x_88, 19);
x_115 = lean_ctor_get(x_88, 20);
x_116 = lean_ctor_get(x_88, 21);
x_117 = lean_ctor_get(x_88, 22);
x_118 = lean_ctor_get(x_88, 23);
x_119 = lean_ctor_get(x_88, 24);
x_120 = lean_ctor_get(x_88, 25);
x_121 = lean_ctor_get(x_88, 26);
x_122 = lean_ctor_get(x_88, 27);
x_123 = lean_ctor_get(x_88, 28);
x_124 = lean_ctor_get(x_88, 29);
x_125 = lean_ctor_get(x_88, 30);
x_126 = lean_ctor_get(x_88, 31);
x_127 = lean_ctor_get(x_88, 32);
x_128 = lean_ctor_get(x_88, 33);
x_129 = lean_ctor_get(x_88, 34);
x_130 = lean_ctor_get(x_88, 35);
x_131 = lean_ctor_get(x_88, 36);
x_132 = lean_ctor_get_uint8(x_88, sizeof(void*)*43);
x_133 = lean_ctor_get(x_88, 37);
x_134 = lean_ctor_get(x_88, 38);
x_135 = lean_ctor_get(x_88, 39);
x_136 = lean_ctor_get(x_88, 40);
x_137 = lean_ctor_get(x_88, 41);
x_138 = lean_ctor_get(x_88, 42);
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
lean_inc(x_95);
lean_dec(x_88);
x_139 = lean_box(0);
x_140 = lean_array_fset(x_83, x_5, x_139);
x_141 = l_Lean_PersistentArray_set___redArg(x_129, x_4, x_56);
x_142 = lean_alloc_ctor(0, 43, 1);
lean_ctor_set(x_142, 0, x_95);
lean_ctor_set(x_142, 1, x_96);
lean_ctor_set(x_142, 2, x_97);
lean_ctor_set(x_142, 3, x_98);
lean_ctor_set(x_142, 4, x_99);
lean_ctor_set(x_142, 5, x_100);
lean_ctor_set(x_142, 6, x_101);
lean_ctor_set(x_142, 7, x_102);
lean_ctor_set(x_142, 8, x_103);
lean_ctor_set(x_142, 9, x_104);
lean_ctor_set(x_142, 10, x_105);
lean_ctor_set(x_142, 11, x_106);
lean_ctor_set(x_142, 12, x_107);
lean_ctor_set(x_142, 13, x_108);
lean_ctor_set(x_142, 14, x_109);
lean_ctor_set(x_142, 15, x_110);
lean_ctor_set(x_142, 16, x_111);
lean_ctor_set(x_142, 17, x_112);
lean_ctor_set(x_142, 18, x_113);
lean_ctor_set(x_142, 19, x_114);
lean_ctor_set(x_142, 20, x_115);
lean_ctor_set(x_142, 21, x_116);
lean_ctor_set(x_142, 22, x_117);
lean_ctor_set(x_142, 23, x_118);
lean_ctor_set(x_142, 24, x_119);
lean_ctor_set(x_142, 25, x_120);
lean_ctor_set(x_142, 26, x_121);
lean_ctor_set(x_142, 27, x_122);
lean_ctor_set(x_142, 28, x_123);
lean_ctor_set(x_142, 29, x_124);
lean_ctor_set(x_142, 30, x_125);
lean_ctor_set(x_142, 31, x_126);
lean_ctor_set(x_142, 32, x_127);
lean_ctor_set(x_142, 33, x_128);
lean_ctor_set(x_142, 34, x_141);
lean_ctor_set(x_142, 35, x_130);
lean_ctor_set(x_142, 36, x_131);
lean_ctor_set(x_142, 37, x_133);
lean_ctor_set(x_142, 38, x_134);
lean_ctor_set(x_142, 39, x_135);
lean_ctor_set(x_142, 40, x_136);
lean_ctor_set(x_142, 41, x_137);
lean_ctor_set(x_142, 42, x_138);
lean_ctor_set_uint8(x_142, sizeof(void*)*43, x_132);
x_143 = lean_array_fset(x_140, x_5, x_142);
x_15 = x_65;
x_16 = x_69;
x_17 = x_75;
x_18 = x_62;
x_19 = x_57;
x_20 = x_71;
x_21 = x_74;
x_22 = x_76;
x_23 = x_81;
x_24 = x_72;
x_25 = x_63;
x_26 = x_68;
x_27 = x_66;
x_28 = x_79;
x_29 = x_78;
x_30 = x_84;
x_31 = x_85;
x_32 = x_64;
x_33 = x_82;
x_34 = x_67;
x_35 = x_70;
x_36 = x_73;
x_37 = x_80;
x_38 = x_77;
x_39 = x_143;
goto block_46;
}
}
}
}
else
{
uint8_t x_151; 
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
x_151 = !lean_is_exclusive(x_51);
if (x_151 == 0)
{
return x_51;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_51, 0);
x_153 = lean_ctor_get(x_51, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_51);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
uint8_t x_155; 
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
x_155 = !lean_is_exclusive(x_47);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_47, 0);
lean_dec(x_156);
x_157 = lean_box(0);
lean_ctor_set(x_47, 0, x_157);
return x_47;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_47, 1);
lean_inc(x_158);
lean_dec(x_47);
x_159 = lean_box(0);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
else
{
uint8_t x_161; 
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
x_161 = !lean_is_exclusive(x_47);
if (x_161 == 0)
{
return x_47;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_47, 0);
x_163 = lean_ctor_get(x_47, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_47);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
block_46:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_31);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_23);
lean_ctor_set(x_41, 2, x_33);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_42, 0, x_25);
lean_ctor_set(x_42, 1, x_32);
lean_ctor_set(x_42, 2, x_15);
lean_ctor_set(x_42, 3, x_27);
lean_ctor_set(x_42, 4, x_34);
lean_ctor_set(x_42, 5, x_26);
lean_ctor_set(x_42, 6, x_16);
lean_ctor_set(x_42, 7, x_35);
lean_ctor_set(x_42, 8, x_24);
lean_ctor_set(x_42, 9, x_36);
lean_ctor_set(x_42, 10, x_21);
lean_ctor_set(x_42, 11, x_17);
lean_ctor_set(x_42, 12, x_22);
lean_ctor_set(x_42, 13, x_38);
lean_ctor_set(x_42, 14, x_41);
lean_ctor_set(x_42, 15, x_29);
lean_ctor_set(x_42, 16, x_28);
lean_ctor_set_uint8(x_42, sizeof(void*)*17, x_20);
x_43 = lean_st_ref_set(x_6, x_42, x_18);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_44);
lean_dec_ref(x_19);
return x_45;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2;
x_153 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_152, x_9, x_11);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec_ref(x_153);
x_48 = x_2;
x_49 = x_3;
x_50 = x_4;
x_51 = x_5;
x_52 = x_6;
x_53 = x_7;
x_54 = x_8;
x_55 = x_9;
x_56 = x_10;
x_57 = x_156;
goto block_151;
}
else
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_153);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_153, 1);
x_159 = lean_ctor_get(x_153, 0);
lean_dec(x_159);
x_160 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_158);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
x_163 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_164 = l_Lean_MessageData_ofExpr(x_161);
lean_ctor_set_tag(x_153, 7);
lean_ctor_set(x_153, 1, x_164);
lean_ctor_set(x_153, 0, x_163);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_153);
lean_ctor_set(x_165, 1, x_163);
x_166 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_152, x_165, x_7, x_8, x_9, x_10, x_162);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec_ref(x_166);
x_48 = x_2;
x_49 = x_3;
x_50 = x_4;
x_51 = x_5;
x_52 = x_6;
x_53 = x_7;
x_54 = x_8;
x_55 = x_9;
x_56 = x_10;
x_57 = x_167;
goto block_151;
}
else
{
uint8_t x_168; 
lean_free_object(x_153);
x_168 = !lean_is_exclusive(x_160);
if (x_168 == 0)
{
return x_160;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_160, 0);
x_170 = lean_ctor_get(x_160, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_160);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_153, 1);
lean_inc(x_172);
lean_dec(x_153);
x_173 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec_ref(x_173);
x_176 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_177 = l_Lean_MessageData_ofExpr(x_174);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_176);
x_180 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_152, x_179, x_7, x_8, x_9, x_10, x_175);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec_ref(x_180);
x_48 = x_2;
x_49 = x_3;
x_50 = x_4;
x_51 = x_5;
x_52 = x_6;
x_53 = x_7;
x_54 = x_8;
x_55 = x_9;
x_56 = x_10;
x_57 = x_181;
goto block_151;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_173, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_173, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_184 = x_173;
} else {
 lean_dec_ref(x_173);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
block_47:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_33);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_15);
lean_ctor_set(x_38, 2, x_18);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_20);
lean_ctor_set(x_39, 2, x_28);
lean_ctor_set(x_39, 3, x_13);
lean_ctor_set(x_39, 4, x_24);
lean_ctor_set(x_39, 5, x_34);
lean_ctor_set(x_39, 6, x_14);
lean_ctor_set(x_39, 7, x_22);
lean_ctor_set(x_39, 8, x_26);
lean_ctor_set(x_39, 9, x_35);
lean_ctor_set(x_39, 10, x_19);
lean_ctor_set(x_39, 11, x_25);
lean_ctor_set(x_39, 12, x_29);
lean_ctor_set(x_39, 13, x_12);
lean_ctor_set(x_39, 14, x_38);
lean_ctor_set(x_39, 15, x_23);
lean_ctor_set(x_39, 16, x_17);
lean_ctor_set_uint8(x_39, sizeof(void*)*17, x_31);
x_40 = lean_st_ref_set(x_16, x_39, x_21);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
block_151:
{
lean_object* x_58; 
x_58 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_st_ref_take(x_49, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 14);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_63, 3);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec_ref(x_61);
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_62, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 3);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_62, 4);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_62, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_62, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_62, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get_uint8(x_62, sizeof(void*)*17);
x_75 = lean_ctor_get(x_62, 8);
lean_inc(x_75);
x_76 = lean_ctor_get(x_62, 9);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_62, 10);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_62, 11);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_62, 12);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_62, 13);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_62, 15);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_62, 16);
lean_inc_ref(x_82);
lean_dec(x_62);
x_83 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_85);
lean_dec_ref(x_63);
x_86 = lean_ctor_get(x_64, 0);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_64, 2);
lean_inc_ref(x_88);
lean_dec_ref(x_64);
x_89 = lean_array_get_size(x_86);
x_90 = lean_nat_dec_lt(x_48, x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_dec(x_59);
x_12 = x_80;
x_13 = x_69;
x_14 = x_72;
x_15 = x_84;
x_16 = x_49;
x_17 = x_82;
x_18 = x_85;
x_19 = x_77;
x_20 = x_67;
x_21 = x_65;
x_22 = x_73;
x_23 = x_81;
x_24 = x_70;
x_25 = x_78;
x_26 = x_75;
x_27 = x_83;
x_28 = x_68;
x_29 = x_79;
x_30 = x_66;
x_31 = x_74;
x_32 = x_87;
x_33 = x_88;
x_34 = x_71;
x_35 = x_76;
x_36 = x_86;
goto block_47;
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_array_fget(x_86, x_48);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_91, 42);
x_94 = lean_box(0);
x_95 = lean_array_fset(x_86, x_48, x_94);
x_96 = l_Lean_PersistentArray_push___redArg(x_93, x_59);
lean_ctor_set(x_91, 42, x_96);
x_97 = lean_array_fset(x_95, x_48, x_91);
x_12 = x_80;
x_13 = x_69;
x_14 = x_72;
x_15 = x_84;
x_16 = x_49;
x_17 = x_82;
x_18 = x_85;
x_19 = x_77;
x_20 = x_67;
x_21 = x_65;
x_22 = x_73;
x_23 = x_81;
x_24 = x_70;
x_25 = x_78;
x_26 = x_75;
x_27 = x_83;
x_28 = x_68;
x_29 = x_79;
x_30 = x_66;
x_31 = x_74;
x_32 = x_87;
x_33 = x_88;
x_34 = x_71;
x_35 = x_76;
x_36 = x_97;
goto block_47;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_98 = lean_ctor_get(x_91, 0);
x_99 = lean_ctor_get(x_91, 1);
x_100 = lean_ctor_get(x_91, 2);
x_101 = lean_ctor_get(x_91, 3);
x_102 = lean_ctor_get(x_91, 4);
x_103 = lean_ctor_get(x_91, 5);
x_104 = lean_ctor_get(x_91, 6);
x_105 = lean_ctor_get(x_91, 7);
x_106 = lean_ctor_get(x_91, 8);
x_107 = lean_ctor_get(x_91, 9);
x_108 = lean_ctor_get(x_91, 10);
x_109 = lean_ctor_get(x_91, 11);
x_110 = lean_ctor_get(x_91, 12);
x_111 = lean_ctor_get(x_91, 13);
x_112 = lean_ctor_get(x_91, 14);
x_113 = lean_ctor_get(x_91, 15);
x_114 = lean_ctor_get(x_91, 16);
x_115 = lean_ctor_get(x_91, 17);
x_116 = lean_ctor_get(x_91, 18);
x_117 = lean_ctor_get(x_91, 19);
x_118 = lean_ctor_get(x_91, 20);
x_119 = lean_ctor_get(x_91, 21);
x_120 = lean_ctor_get(x_91, 22);
x_121 = lean_ctor_get(x_91, 23);
x_122 = lean_ctor_get(x_91, 24);
x_123 = lean_ctor_get(x_91, 25);
x_124 = lean_ctor_get(x_91, 26);
x_125 = lean_ctor_get(x_91, 27);
x_126 = lean_ctor_get(x_91, 28);
x_127 = lean_ctor_get(x_91, 29);
x_128 = lean_ctor_get(x_91, 30);
x_129 = lean_ctor_get(x_91, 31);
x_130 = lean_ctor_get(x_91, 32);
x_131 = lean_ctor_get(x_91, 33);
x_132 = lean_ctor_get(x_91, 34);
x_133 = lean_ctor_get(x_91, 35);
x_134 = lean_ctor_get(x_91, 36);
x_135 = lean_ctor_get_uint8(x_91, sizeof(void*)*43);
x_136 = lean_ctor_get(x_91, 37);
x_137 = lean_ctor_get(x_91, 38);
x_138 = lean_ctor_get(x_91, 39);
x_139 = lean_ctor_get(x_91, 40);
x_140 = lean_ctor_get(x_91, 41);
x_141 = lean_ctor_get(x_91, 42);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
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
lean_dec(x_91);
x_142 = lean_box(0);
x_143 = lean_array_fset(x_86, x_48, x_142);
x_144 = l_Lean_PersistentArray_push___redArg(x_141, x_59);
x_145 = lean_alloc_ctor(0, 43, 1);
lean_ctor_set(x_145, 0, x_98);
lean_ctor_set(x_145, 1, x_99);
lean_ctor_set(x_145, 2, x_100);
lean_ctor_set(x_145, 3, x_101);
lean_ctor_set(x_145, 4, x_102);
lean_ctor_set(x_145, 5, x_103);
lean_ctor_set(x_145, 6, x_104);
lean_ctor_set(x_145, 7, x_105);
lean_ctor_set(x_145, 8, x_106);
lean_ctor_set(x_145, 9, x_107);
lean_ctor_set(x_145, 10, x_108);
lean_ctor_set(x_145, 11, x_109);
lean_ctor_set(x_145, 12, x_110);
lean_ctor_set(x_145, 13, x_111);
lean_ctor_set(x_145, 14, x_112);
lean_ctor_set(x_145, 15, x_113);
lean_ctor_set(x_145, 16, x_114);
lean_ctor_set(x_145, 17, x_115);
lean_ctor_set(x_145, 18, x_116);
lean_ctor_set(x_145, 19, x_117);
lean_ctor_set(x_145, 20, x_118);
lean_ctor_set(x_145, 21, x_119);
lean_ctor_set(x_145, 22, x_120);
lean_ctor_set(x_145, 23, x_121);
lean_ctor_set(x_145, 24, x_122);
lean_ctor_set(x_145, 25, x_123);
lean_ctor_set(x_145, 26, x_124);
lean_ctor_set(x_145, 27, x_125);
lean_ctor_set(x_145, 28, x_126);
lean_ctor_set(x_145, 29, x_127);
lean_ctor_set(x_145, 30, x_128);
lean_ctor_set(x_145, 31, x_129);
lean_ctor_set(x_145, 32, x_130);
lean_ctor_set(x_145, 33, x_131);
lean_ctor_set(x_145, 34, x_132);
lean_ctor_set(x_145, 35, x_133);
lean_ctor_set(x_145, 36, x_134);
lean_ctor_set(x_145, 37, x_136);
lean_ctor_set(x_145, 38, x_137);
lean_ctor_set(x_145, 39, x_138);
lean_ctor_set(x_145, 40, x_139);
lean_ctor_set(x_145, 41, x_140);
lean_ctor_set(x_145, 42, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*43, x_135);
x_146 = lean_array_fset(x_143, x_48, x_145);
x_12 = x_80;
x_13 = x_69;
x_14 = x_72;
x_15 = x_84;
x_16 = x_49;
x_17 = x_82;
x_18 = x_85;
x_19 = x_77;
x_20 = x_67;
x_21 = x_65;
x_22 = x_73;
x_23 = x_81;
x_24 = x_70;
x_25 = x_78;
x_26 = x_75;
x_27 = x_83;
x_28 = x_68;
x_29 = x_79;
x_30 = x_66;
x_31 = x_74;
x_32 = x_87;
x_33 = x_88;
x_34 = x_71;
x_35 = x_76;
x_36 = x_146;
goto block_47;
}
}
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_58);
if (x_147 == 0)
{
return x_58;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_58, 0);
x_149 = lean_ctor_get(x_58, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_58);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
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
x_26 = lean_ctor_get(x_9, 13);
x_27 = lean_nat_dec_eq(x_16, x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_16, x_29);
lean_dec(x_16);
lean_ctor_set(x_9, 3, x_30);
x_31 = l_Lean_Grind_Linarith_Poly_findVarToSubst(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec_ref(x_9);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec_ref(x_32);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_dec_ref(x_31);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_ctor_get(x_41, 0);
x_46 = l_Lean_Grind_Linarith_Poly_coeff(x_45, x_44);
lean_inc_ref(x_1);
x_47 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_46, x_44, x_41, x_43, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
lean_dec(x_44);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_1);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_dec_ref(x_47);
x_60 = lean_ctor_get(x_48, 0);
lean_inc(x_60);
lean_dec_ref(x_48);
x_1 = x_60;
x_11 = x_59;
goto _start;
}
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_1);
return x_47;
}
}
}
else
{
uint8_t x_62; 
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_62 = !lean_is_exclusive(x_31);
if (x_62 == 0)
{
return x_31;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_31, 0);
x_64 = lean_ctor_get(x_31, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_31);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; 
lean_free_object(x_9);
lean_dec_ref(x_26);
lean_dec(x_25);
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
x_66 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_18, x_11);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; uint8_t x_83; 
x_67 = lean_ctor_get(x_9, 0);
x_68 = lean_ctor_get(x_9, 1);
x_69 = lean_ctor_get(x_9, 2);
x_70 = lean_ctor_get(x_9, 3);
x_71 = lean_ctor_get(x_9, 4);
x_72 = lean_ctor_get(x_9, 5);
x_73 = lean_ctor_get(x_9, 6);
x_74 = lean_ctor_get(x_9, 7);
x_75 = lean_ctor_get(x_9, 8);
x_76 = lean_ctor_get(x_9, 9);
x_77 = lean_ctor_get(x_9, 10);
x_78 = lean_ctor_get(x_9, 11);
x_79 = lean_ctor_get_uint8(x_9, sizeof(void*)*14);
x_80 = lean_ctor_get(x_9, 12);
x_81 = lean_ctor_get_uint8(x_9, sizeof(void*)*14 + 1);
x_82 = lean_ctor_get(x_9, 13);
lean_inc(x_82);
lean_inc(x_80);
lean_inc(x_78);
lean_inc(x_77);
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
lean_dec(x_9);
x_83 = lean_nat_dec_eq(x_70, x_71);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_1, 0);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_70, x_85);
lean_dec(x_70);
x_87 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_87, 0, x_67);
lean_ctor_set(x_87, 1, x_68);
lean_ctor_set(x_87, 2, x_69);
lean_ctor_set(x_87, 3, x_86);
lean_ctor_set(x_87, 4, x_71);
lean_ctor_set(x_87, 5, x_72);
lean_ctor_set(x_87, 6, x_73);
lean_ctor_set(x_87, 7, x_74);
lean_ctor_set(x_87, 8, x_75);
lean_ctor_set(x_87, 9, x_76);
lean_ctor_set(x_87, 10, x_77);
lean_ctor_set(x_87, 11, x_78);
lean_ctor_set(x_87, 12, x_80);
lean_ctor_set(x_87, 13, x_82);
lean_ctor_set_uint8(x_87, sizeof(void*)*14, x_79);
lean_ctor_set_uint8(x_87, sizeof(void*)*14 + 1, x_81);
x_88 = l_Lean_Grind_Linarith_Poly_findVarToSubst(x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_87, x_10, x_11);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_87);
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
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_1);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
lean_dec_ref(x_89);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_88, 1);
lean_inc(x_97);
lean_dec_ref(x_88);
x_98 = lean_ctor_get(x_94, 0);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_ctor_get(x_96, 0);
x_101 = l_Lean_Grind_Linarith_Poly_coeff(x_100, x_99);
lean_inc_ref(x_1);
x_102 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_101, x_99, x_96, x_98, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_87, x_10, x_97);
lean_dec(x_99);
lean_dec(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_87, x_10, x_104);
lean_dec_ref(x_87);
lean_dec_ref(x_1);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_111 = x_105;
} else {
 lean_dec_ref(x_105);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_1);
x_113 = lean_ctor_get(x_102, 1);
lean_inc(x_113);
lean_dec_ref(x_102);
x_114 = lean_ctor_get(x_103, 0);
lean_inc(x_114);
lean_dec_ref(x_103);
x_1 = x_114;
x_9 = x_87;
x_11 = x_113;
goto _start;
}
}
else
{
lean_dec_ref(x_87);
lean_dec_ref(x_1);
return x_102;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec_ref(x_87);
lean_dec_ref(x_1);
x_116 = lean_ctor_get(x_88, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_88, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_118 = x_88;
} else {
 lean_dec_ref(x_88);
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
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_1);
x_120 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_72, x_11);
return x_120;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_292; 
x_88 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0;
x_89 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_88, x_9, x_11);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1;
x_292 = lean_unbox(x_90);
lean_dec(x_90);
if (x_292 == 0)
{
x_196 = x_2;
x_197 = x_3;
x_198 = x_4;
x_199 = x_5;
x_200 = x_6;
x_201 = x_7;
x_202 = x_8;
x_203 = x_9;
x_204 = x_10;
x_205 = x_91;
goto block_291;
}
else
{
lean_object* x_293; 
x_293 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_91);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec_ref(x_293);
x_296 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_297 = l_Lean_MessageData_ofExpr(x_294);
x_298 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_296);
x_300 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_88, x_299, x_7, x_8, x_9, x_10, x_295);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
lean_dec_ref(x_300);
x_196 = x_2;
x_197 = x_3;
x_198 = x_4;
x_199 = x_5;
x_200 = x_6;
x_201 = x_7;
x_202 = x_8;
x_203 = x_9;
x_204 = x_10;
x_205 = x_301;
goto block_291;
}
else
{
uint8_t x_302; 
lean_dec(x_92);
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
x_302 = !lean_is_exclusive(x_293);
if (x_302 == 0)
{
return x_293;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_293, 0);
x_304 = lean_ctor_get(x_293, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_293);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
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
block_87:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_28);
lean_ctor_set(x_62, 1, x_51);
lean_ctor_set(x_62, 2, x_27);
lean_ctor_set(x_62, 3, x_61);
x_63 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_63, 0, x_36);
lean_ctor_set(x_63, 1, x_44);
lean_ctor_set(x_63, 2, x_39);
lean_ctor_set(x_63, 3, x_50);
lean_ctor_set(x_63, 4, x_33);
lean_ctor_set(x_63, 5, x_55);
lean_ctor_set(x_63, 6, x_41);
lean_ctor_set(x_63, 7, x_48);
lean_ctor_set(x_63, 8, x_38);
lean_ctor_set(x_63, 9, x_47);
lean_ctor_set(x_63, 10, x_45);
lean_ctor_set(x_63, 11, x_30);
lean_ctor_set(x_63, 12, x_57);
lean_ctor_set(x_63, 13, x_31);
lean_ctor_set(x_63, 14, x_62);
lean_ctor_set(x_63, 15, x_35);
lean_ctor_set(x_63, 16, x_56);
lean_ctor_set_uint8(x_63, sizeof(void*)*17, x_59);
x_64 = lean_st_ref_set(x_49, x_63, x_34);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(x_52, x_58, x_49, x_37, x_54, x_29, x_40, x_26, x_53, x_32, x_65);
lean_dec(x_32);
lean_dec_ref(x_53);
lean_dec(x_26);
lean_dec_ref(x_40);
lean_dec(x_29);
lean_dec_ref(x_54);
lean_dec(x_37);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
x_70 = 0;
x_71 = lean_unbox(x_68);
lean_dec(x_68);
x_72 = l_Lean_beqLBool____x40_Lean_Data_LBool_27903016____hygCtx___hyg_9_(x_71, x_70);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_58);
lean_dec(x_49);
lean_dec(x_46);
x_73 = lean_box(0);
lean_ctor_set(x_66, 0, x_73);
return x_66;
}
else
{
lean_object* x_74; 
lean_free_object(x_66);
x_74 = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(x_46, x_58, x_49, x_69);
lean_dec(x_49);
lean_dec(x_58);
lean_dec(x_46);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_66, 0);
x_76 = lean_ctor_get(x_66, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_66);
x_77 = 0;
x_78 = lean_unbox(x_75);
lean_dec(x_75);
x_79 = l_Lean_beqLBool____x40_Lean_Data_LBool_27903016____hygCtx___hyg_9_(x_78, x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_58);
lean_dec(x_49);
lean_dec(x_46);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
else
{
lean_object* x_82; 
x_82 = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(x_46, x_58, x_49, x_76);
lean_dec(x_49);
lean_dec(x_58);
lean_dec(x_46);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_58);
lean_dec(x_49);
lean_dec(x_46);
x_83 = !lean_is_exclusive(x_66);
if (x_83 == 0)
{
return x_66;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_66, 0);
x_85 = lean_ctor_get(x_66, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_66);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
block_195:
{
lean_object* x_107; 
x_107 = l_Lean_Grind_Linarith_Poly_updateOccs(x_94, x_97, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_st_ref_take(x_98, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 14);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_111, 3);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
lean_dec_ref(x_109);
x_114 = lean_ctor_get(x_110, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 1);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_110, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 3);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_110, 4);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_110, 5);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_110, 6);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_110, 7);
lean_inc_ref(x_121);
x_122 = lean_ctor_get_uint8(x_110, sizeof(void*)*17);
x_123 = lean_ctor_get(x_110, 8);
lean_inc(x_123);
x_124 = lean_ctor_get(x_110, 9);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_110, 10);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_110, 11);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_110, 12);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_110, 13);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_110, 15);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_110, 16);
lean_inc_ref(x_130);
lean_dec(x_110);
x_131 = lean_ctor_get(x_111, 0);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_111, 1);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_111, 2);
lean_inc_ref(x_133);
lean_dec_ref(x_111);
x_134 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_112, 1);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_112, 2);
lean_inc_ref(x_136);
lean_dec_ref(x_112);
x_137 = lean_array_get_size(x_134);
x_138 = lean_nat_dec_lt(x_97, x_137);
lean_dec(x_137);
if (x_138 == 0)
{
x_26 = x_103;
x_27 = x_133;
x_28 = x_131;
x_29 = x_101;
x_30 = x_126;
x_31 = x_128;
x_32 = x_105;
x_33 = x_118;
x_34 = x_113;
x_35 = x_129;
x_36 = x_114;
x_37 = x_99;
x_38 = x_123;
x_39 = x_116;
x_40 = x_102;
x_41 = x_120;
x_42 = x_135;
x_43 = x_136;
x_44 = x_115;
x_45 = x_125;
x_46 = x_96;
x_47 = x_124;
x_48 = x_121;
x_49 = x_98;
x_50 = x_117;
x_51 = x_132;
x_52 = x_95;
x_53 = x_104;
x_54 = x_100;
x_55 = x_119;
x_56 = x_130;
x_57 = x_127;
x_58 = x_97;
x_59 = x_122;
x_60 = x_134;
goto block_87;
}
else
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_array_fget(x_134, x_97);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_139, 35);
x_142 = lean_box(0);
x_143 = lean_array_fset(x_134, x_97, x_142);
lean_inc_ref(x_95);
x_144 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(x_95, x_93, x_141, x_96);
lean_ctor_set(x_139, 35, x_144);
x_145 = lean_array_fset(x_143, x_97, x_139);
x_26 = x_103;
x_27 = x_133;
x_28 = x_131;
x_29 = x_101;
x_30 = x_126;
x_31 = x_128;
x_32 = x_105;
x_33 = x_118;
x_34 = x_113;
x_35 = x_129;
x_36 = x_114;
x_37 = x_99;
x_38 = x_123;
x_39 = x_116;
x_40 = x_102;
x_41 = x_120;
x_42 = x_135;
x_43 = x_136;
x_44 = x_115;
x_45 = x_125;
x_46 = x_96;
x_47 = x_124;
x_48 = x_121;
x_49 = x_98;
x_50 = x_117;
x_51 = x_132;
x_52 = x_95;
x_53 = x_104;
x_54 = x_100;
x_55 = x_119;
x_56 = x_130;
x_57 = x_127;
x_58 = x_97;
x_59 = x_122;
x_60 = x_145;
goto block_87;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_146 = lean_ctor_get(x_139, 0);
x_147 = lean_ctor_get(x_139, 1);
x_148 = lean_ctor_get(x_139, 2);
x_149 = lean_ctor_get(x_139, 3);
x_150 = lean_ctor_get(x_139, 4);
x_151 = lean_ctor_get(x_139, 5);
x_152 = lean_ctor_get(x_139, 6);
x_153 = lean_ctor_get(x_139, 7);
x_154 = lean_ctor_get(x_139, 8);
x_155 = lean_ctor_get(x_139, 9);
x_156 = lean_ctor_get(x_139, 10);
x_157 = lean_ctor_get(x_139, 11);
x_158 = lean_ctor_get(x_139, 12);
x_159 = lean_ctor_get(x_139, 13);
x_160 = lean_ctor_get(x_139, 14);
x_161 = lean_ctor_get(x_139, 15);
x_162 = lean_ctor_get(x_139, 16);
x_163 = lean_ctor_get(x_139, 17);
x_164 = lean_ctor_get(x_139, 18);
x_165 = lean_ctor_get(x_139, 19);
x_166 = lean_ctor_get(x_139, 20);
x_167 = lean_ctor_get(x_139, 21);
x_168 = lean_ctor_get(x_139, 22);
x_169 = lean_ctor_get(x_139, 23);
x_170 = lean_ctor_get(x_139, 24);
x_171 = lean_ctor_get(x_139, 25);
x_172 = lean_ctor_get(x_139, 26);
x_173 = lean_ctor_get(x_139, 27);
x_174 = lean_ctor_get(x_139, 28);
x_175 = lean_ctor_get(x_139, 29);
x_176 = lean_ctor_get(x_139, 30);
x_177 = lean_ctor_get(x_139, 31);
x_178 = lean_ctor_get(x_139, 32);
x_179 = lean_ctor_get(x_139, 33);
x_180 = lean_ctor_get(x_139, 34);
x_181 = lean_ctor_get(x_139, 35);
x_182 = lean_ctor_get(x_139, 36);
x_183 = lean_ctor_get_uint8(x_139, sizeof(void*)*43);
x_184 = lean_ctor_get(x_139, 37);
x_185 = lean_ctor_get(x_139, 38);
x_186 = lean_ctor_get(x_139, 39);
x_187 = lean_ctor_get(x_139, 40);
x_188 = lean_ctor_get(x_139, 41);
x_189 = lean_ctor_get(x_139, 42);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
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
lean_dec(x_139);
x_190 = lean_box(0);
x_191 = lean_array_fset(x_134, x_97, x_190);
lean_inc_ref(x_95);
x_192 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(x_95, x_93, x_181, x_96);
x_193 = lean_alloc_ctor(0, 43, 1);
lean_ctor_set(x_193, 0, x_146);
lean_ctor_set(x_193, 1, x_147);
lean_ctor_set(x_193, 2, x_148);
lean_ctor_set(x_193, 3, x_149);
lean_ctor_set(x_193, 4, x_150);
lean_ctor_set(x_193, 5, x_151);
lean_ctor_set(x_193, 6, x_152);
lean_ctor_set(x_193, 7, x_153);
lean_ctor_set(x_193, 8, x_154);
lean_ctor_set(x_193, 9, x_155);
lean_ctor_set(x_193, 10, x_156);
lean_ctor_set(x_193, 11, x_157);
lean_ctor_set(x_193, 12, x_158);
lean_ctor_set(x_193, 13, x_159);
lean_ctor_set(x_193, 14, x_160);
lean_ctor_set(x_193, 15, x_161);
lean_ctor_set(x_193, 16, x_162);
lean_ctor_set(x_193, 17, x_163);
lean_ctor_set(x_193, 18, x_164);
lean_ctor_set(x_193, 19, x_165);
lean_ctor_set(x_193, 20, x_166);
lean_ctor_set(x_193, 21, x_167);
lean_ctor_set(x_193, 22, x_168);
lean_ctor_set(x_193, 23, x_169);
lean_ctor_set(x_193, 24, x_170);
lean_ctor_set(x_193, 25, x_171);
lean_ctor_set(x_193, 26, x_172);
lean_ctor_set(x_193, 27, x_173);
lean_ctor_set(x_193, 28, x_174);
lean_ctor_set(x_193, 29, x_175);
lean_ctor_set(x_193, 30, x_176);
lean_ctor_set(x_193, 31, x_177);
lean_ctor_set(x_193, 32, x_178);
lean_ctor_set(x_193, 33, x_179);
lean_ctor_set(x_193, 34, x_180);
lean_ctor_set(x_193, 35, x_192);
lean_ctor_set(x_193, 36, x_182);
lean_ctor_set(x_193, 37, x_184);
lean_ctor_set(x_193, 38, x_185);
lean_ctor_set(x_193, 39, x_186);
lean_ctor_set(x_193, 40, x_187);
lean_ctor_set(x_193, 41, x_188);
lean_ctor_set(x_193, 42, x_189);
lean_ctor_set_uint8(x_193, sizeof(void*)*43, x_183);
x_194 = lean_array_fset(x_191, x_97, x_193);
x_26 = x_103;
x_27 = x_133;
x_28 = x_131;
x_29 = x_101;
x_30 = x_126;
x_31 = x_128;
x_32 = x_105;
x_33 = x_118;
x_34 = x_113;
x_35 = x_129;
x_36 = x_114;
x_37 = x_99;
x_38 = x_123;
x_39 = x_116;
x_40 = x_102;
x_41 = x_120;
x_42 = x_135;
x_43 = x_136;
x_44 = x_115;
x_45 = x_125;
x_46 = x_96;
x_47 = x_124;
x_48 = x_121;
x_49 = x_98;
x_50 = x_117;
x_51 = x_132;
x_52 = x_95;
x_53 = x_104;
x_54 = x_100;
x_55 = x_119;
x_56 = x_130;
x_57 = x_127;
x_58 = x_97;
x_59 = x_122;
x_60 = x_194;
goto block_87;
}
}
}
else
{
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec_ref(x_95);
return x_107;
}
}
block_291:
{
lean_object* x_206; 
lean_inc_ref(x_203);
x_206 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(x_1, x_196, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
lean_dec(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_92);
x_208 = !lean_is_exclusive(x_206);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_206, 0);
lean_dec(x_209);
x_210 = lean_box(0);
lean_ctor_set(x_206, 0, x_210);
return x_206;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_206, 1);
lean_inc(x_211);
lean_dec(x_206);
x_212 = lean_box(0);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_207, 0);
lean_inc(x_214);
lean_dec_ref(x_207);
x_215 = lean_ctor_get(x_214, 0);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_206, 1);
lean_inc(x_216);
lean_dec_ref(x_206);
x_217 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3;
x_218 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_217, x_203, x_216);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_unbox(x_219);
lean_dec(x_219);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec(x_92);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec_ref(x_218);
x_12 = x_214;
x_13 = x_196;
x_14 = x_197;
x_15 = x_198;
x_16 = x_199;
x_17 = x_200;
x_18 = x_201;
x_19 = x_202;
x_20 = x_203;
x_21 = x_204;
x_22 = x_221;
goto block_25;
}
else
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_218);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_218, 1);
x_224 = lean_ctor_get(x_218, 0);
lean_dec(x_224);
x_225 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_214, x_196, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_223);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec_ref(x_225);
x_228 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_229 = l_Lean_MessageData_ofExpr(x_226);
lean_ctor_set_tag(x_218, 7);
lean_ctor_set(x_218, 1, x_229);
lean_ctor_set(x_218, 0, x_228);
if (lean_is_scalar(x_92)) {
 x_230 = lean_alloc_ctor(7, 2, 0);
} else {
 x_230 = x_92;
 lean_ctor_set_tag(x_230, 7);
}
lean_ctor_set(x_230, 0, x_218);
lean_ctor_set(x_230, 1, x_228);
x_231 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_217, x_230, x_201, x_202, x_203, x_204, x_227);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec_ref(x_231);
x_12 = x_214;
x_13 = x_196;
x_14 = x_197;
x_15 = x_198;
x_16 = x_199;
x_17 = x_200;
x_18 = x_201;
x_19 = x_202;
x_20 = x_203;
x_21 = x_204;
x_22 = x_232;
goto block_25;
}
else
{
uint8_t x_233; 
lean_free_object(x_218);
lean_dec(x_214);
lean_dec(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_92);
x_233 = !lean_is_exclusive(x_225);
if (x_233 == 0)
{
return x_225;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_225, 0);
x_235 = lean_ctor_get(x_225, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_225);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_218, 1);
lean_inc(x_237);
lean_dec(x_218);
x_238 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_214, x_196, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_237);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec_ref(x_238);
x_241 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_242 = l_Lean_MessageData_ofExpr(x_239);
x_243 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
if (lean_is_scalar(x_92)) {
 x_244 = lean_alloc_ctor(7, 2, 0);
} else {
 x_244 = x_92;
 lean_ctor_set_tag(x_244, 7);
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_241);
x_245 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_217, x_244, x_201, x_202, x_203, x_204, x_240);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec_ref(x_245);
x_12 = x_214;
x_13 = x_196;
x_14 = x_197;
x_15 = x_198;
x_16 = x_199;
x_17 = x_200;
x_18 = x_201;
x_19 = x_202;
x_20 = x_203;
x_21 = x_204;
x_22 = x_246;
goto block_25;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_214);
lean_dec(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_92);
x_247 = lean_ctor_get(x_238, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_238, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_249 = x_238;
} else {
 lean_dec_ref(x_238);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
lean_inc_ref(x_215);
x_251 = lean_ctor_get(x_206, 1);
lean_inc(x_251);
lean_dec_ref(x_206);
x_252 = lean_ctor_get(x_215, 1);
lean_inc(x_252);
x_253 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5;
x_254 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_253, x_203, x_251);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_unbox(x_255);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; 
lean_dec(x_92);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec_ref(x_254);
x_94 = x_215;
x_95 = x_214;
x_96 = x_252;
x_97 = x_196;
x_98 = x_197;
x_99 = x_198;
x_100 = x_199;
x_101 = x_200;
x_102 = x_201;
x_103 = x_202;
x_104 = x_203;
x_105 = x_204;
x_106 = x_257;
goto block_195;
}
else
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_254);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_254, 1);
x_260 = lean_ctor_get(x_254, 0);
lean_dec(x_260);
x_261 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_214, x_196, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_259);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec_ref(x_261);
x_264 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_265 = l_Lean_MessageData_ofExpr(x_262);
lean_ctor_set_tag(x_254, 7);
lean_ctor_set(x_254, 1, x_265);
lean_ctor_set(x_254, 0, x_264);
if (lean_is_scalar(x_92)) {
 x_266 = lean_alloc_ctor(7, 2, 0);
} else {
 x_266 = x_92;
 lean_ctor_set_tag(x_266, 7);
}
lean_ctor_set(x_266, 0, x_254);
lean_ctor_set(x_266, 1, x_264);
x_267 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_253, x_266, x_201, x_202, x_203, x_204, x_263);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec_ref(x_267);
x_94 = x_215;
x_95 = x_214;
x_96 = x_252;
x_97 = x_196;
x_98 = x_197;
x_99 = x_198;
x_100 = x_199;
x_101 = x_200;
x_102 = x_201;
x_103 = x_202;
x_104 = x_203;
x_105 = x_204;
x_106 = x_268;
goto block_195;
}
else
{
uint8_t x_269; 
lean_free_object(x_254);
lean_dec(x_252);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_92);
x_269 = !lean_is_exclusive(x_261);
if (x_269 == 0)
{
return x_261;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_261, 0);
x_271 = lean_ctor_get(x_261, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_261);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_254, 1);
lean_inc(x_273);
lean_dec(x_254);
x_274 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_214, x_196, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec_ref(x_274);
x_277 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_278 = l_Lean_MessageData_ofExpr(x_275);
x_279 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
if (lean_is_scalar(x_92)) {
 x_280 = lean_alloc_ctor(7, 2, 0);
} else {
 x_280 = x_92;
 lean_ctor_set_tag(x_280, 7);
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_277);
x_281 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_253, x_280, x_201, x_202, x_203, x_204, x_276);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec_ref(x_281);
x_94 = x_215;
x_95 = x_214;
x_96 = x_252;
x_97 = x_196;
x_98 = x_197;
x_99 = x_198;
x_100 = x_199;
x_101 = x_200;
x_102 = x_201;
x_103 = x_202;
x_104 = x_203;
x_105 = x_204;
x_106 = x_282;
goto block_195;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_252);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_92);
x_283 = lean_ctor_get(x_274, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_274, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_285 = x_274;
} else {
 lean_dec_ref(x_274);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
}
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_92);
x_287 = !lean_is_exclusive(x_206);
if (x_287 == 0)
{
return x_206;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_206, 0);
x_289 = lean_ctor_get(x_206, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_206);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_67; 
x_67 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec_ref(x_67);
x_71 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_165 = lean_ctor_get(x_72, 35);
lean_inc_ref(x_165);
lean_dec(x_72);
x_166 = lean_ctor_get(x_165, 2);
x_167 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1;
x_168 = lean_nat_dec_lt(x_4, x_166);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec_ref(x_165);
x_169 = l_outOfBounds___redArg(x_167);
x_74 = x_169;
goto block_164;
}
else
{
lean_object* x_170; 
x_170 = l_Lean_PersistentArray_get_x21___redArg(x_167, x_165, x_4);
x_74 = x_170;
goto block_164;
}
block_164:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_75 = l_Lean_Meta_Grind_Arith_split___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(x_2, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_st_ref_take(x_6, x_73);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 14);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_80, 3);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec_ref(x_78);
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 1);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_79, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 3);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_79, 4);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_79, 5);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_79, 6);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_79, 7);
lean_inc_ref(x_90);
x_91 = lean_ctor_get_uint8(x_79, sizeof(void*)*17);
x_92 = lean_ctor_get(x_79, 8);
lean_inc(x_92);
x_93 = lean_ctor_get(x_79, 9);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_79, 10);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_79, 11);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_79, 12);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_79, 13);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_79, 15);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_79, 16);
lean_inc_ref(x_99);
lean_dec(x_79);
x_100 = lean_ctor_get(x_80, 0);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_80, 1);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_80, 2);
lean_inc_ref(x_102);
lean_dec_ref(x_80);
x_103 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_81, 2);
lean_inc_ref(x_105);
lean_dec_ref(x_81);
x_106 = lean_array_get_size(x_103);
x_107 = lean_nat_dec_lt(x_5, x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_dec(x_76);
x_15 = x_90;
x_16 = x_89;
x_17 = x_88;
x_18 = x_104;
x_19 = x_105;
x_20 = x_96;
x_21 = x_93;
x_22 = x_87;
x_23 = x_98;
x_24 = x_77;
x_25 = x_95;
x_26 = x_85;
x_27 = x_97;
x_28 = x_83;
x_29 = x_94;
x_30 = x_86;
x_31 = x_82;
x_32 = x_92;
x_33 = x_101;
x_34 = x_100;
x_35 = x_102;
x_36 = x_99;
x_37 = x_84;
x_38 = x_91;
x_39 = x_103;
goto block_66;
}
else
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_array_fget(x_103, x_5);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_108, 35);
x_111 = lean_box(0);
x_112 = lean_array_fset(x_103, x_5, x_111);
x_113 = l_Lean_PersistentArray_set___redArg(x_110, x_4, x_76);
lean_ctor_set(x_108, 35, x_113);
x_114 = lean_array_fset(x_112, x_5, x_108);
x_15 = x_90;
x_16 = x_89;
x_17 = x_88;
x_18 = x_104;
x_19 = x_105;
x_20 = x_96;
x_21 = x_93;
x_22 = x_87;
x_23 = x_98;
x_24 = x_77;
x_25 = x_95;
x_26 = x_85;
x_27 = x_97;
x_28 = x_83;
x_29 = x_94;
x_30 = x_86;
x_31 = x_82;
x_32 = x_92;
x_33 = x_101;
x_34 = x_100;
x_35 = x_102;
x_36 = x_99;
x_37 = x_84;
x_38 = x_91;
x_39 = x_114;
goto block_66;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_115 = lean_ctor_get(x_108, 0);
x_116 = lean_ctor_get(x_108, 1);
x_117 = lean_ctor_get(x_108, 2);
x_118 = lean_ctor_get(x_108, 3);
x_119 = lean_ctor_get(x_108, 4);
x_120 = lean_ctor_get(x_108, 5);
x_121 = lean_ctor_get(x_108, 6);
x_122 = lean_ctor_get(x_108, 7);
x_123 = lean_ctor_get(x_108, 8);
x_124 = lean_ctor_get(x_108, 9);
x_125 = lean_ctor_get(x_108, 10);
x_126 = lean_ctor_get(x_108, 11);
x_127 = lean_ctor_get(x_108, 12);
x_128 = lean_ctor_get(x_108, 13);
x_129 = lean_ctor_get(x_108, 14);
x_130 = lean_ctor_get(x_108, 15);
x_131 = lean_ctor_get(x_108, 16);
x_132 = lean_ctor_get(x_108, 17);
x_133 = lean_ctor_get(x_108, 18);
x_134 = lean_ctor_get(x_108, 19);
x_135 = lean_ctor_get(x_108, 20);
x_136 = lean_ctor_get(x_108, 21);
x_137 = lean_ctor_get(x_108, 22);
x_138 = lean_ctor_get(x_108, 23);
x_139 = lean_ctor_get(x_108, 24);
x_140 = lean_ctor_get(x_108, 25);
x_141 = lean_ctor_get(x_108, 26);
x_142 = lean_ctor_get(x_108, 27);
x_143 = lean_ctor_get(x_108, 28);
x_144 = lean_ctor_get(x_108, 29);
x_145 = lean_ctor_get(x_108, 30);
x_146 = lean_ctor_get(x_108, 31);
x_147 = lean_ctor_get(x_108, 32);
x_148 = lean_ctor_get(x_108, 33);
x_149 = lean_ctor_get(x_108, 34);
x_150 = lean_ctor_get(x_108, 35);
x_151 = lean_ctor_get(x_108, 36);
x_152 = lean_ctor_get_uint8(x_108, sizeof(void*)*43);
x_153 = lean_ctor_get(x_108, 37);
x_154 = lean_ctor_get(x_108, 38);
x_155 = lean_ctor_get(x_108, 39);
x_156 = lean_ctor_get(x_108, 40);
x_157 = lean_ctor_get(x_108, 41);
x_158 = lean_ctor_get(x_108, 42);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
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
lean_dec(x_108);
x_159 = lean_box(0);
x_160 = lean_array_fset(x_103, x_5, x_159);
x_161 = l_Lean_PersistentArray_set___redArg(x_150, x_4, x_76);
x_162 = lean_alloc_ctor(0, 43, 1);
lean_ctor_set(x_162, 0, x_115);
lean_ctor_set(x_162, 1, x_116);
lean_ctor_set(x_162, 2, x_117);
lean_ctor_set(x_162, 3, x_118);
lean_ctor_set(x_162, 4, x_119);
lean_ctor_set(x_162, 5, x_120);
lean_ctor_set(x_162, 6, x_121);
lean_ctor_set(x_162, 7, x_122);
lean_ctor_set(x_162, 8, x_123);
lean_ctor_set(x_162, 9, x_124);
lean_ctor_set(x_162, 10, x_125);
lean_ctor_set(x_162, 11, x_126);
lean_ctor_set(x_162, 12, x_127);
lean_ctor_set(x_162, 13, x_128);
lean_ctor_set(x_162, 14, x_129);
lean_ctor_set(x_162, 15, x_130);
lean_ctor_set(x_162, 16, x_131);
lean_ctor_set(x_162, 17, x_132);
lean_ctor_set(x_162, 18, x_133);
lean_ctor_set(x_162, 19, x_134);
lean_ctor_set(x_162, 20, x_135);
lean_ctor_set(x_162, 21, x_136);
lean_ctor_set(x_162, 22, x_137);
lean_ctor_set(x_162, 23, x_138);
lean_ctor_set(x_162, 24, x_139);
lean_ctor_set(x_162, 25, x_140);
lean_ctor_set(x_162, 26, x_141);
lean_ctor_set(x_162, 27, x_142);
lean_ctor_set(x_162, 28, x_143);
lean_ctor_set(x_162, 29, x_144);
lean_ctor_set(x_162, 30, x_145);
lean_ctor_set(x_162, 31, x_146);
lean_ctor_set(x_162, 32, x_147);
lean_ctor_set(x_162, 33, x_148);
lean_ctor_set(x_162, 34, x_149);
lean_ctor_set(x_162, 35, x_161);
lean_ctor_set(x_162, 36, x_151);
lean_ctor_set(x_162, 37, x_153);
lean_ctor_set(x_162, 38, x_154);
lean_ctor_set(x_162, 39, x_155);
lean_ctor_set(x_162, 40, x_156);
lean_ctor_set(x_162, 41, x_157);
lean_ctor_set(x_162, 42, x_158);
lean_ctor_set_uint8(x_162, sizeof(void*)*43, x_152);
x_163 = lean_array_fset(x_160, x_5, x_162);
x_15 = x_90;
x_16 = x_89;
x_17 = x_88;
x_18 = x_104;
x_19 = x_105;
x_20 = x_96;
x_21 = x_93;
x_22 = x_87;
x_23 = x_98;
x_24 = x_77;
x_25 = x_95;
x_26 = x_85;
x_27 = x_97;
x_28 = x_83;
x_29 = x_94;
x_30 = x_86;
x_31 = x_82;
x_32 = x_92;
x_33 = x_101;
x_34 = x_100;
x_35 = x_102;
x_36 = x_99;
x_37 = x_84;
x_38 = x_91;
x_39 = x_163;
goto block_66;
}
}
}
}
else
{
uint8_t x_171; 
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
x_171 = !lean_is_exclusive(x_71);
if (x_171 == 0)
{
return x_71;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_71, 0);
x_173 = lean_ctor_get(x_71, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_71);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
uint8_t x_175; 
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
x_175 = !lean_is_exclusive(x_67);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_67, 0);
lean_dec(x_176);
x_177 = lean_box(0);
lean_ctor_set(x_67, 0, x_177);
return x_67;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_67, 1);
lean_inc(x_178);
lean_dec(x_67);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
else
{
uint8_t x_181; 
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
x_181 = !lean_is_exclusive(x_67);
if (x_181 == 0)
{
return x_67;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_67, 0);
x_183 = lean_ctor_get(x_67, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_67);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
block_66:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; 
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_18);
lean_ctor_set(x_40, 2, x_19);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 2, x_26);
lean_ctor_set(x_42, 3, x_30);
lean_ctor_set(x_42, 4, x_22);
lean_ctor_set(x_42, 5, x_17);
lean_ctor_set(x_42, 6, x_16);
lean_ctor_set(x_42, 7, x_15);
lean_ctor_set(x_42, 8, x_32);
lean_ctor_set(x_42, 9, x_21);
lean_ctor_set(x_42, 10, x_29);
lean_ctor_set(x_42, 11, x_25);
lean_ctor_set(x_42, 12, x_20);
lean_ctor_set(x_42, 13, x_27);
lean_ctor_set(x_42, 14, x_41);
lean_ctor_set(x_42, 15, x_23);
lean_ctor_set(x_42, 16, x_36);
lean_ctor_set_uint8(x_42, sizeof(void*)*17, x_38);
x_43 = lean_st_ref_set(x_6, x_42, x_31);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_box(0);
x_46 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0;
x_47 = lean_array_size(x_24);
x_48 = 0;
x_49 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(x_1, x_2, x_3, x_46, x_45, x_24, x_47, x_48, x_46, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_44);
lean_dec_ref(x_24);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_49, 0);
lean_dec(x_53);
lean_ctor_set(x_49, 0, x_45);
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_49, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
lean_dec_ref(x_51);
lean_ctor_set(x_49, 0, x_58);
return x_49;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_dec(x_49);
x_60 = lean_ctor_get(x_51, 0);
lean_inc(x_60);
lean_dec_ref(x_51);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_49);
if (x_62 == 0)
{
return x_49;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_49, 0);
x_64 = lean_ctor_get(x_49, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_49);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_57; 
x_57 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_150 = lean_ctor_get(x_58, 41);
lean_inc_ref(x_150);
lean_dec(x_58);
x_151 = lean_ctor_get(x_150, 2);
x_152 = lean_box(1);
x_153 = lean_nat_dec_lt(x_2, x_151);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec_ref(x_150);
x_154 = l_outOfBounds___redArg(x_152);
x_60 = x_154;
goto block_149;
}
else
{
lean_object* x_155; 
x_155 = l_Lean_PersistentArray_get_x21___redArg(x_152, x_150, x_2);
x_60 = x_155;
goto block_149;
}
block_149:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_61 = lean_st_ref_take(x_5, x_59);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 14);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_63, 3);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec_ref(x_61);
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_62, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 3);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_62, 4);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_62, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_62, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_62, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get_uint8(x_62, sizeof(void*)*17);
x_75 = lean_ctor_get(x_62, 8);
lean_inc(x_75);
x_76 = lean_ctor_get(x_62, 9);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_62, 10);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_62, 11);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_62, 12);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_62, 13);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_62, 15);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_62, 16);
lean_inc_ref(x_82);
lean_dec(x_62);
x_83 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_85);
lean_dec_ref(x_63);
x_86 = lean_ctor_get(x_64, 0);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_64, 2);
lean_inc_ref(x_88);
lean_dec_ref(x_64);
x_89 = lean_array_get_size(x_86);
x_90 = lean_nat_dec_lt(x_4, x_89);
lean_dec(x_89);
if (x_90 == 0)
{
x_14 = x_77;
x_15 = x_73;
x_16 = x_65;
x_17 = x_72;
x_18 = x_78;
x_19 = x_79;
x_20 = x_74;
x_21 = x_80;
x_22 = x_81;
x_23 = x_66;
x_24 = x_82;
x_25 = x_75;
x_26 = x_60;
x_27 = x_87;
x_28 = x_88;
x_29 = x_83;
x_30 = x_70;
x_31 = x_85;
x_32 = x_84;
x_33 = x_71;
x_34 = x_76;
x_35 = x_69;
x_36 = x_68;
x_37 = x_67;
x_38 = x_86;
goto block_56;
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_array_fget(x_86, x_4);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_91, 41);
x_94 = lean_box(0);
x_95 = lean_array_fset(x_86, x_4, x_94);
x_96 = lean_box(1);
x_97 = l_Lean_PersistentArray_set___redArg(x_93, x_2, x_96);
lean_ctor_set(x_91, 41, x_97);
x_98 = lean_array_fset(x_95, x_4, x_91);
x_14 = x_77;
x_15 = x_73;
x_16 = x_65;
x_17 = x_72;
x_18 = x_78;
x_19 = x_79;
x_20 = x_74;
x_21 = x_80;
x_22 = x_81;
x_23 = x_66;
x_24 = x_82;
x_25 = x_75;
x_26 = x_60;
x_27 = x_87;
x_28 = x_88;
x_29 = x_83;
x_30 = x_70;
x_31 = x_85;
x_32 = x_84;
x_33 = x_71;
x_34 = x_76;
x_35 = x_69;
x_36 = x_68;
x_37 = x_67;
x_38 = x_98;
goto block_56;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_99 = lean_ctor_get(x_91, 0);
x_100 = lean_ctor_get(x_91, 1);
x_101 = lean_ctor_get(x_91, 2);
x_102 = lean_ctor_get(x_91, 3);
x_103 = lean_ctor_get(x_91, 4);
x_104 = lean_ctor_get(x_91, 5);
x_105 = lean_ctor_get(x_91, 6);
x_106 = lean_ctor_get(x_91, 7);
x_107 = lean_ctor_get(x_91, 8);
x_108 = lean_ctor_get(x_91, 9);
x_109 = lean_ctor_get(x_91, 10);
x_110 = lean_ctor_get(x_91, 11);
x_111 = lean_ctor_get(x_91, 12);
x_112 = lean_ctor_get(x_91, 13);
x_113 = lean_ctor_get(x_91, 14);
x_114 = lean_ctor_get(x_91, 15);
x_115 = lean_ctor_get(x_91, 16);
x_116 = lean_ctor_get(x_91, 17);
x_117 = lean_ctor_get(x_91, 18);
x_118 = lean_ctor_get(x_91, 19);
x_119 = lean_ctor_get(x_91, 20);
x_120 = lean_ctor_get(x_91, 21);
x_121 = lean_ctor_get(x_91, 22);
x_122 = lean_ctor_get(x_91, 23);
x_123 = lean_ctor_get(x_91, 24);
x_124 = lean_ctor_get(x_91, 25);
x_125 = lean_ctor_get(x_91, 26);
x_126 = lean_ctor_get(x_91, 27);
x_127 = lean_ctor_get(x_91, 28);
x_128 = lean_ctor_get(x_91, 29);
x_129 = lean_ctor_get(x_91, 30);
x_130 = lean_ctor_get(x_91, 31);
x_131 = lean_ctor_get(x_91, 32);
x_132 = lean_ctor_get(x_91, 33);
x_133 = lean_ctor_get(x_91, 34);
x_134 = lean_ctor_get(x_91, 35);
x_135 = lean_ctor_get(x_91, 36);
x_136 = lean_ctor_get_uint8(x_91, sizeof(void*)*43);
x_137 = lean_ctor_get(x_91, 37);
x_138 = lean_ctor_get(x_91, 38);
x_139 = lean_ctor_get(x_91, 39);
x_140 = lean_ctor_get(x_91, 40);
x_141 = lean_ctor_get(x_91, 41);
x_142 = lean_ctor_get(x_91, 42);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
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
lean_dec(x_91);
x_143 = lean_box(0);
x_144 = lean_array_fset(x_86, x_4, x_143);
x_145 = lean_box(1);
x_146 = l_Lean_PersistentArray_set___redArg(x_141, x_2, x_145);
x_147 = lean_alloc_ctor(0, 43, 1);
lean_ctor_set(x_147, 0, x_99);
lean_ctor_set(x_147, 1, x_100);
lean_ctor_set(x_147, 2, x_101);
lean_ctor_set(x_147, 3, x_102);
lean_ctor_set(x_147, 4, x_103);
lean_ctor_set(x_147, 5, x_104);
lean_ctor_set(x_147, 6, x_105);
lean_ctor_set(x_147, 7, x_106);
lean_ctor_set(x_147, 8, x_107);
lean_ctor_set(x_147, 9, x_108);
lean_ctor_set(x_147, 10, x_109);
lean_ctor_set(x_147, 11, x_110);
lean_ctor_set(x_147, 12, x_111);
lean_ctor_set(x_147, 13, x_112);
lean_ctor_set(x_147, 14, x_113);
lean_ctor_set(x_147, 15, x_114);
lean_ctor_set(x_147, 16, x_115);
lean_ctor_set(x_147, 17, x_116);
lean_ctor_set(x_147, 18, x_117);
lean_ctor_set(x_147, 19, x_118);
lean_ctor_set(x_147, 20, x_119);
lean_ctor_set(x_147, 21, x_120);
lean_ctor_set(x_147, 22, x_121);
lean_ctor_set(x_147, 23, x_122);
lean_ctor_set(x_147, 24, x_123);
lean_ctor_set(x_147, 25, x_124);
lean_ctor_set(x_147, 26, x_125);
lean_ctor_set(x_147, 27, x_126);
lean_ctor_set(x_147, 28, x_127);
lean_ctor_set(x_147, 29, x_128);
lean_ctor_set(x_147, 30, x_129);
lean_ctor_set(x_147, 31, x_130);
lean_ctor_set(x_147, 32, x_131);
lean_ctor_set(x_147, 33, x_132);
lean_ctor_set(x_147, 34, x_133);
lean_ctor_set(x_147, 35, x_134);
lean_ctor_set(x_147, 36, x_135);
lean_ctor_set(x_147, 37, x_137);
lean_ctor_set(x_147, 38, x_138);
lean_ctor_set(x_147, 39, x_139);
lean_ctor_set(x_147, 40, x_140);
lean_ctor_set(x_147, 41, x_146);
lean_ctor_set(x_147, 42, x_142);
lean_ctor_set_uint8(x_147, sizeof(void*)*43, x_136);
x_148 = lean_array_fset(x_144, x_4, x_147);
x_14 = x_77;
x_15 = x_73;
x_16 = x_65;
x_17 = x_72;
x_18 = x_78;
x_19 = x_79;
x_20 = x_74;
x_21 = x_80;
x_22 = x_81;
x_23 = x_66;
x_24 = x_82;
x_25 = x_75;
x_26 = x_60;
x_27 = x_87;
x_28 = x_88;
x_29 = x_83;
x_30 = x_70;
x_31 = x_85;
x_32 = x_84;
x_33 = x_71;
x_34 = x_76;
x_35 = x_69;
x_36 = x_68;
x_37 = x_67;
x_38 = x_148;
goto block_56;
}
}
}
}
else
{
uint8_t x_156; 
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
x_156 = !lean_is_exclusive(x_57);
if (x_156 == 0)
{
return x_57;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_57, 0);
x_158 = lean_ctor_get(x_57, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_57);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
block_56:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_39, 2, x_28);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_31);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_35);
lean_ctor_set(x_41, 4, x_30);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_41, 6, x_17);
lean_ctor_set(x_41, 7, x_15);
lean_ctor_set(x_41, 8, x_25);
lean_ctor_set(x_41, 9, x_34);
lean_ctor_set(x_41, 10, x_14);
lean_ctor_set(x_41, 11, x_18);
lean_ctor_set(x_41, 12, x_19);
lean_ctor_set(x_41, 13, x_21);
lean_ctor_set(x_41, 14, x_40);
lean_ctor_set(x_41, 15, x_22);
lean_ctor_set(x_41, 16, x_24);
lean_ctor_set_uint8(x_41, sizeof(void*)*17, x_20);
x_42 = lean_st_ref_set(x_5, x_41, x_16);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
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
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(x_1, x_2, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_box(0);
x_47 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(x_1, x_2, x_3, x_46, x_46, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_45);
lean_dec(x_26);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_47);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_dec(x_26);
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
return x_44;
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
lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; 
x_497 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0;
x_498 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_497, x_9, x_11);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_unbox(x_499);
lean_dec(x_499);
if (x_500 == 0)
{
lean_object* x_501; 
x_501 = lean_ctor_get(x_498, 1);
lean_inc(x_501);
lean_dec_ref(x_498);
x_291 = x_2;
x_292 = x_3;
x_293 = x_4;
x_294 = x_5;
x_295 = x_6;
x_296 = x_7;
x_297 = x_8;
x_298 = x_9;
x_299 = x_10;
x_300 = x_501;
goto block_496;
}
else
{
uint8_t x_502; 
x_502 = !lean_is_exclusive(x_498);
if (x_502 == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_498, 1);
x_504 = lean_ctor_get(x_498, 0);
lean_dec(x_504);
x_505 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_503);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec_ref(x_505);
x_508 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_509 = l_Lean_MessageData_ofExpr(x_506);
lean_ctor_set_tag(x_498, 7);
lean_ctor_set(x_498, 1, x_509);
lean_ctor_set(x_498, 0, x_508);
x_510 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_510, 0, x_498);
lean_ctor_set(x_510, 1, x_508);
x_511 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_497, x_510, x_7, x_8, x_9, x_10, x_507);
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
lean_dec_ref(x_511);
x_291 = x_2;
x_292 = x_3;
x_293 = x_4;
x_294 = x_5;
x_295 = x_6;
x_296 = x_7;
x_297 = x_8;
x_298 = x_9;
x_299 = x_10;
x_300 = x_512;
goto block_496;
}
else
{
uint8_t x_513; 
lean_free_object(x_498);
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
x_513 = !lean_is_exclusive(x_505);
if (x_513 == 0)
{
return x_505;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_505, 0);
x_515 = lean_ctor_get(x_505, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_505);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
return x_516;
}
}
}
else
{
lean_object* x_517; lean_object* x_518; 
x_517 = lean_ctor_get(x_498, 1);
lean_inc(x_517);
lean_dec(x_498);
x_518 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_517);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec_ref(x_518);
x_521 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_522 = l_Lean_MessageData_ofExpr(x_519);
x_523 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set(x_523, 1, x_522);
x_524 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_521);
x_525 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_497, x_524, x_7, x_8, x_9, x_10, x_520);
x_526 = lean_ctor_get(x_525, 1);
lean_inc(x_526);
lean_dec_ref(x_525);
x_291 = x_2;
x_292 = x_3;
x_293 = x_4;
x_294 = x_5;
x_295 = x_6;
x_296 = x_7;
x_297 = x_8;
x_298 = x_9;
x_299 = x_10;
x_300 = x_526;
goto block_496;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
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
x_527 = lean_ctor_get(x_518, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_518, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 x_529 = x_518;
} else {
 lean_dec_ref(x_518);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 2, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_527);
lean_ctor_set(x_530, 1, x_528);
return x_530;
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
block_58:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_38);
lean_ctor_set(x_52, 2, x_39);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_28);
lean_ctor_set(x_53, 1, x_33);
lean_ctor_set(x_53, 2, x_44);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_27);
lean_ctor_set(x_54, 2, x_31);
lean_ctor_set(x_54, 3, x_50);
lean_ctor_set(x_54, 4, x_37);
lean_ctor_set(x_54, 5, x_22);
lean_ctor_set(x_54, 6, x_19);
lean_ctor_set(x_54, 7, x_23);
lean_ctor_set(x_54, 8, x_40);
lean_ctor_set(x_54, 9, x_35);
lean_ctor_set(x_54, 10, x_24);
lean_ctor_set(x_54, 11, x_32);
lean_ctor_set(x_54, 12, x_41);
lean_ctor_set(x_54, 13, x_34);
lean_ctor_set(x_54, 14, x_53);
lean_ctor_set(x_54, 15, x_29);
lean_ctor_set(x_54, 16, x_47);
lean_ctor_set_uint8(x_54, sizeof(void*)*17, x_49);
x_55 = lean_st_ref_set(x_30, x_54, x_25);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_17, x_45, x_48, x_46, x_30, x_36, x_26, x_21, x_42, x_18, x_20, x_16, x_56);
return x_57;
}
block_242:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_st_ref_take(x_63, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 14);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_74, 3);
lean_inc_ref(x_75);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_77 = lean_ctor_get(x_72, 1);
x_78 = lean_ctor_get(x_72, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 1);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_73, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_73, 3);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_73, 4);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_73, 5);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_73, 6);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_73, 7);
lean_inc_ref(x_86);
x_87 = lean_ctor_get_uint8(x_73, sizeof(void*)*17);
x_88 = lean_ctor_get(x_73, 8);
lean_inc(x_88);
x_89 = lean_ctor_get(x_73, 9);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_73, 10);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_73, 11);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_73, 12);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_73, 13);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_73, 15);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_73, 16);
lean_inc_ref(x_95);
lean_dec(x_73);
x_96 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_74, 1);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_74, 2);
lean_inc_ref(x_98);
lean_dec_ref(x_74);
x_99 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_75, 2);
lean_inc_ref(x_101);
lean_dec_ref(x_75);
x_102 = lean_array_get_size(x_99);
x_103 = lean_nat_dec_lt(x_62, x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_free_object(x_72);
x_16 = x_70;
x_17 = x_60;
x_18 = x_68;
x_19 = x_85;
x_20 = x_69;
x_21 = x_66;
x_22 = x_84;
x_23 = x_86;
x_24 = x_90;
x_25 = x_77;
x_26 = x_65;
x_27 = x_80;
x_28 = x_96;
x_29 = x_94;
x_30 = x_63;
x_31 = x_81;
x_32 = x_91;
x_33 = x_97;
x_34 = x_93;
x_35 = x_89;
x_36 = x_64;
x_37 = x_83;
x_38 = x_100;
x_39 = x_101;
x_40 = x_88;
x_41 = x_92;
x_42 = x_67;
x_43 = x_79;
x_44 = x_98;
x_45 = x_61;
x_46 = x_62;
x_47 = x_95;
x_48 = x_59;
x_49 = x_87;
x_50 = x_82;
x_51 = x_99;
goto block_58;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_array_fget(x_99, x_62);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_104, 39);
x_107 = lean_ctor_get(x_104, 40);
x_108 = lean_box(0);
x_109 = lean_array_fset(x_99, x_62, x_108);
lean_inc_ref(x_59);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_59);
x_111 = l_Lean_PersistentArray_set___redArg(x_106, x_61, x_110);
lean_inc(x_61);
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 1, x_107);
lean_ctor_set(x_72, 0, x_61);
lean_ctor_set(x_104, 40, x_72);
lean_ctor_set(x_104, 39, x_111);
x_112 = lean_array_fset(x_109, x_62, x_104);
x_16 = x_70;
x_17 = x_60;
x_18 = x_68;
x_19 = x_85;
x_20 = x_69;
x_21 = x_66;
x_22 = x_84;
x_23 = x_86;
x_24 = x_90;
x_25 = x_77;
x_26 = x_65;
x_27 = x_80;
x_28 = x_96;
x_29 = x_94;
x_30 = x_63;
x_31 = x_81;
x_32 = x_91;
x_33 = x_97;
x_34 = x_93;
x_35 = x_89;
x_36 = x_64;
x_37 = x_83;
x_38 = x_100;
x_39 = x_101;
x_40 = x_88;
x_41 = x_92;
x_42 = x_67;
x_43 = x_79;
x_44 = x_98;
x_45 = x_61;
x_46 = x_62;
x_47 = x_95;
x_48 = x_59;
x_49 = x_87;
x_50 = x_82;
x_51 = x_112;
goto block_58;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_113 = lean_ctor_get(x_104, 0);
x_114 = lean_ctor_get(x_104, 1);
x_115 = lean_ctor_get(x_104, 2);
x_116 = lean_ctor_get(x_104, 3);
x_117 = lean_ctor_get(x_104, 4);
x_118 = lean_ctor_get(x_104, 5);
x_119 = lean_ctor_get(x_104, 6);
x_120 = lean_ctor_get(x_104, 7);
x_121 = lean_ctor_get(x_104, 8);
x_122 = lean_ctor_get(x_104, 9);
x_123 = lean_ctor_get(x_104, 10);
x_124 = lean_ctor_get(x_104, 11);
x_125 = lean_ctor_get(x_104, 12);
x_126 = lean_ctor_get(x_104, 13);
x_127 = lean_ctor_get(x_104, 14);
x_128 = lean_ctor_get(x_104, 15);
x_129 = lean_ctor_get(x_104, 16);
x_130 = lean_ctor_get(x_104, 17);
x_131 = lean_ctor_get(x_104, 18);
x_132 = lean_ctor_get(x_104, 19);
x_133 = lean_ctor_get(x_104, 20);
x_134 = lean_ctor_get(x_104, 21);
x_135 = lean_ctor_get(x_104, 22);
x_136 = lean_ctor_get(x_104, 23);
x_137 = lean_ctor_get(x_104, 24);
x_138 = lean_ctor_get(x_104, 25);
x_139 = lean_ctor_get(x_104, 26);
x_140 = lean_ctor_get(x_104, 27);
x_141 = lean_ctor_get(x_104, 28);
x_142 = lean_ctor_get(x_104, 29);
x_143 = lean_ctor_get(x_104, 30);
x_144 = lean_ctor_get(x_104, 31);
x_145 = lean_ctor_get(x_104, 32);
x_146 = lean_ctor_get(x_104, 33);
x_147 = lean_ctor_get(x_104, 34);
x_148 = lean_ctor_get(x_104, 35);
x_149 = lean_ctor_get(x_104, 36);
x_150 = lean_ctor_get_uint8(x_104, sizeof(void*)*43);
x_151 = lean_ctor_get(x_104, 37);
x_152 = lean_ctor_get(x_104, 38);
x_153 = lean_ctor_get(x_104, 39);
x_154 = lean_ctor_get(x_104, 40);
x_155 = lean_ctor_get(x_104, 41);
x_156 = lean_ctor_get(x_104, 42);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_149);
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
lean_dec(x_104);
x_157 = lean_box(0);
x_158 = lean_array_fset(x_99, x_62, x_157);
lean_inc_ref(x_59);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_59);
x_160 = l_Lean_PersistentArray_set___redArg(x_153, x_61, x_159);
lean_inc(x_61);
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 1, x_154);
lean_ctor_set(x_72, 0, x_61);
x_161 = lean_alloc_ctor(0, 43, 1);
lean_ctor_set(x_161, 0, x_113);
lean_ctor_set(x_161, 1, x_114);
lean_ctor_set(x_161, 2, x_115);
lean_ctor_set(x_161, 3, x_116);
lean_ctor_set(x_161, 4, x_117);
lean_ctor_set(x_161, 5, x_118);
lean_ctor_set(x_161, 6, x_119);
lean_ctor_set(x_161, 7, x_120);
lean_ctor_set(x_161, 8, x_121);
lean_ctor_set(x_161, 9, x_122);
lean_ctor_set(x_161, 10, x_123);
lean_ctor_set(x_161, 11, x_124);
lean_ctor_set(x_161, 12, x_125);
lean_ctor_set(x_161, 13, x_126);
lean_ctor_set(x_161, 14, x_127);
lean_ctor_set(x_161, 15, x_128);
lean_ctor_set(x_161, 16, x_129);
lean_ctor_set(x_161, 17, x_130);
lean_ctor_set(x_161, 18, x_131);
lean_ctor_set(x_161, 19, x_132);
lean_ctor_set(x_161, 20, x_133);
lean_ctor_set(x_161, 21, x_134);
lean_ctor_set(x_161, 22, x_135);
lean_ctor_set(x_161, 23, x_136);
lean_ctor_set(x_161, 24, x_137);
lean_ctor_set(x_161, 25, x_138);
lean_ctor_set(x_161, 26, x_139);
lean_ctor_set(x_161, 27, x_140);
lean_ctor_set(x_161, 28, x_141);
lean_ctor_set(x_161, 29, x_142);
lean_ctor_set(x_161, 30, x_143);
lean_ctor_set(x_161, 31, x_144);
lean_ctor_set(x_161, 32, x_145);
lean_ctor_set(x_161, 33, x_146);
lean_ctor_set(x_161, 34, x_147);
lean_ctor_set(x_161, 35, x_148);
lean_ctor_set(x_161, 36, x_149);
lean_ctor_set(x_161, 37, x_151);
lean_ctor_set(x_161, 38, x_152);
lean_ctor_set(x_161, 39, x_160);
lean_ctor_set(x_161, 40, x_72);
lean_ctor_set(x_161, 41, x_155);
lean_ctor_set(x_161, 42, x_156);
lean_ctor_set_uint8(x_161, sizeof(void*)*43, x_150);
x_162 = lean_array_fset(x_158, x_62, x_161);
x_16 = x_70;
x_17 = x_60;
x_18 = x_68;
x_19 = x_85;
x_20 = x_69;
x_21 = x_66;
x_22 = x_84;
x_23 = x_86;
x_24 = x_90;
x_25 = x_77;
x_26 = x_65;
x_27 = x_80;
x_28 = x_96;
x_29 = x_94;
x_30 = x_63;
x_31 = x_81;
x_32 = x_91;
x_33 = x_97;
x_34 = x_93;
x_35 = x_89;
x_36 = x_64;
x_37 = x_83;
x_38 = x_100;
x_39 = x_101;
x_40 = x_88;
x_41 = x_92;
x_42 = x_67;
x_43 = x_79;
x_44 = x_98;
x_45 = x_61;
x_46 = x_62;
x_47 = x_95;
x_48 = x_59;
x_49 = x_87;
x_50 = x_82;
x_51 = x_162;
goto block_58;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_163 = lean_ctor_get(x_72, 1);
lean_inc(x_163);
lean_dec(x_72);
x_164 = lean_ctor_get(x_73, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_73, 1);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_73, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_73, 3);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_73, 4);
lean_inc_ref(x_168);
x_169 = lean_ctor_get(x_73, 5);
lean_inc_ref(x_169);
x_170 = lean_ctor_get(x_73, 6);
lean_inc_ref(x_170);
x_171 = lean_ctor_get(x_73, 7);
lean_inc_ref(x_171);
x_172 = lean_ctor_get_uint8(x_73, sizeof(void*)*17);
x_173 = lean_ctor_get(x_73, 8);
lean_inc(x_173);
x_174 = lean_ctor_get(x_73, 9);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_73, 10);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_73, 11);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_73, 12);
lean_inc_ref(x_177);
x_178 = lean_ctor_get(x_73, 13);
lean_inc_ref(x_178);
x_179 = lean_ctor_get(x_73, 15);
lean_inc_ref(x_179);
x_180 = lean_ctor_get(x_73, 16);
lean_inc_ref(x_180);
lean_dec(x_73);
x_181 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_181);
x_182 = lean_ctor_get(x_74, 1);
lean_inc_ref(x_182);
x_183 = lean_ctor_get(x_74, 2);
lean_inc_ref(x_183);
lean_dec_ref(x_74);
x_184 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_184);
x_185 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_185);
x_186 = lean_ctor_get(x_75, 2);
lean_inc_ref(x_186);
lean_dec_ref(x_75);
x_187 = lean_array_get_size(x_184);
x_188 = lean_nat_dec_lt(x_62, x_187);
lean_dec(x_187);
if (x_188 == 0)
{
x_16 = x_70;
x_17 = x_60;
x_18 = x_68;
x_19 = x_170;
x_20 = x_69;
x_21 = x_66;
x_22 = x_169;
x_23 = x_171;
x_24 = x_175;
x_25 = x_163;
x_26 = x_65;
x_27 = x_165;
x_28 = x_181;
x_29 = x_179;
x_30 = x_63;
x_31 = x_166;
x_32 = x_176;
x_33 = x_182;
x_34 = x_178;
x_35 = x_174;
x_36 = x_64;
x_37 = x_168;
x_38 = x_185;
x_39 = x_186;
x_40 = x_173;
x_41 = x_177;
x_42 = x_67;
x_43 = x_164;
x_44 = x_183;
x_45 = x_61;
x_46 = x_62;
x_47 = x_180;
x_48 = x_59;
x_49 = x_172;
x_50 = x_167;
x_51 = x_184;
goto block_58;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_189 = lean_array_fget(x_184, x_62);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 2);
lean_inc_ref(x_192);
x_193 = lean_ctor_get(x_189, 3);
lean_inc(x_193);
x_194 = lean_ctor_get(x_189, 4);
lean_inc_ref(x_194);
x_195 = lean_ctor_get(x_189, 5);
lean_inc(x_195);
x_196 = lean_ctor_get(x_189, 6);
lean_inc(x_196);
x_197 = lean_ctor_get(x_189, 7);
lean_inc(x_197);
x_198 = lean_ctor_get(x_189, 8);
lean_inc(x_198);
x_199 = lean_ctor_get(x_189, 9);
lean_inc(x_199);
x_200 = lean_ctor_get(x_189, 10);
lean_inc(x_200);
x_201 = lean_ctor_get(x_189, 11);
lean_inc(x_201);
x_202 = lean_ctor_get(x_189, 12);
lean_inc(x_202);
x_203 = lean_ctor_get(x_189, 13);
lean_inc(x_203);
x_204 = lean_ctor_get(x_189, 14);
lean_inc(x_204);
x_205 = lean_ctor_get(x_189, 15);
lean_inc(x_205);
x_206 = lean_ctor_get(x_189, 16);
lean_inc(x_206);
x_207 = lean_ctor_get(x_189, 17);
lean_inc(x_207);
x_208 = lean_ctor_get(x_189, 18);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_189, 19);
lean_inc_ref(x_209);
x_210 = lean_ctor_get(x_189, 20);
lean_inc(x_210);
x_211 = lean_ctor_get(x_189, 21);
lean_inc(x_211);
x_212 = lean_ctor_get(x_189, 22);
lean_inc(x_212);
x_213 = lean_ctor_get(x_189, 23);
lean_inc_ref(x_213);
x_214 = lean_ctor_get(x_189, 24);
lean_inc_ref(x_214);
x_215 = lean_ctor_get(x_189, 25);
lean_inc_ref(x_215);
x_216 = lean_ctor_get(x_189, 26);
lean_inc(x_216);
x_217 = lean_ctor_get(x_189, 27);
lean_inc(x_217);
x_218 = lean_ctor_get(x_189, 28);
lean_inc(x_218);
x_219 = lean_ctor_get(x_189, 29);
lean_inc_ref(x_219);
x_220 = lean_ctor_get(x_189, 30);
lean_inc_ref(x_220);
x_221 = lean_ctor_get(x_189, 31);
lean_inc_ref(x_221);
x_222 = lean_ctor_get(x_189, 32);
lean_inc_ref(x_222);
x_223 = lean_ctor_get(x_189, 33);
lean_inc_ref(x_223);
x_224 = lean_ctor_get(x_189, 34);
lean_inc_ref(x_224);
x_225 = lean_ctor_get(x_189, 35);
lean_inc_ref(x_225);
x_226 = lean_ctor_get(x_189, 36);
lean_inc_ref(x_226);
x_227 = lean_ctor_get_uint8(x_189, sizeof(void*)*43);
x_228 = lean_ctor_get(x_189, 37);
lean_inc(x_228);
x_229 = lean_ctor_get(x_189, 38);
lean_inc_ref(x_229);
x_230 = lean_ctor_get(x_189, 39);
lean_inc_ref(x_230);
x_231 = lean_ctor_get(x_189, 40);
lean_inc(x_231);
x_232 = lean_ctor_get(x_189, 41);
lean_inc_ref(x_232);
x_233 = lean_ctor_get(x_189, 42);
lean_inc_ref(x_233);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 lean_ctor_release(x_189, 5);
 lean_ctor_release(x_189, 6);
 lean_ctor_release(x_189, 7);
 lean_ctor_release(x_189, 8);
 lean_ctor_release(x_189, 9);
 lean_ctor_release(x_189, 10);
 lean_ctor_release(x_189, 11);
 lean_ctor_release(x_189, 12);
 lean_ctor_release(x_189, 13);
 lean_ctor_release(x_189, 14);
 lean_ctor_release(x_189, 15);
 lean_ctor_release(x_189, 16);
 lean_ctor_release(x_189, 17);
 lean_ctor_release(x_189, 18);
 lean_ctor_release(x_189, 19);
 lean_ctor_release(x_189, 20);
 lean_ctor_release(x_189, 21);
 lean_ctor_release(x_189, 22);
 lean_ctor_release(x_189, 23);
 lean_ctor_release(x_189, 24);
 lean_ctor_release(x_189, 25);
 lean_ctor_release(x_189, 26);
 lean_ctor_release(x_189, 27);
 lean_ctor_release(x_189, 28);
 lean_ctor_release(x_189, 29);
 lean_ctor_release(x_189, 30);
 lean_ctor_release(x_189, 31);
 lean_ctor_release(x_189, 32);
 lean_ctor_release(x_189, 33);
 lean_ctor_release(x_189, 34);
 lean_ctor_release(x_189, 35);
 lean_ctor_release(x_189, 36);
 lean_ctor_release(x_189, 37);
 lean_ctor_release(x_189, 38);
 lean_ctor_release(x_189, 39);
 lean_ctor_release(x_189, 40);
 lean_ctor_release(x_189, 41);
 lean_ctor_release(x_189, 42);
 x_234 = x_189;
} else {
 lean_dec_ref(x_189);
 x_234 = lean_box(0);
}
x_235 = lean_box(0);
x_236 = lean_array_fset(x_184, x_62, x_235);
lean_inc_ref(x_59);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_59);
x_238 = l_Lean_PersistentArray_set___redArg(x_230, x_61, x_237);
lean_inc(x_61);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_61);
lean_ctor_set(x_239, 1, x_231);
if (lean_is_scalar(x_234)) {
 x_240 = lean_alloc_ctor(0, 43, 1);
} else {
 x_240 = x_234;
}
lean_ctor_set(x_240, 0, x_190);
lean_ctor_set(x_240, 1, x_191);
lean_ctor_set(x_240, 2, x_192);
lean_ctor_set(x_240, 3, x_193);
lean_ctor_set(x_240, 4, x_194);
lean_ctor_set(x_240, 5, x_195);
lean_ctor_set(x_240, 6, x_196);
lean_ctor_set(x_240, 7, x_197);
lean_ctor_set(x_240, 8, x_198);
lean_ctor_set(x_240, 9, x_199);
lean_ctor_set(x_240, 10, x_200);
lean_ctor_set(x_240, 11, x_201);
lean_ctor_set(x_240, 12, x_202);
lean_ctor_set(x_240, 13, x_203);
lean_ctor_set(x_240, 14, x_204);
lean_ctor_set(x_240, 15, x_205);
lean_ctor_set(x_240, 16, x_206);
lean_ctor_set(x_240, 17, x_207);
lean_ctor_set(x_240, 18, x_208);
lean_ctor_set(x_240, 19, x_209);
lean_ctor_set(x_240, 20, x_210);
lean_ctor_set(x_240, 21, x_211);
lean_ctor_set(x_240, 22, x_212);
lean_ctor_set(x_240, 23, x_213);
lean_ctor_set(x_240, 24, x_214);
lean_ctor_set(x_240, 25, x_215);
lean_ctor_set(x_240, 26, x_216);
lean_ctor_set(x_240, 27, x_217);
lean_ctor_set(x_240, 28, x_218);
lean_ctor_set(x_240, 29, x_219);
lean_ctor_set(x_240, 30, x_220);
lean_ctor_set(x_240, 31, x_221);
lean_ctor_set(x_240, 32, x_222);
lean_ctor_set(x_240, 33, x_223);
lean_ctor_set(x_240, 34, x_224);
lean_ctor_set(x_240, 35, x_225);
lean_ctor_set(x_240, 36, x_226);
lean_ctor_set(x_240, 37, x_228);
lean_ctor_set(x_240, 38, x_229);
lean_ctor_set(x_240, 39, x_238);
lean_ctor_set(x_240, 40, x_239);
lean_ctor_set(x_240, 41, x_232);
lean_ctor_set(x_240, 42, x_233);
lean_ctor_set_uint8(x_240, sizeof(void*)*43, x_227);
x_241 = lean_array_fset(x_236, x_62, x_240);
x_16 = x_70;
x_17 = x_60;
x_18 = x_68;
x_19 = x_170;
x_20 = x_69;
x_21 = x_66;
x_22 = x_169;
x_23 = x_171;
x_24 = x_175;
x_25 = x_163;
x_26 = x_65;
x_27 = x_165;
x_28 = x_181;
x_29 = x_179;
x_30 = x_63;
x_31 = x_166;
x_32 = x_176;
x_33 = x_182;
x_34 = x_178;
x_35 = x_174;
x_36 = x_64;
x_37 = x_168;
x_38 = x_185;
x_39 = x_186;
x_40 = x_173;
x_41 = x_177;
x_42 = x_67;
x_43 = x_164;
x_44 = x_183;
x_45 = x_61;
x_46 = x_62;
x_47 = x_180;
x_48 = x_59;
x_49 = x_172;
x_50 = x_167;
x_51 = x_241;
goto block_58;
}
}
}
block_290:
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_256 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5;
x_257 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_256, x_253, x_255);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_unbox(x_258);
lean_dec(x_258);
if (x_259 == 0)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_257, 1);
lean_inc(x_260);
lean_dec_ref(x_257);
x_59 = x_243;
x_60 = x_244;
x_61 = x_245;
x_62 = x_246;
x_63 = x_247;
x_64 = x_248;
x_65 = x_249;
x_66 = x_250;
x_67 = x_251;
x_68 = x_252;
x_69 = x_253;
x_70 = x_254;
x_71 = x_260;
goto block_242;
}
else
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_257);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_257, 1);
x_263 = lean_ctor_get(x_257, 0);
lean_dec(x_263);
x_264 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_243, x_246, x_247, x_248, x_249, x_250, x_251, x_252, x_253, x_254, x_262);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec_ref(x_264);
x_267 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_268 = l_Lean_MessageData_ofExpr(x_265);
lean_ctor_set_tag(x_257, 7);
lean_ctor_set(x_257, 1, x_268);
lean_ctor_set(x_257, 0, x_267);
x_269 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_269, 0, x_257);
lean_ctor_set(x_269, 1, x_267);
x_270 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_256, x_269, x_251, x_252, x_253, x_254, x_266);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec_ref(x_270);
x_59 = x_243;
x_60 = x_244;
x_61 = x_245;
x_62 = x_246;
x_63 = x_247;
x_64 = x_248;
x_65 = x_249;
x_66 = x_250;
x_67 = x_251;
x_68 = x_252;
x_69 = x_253;
x_70 = x_254;
x_71 = x_271;
goto block_242;
}
else
{
uint8_t x_272; 
lean_free_object(x_257);
lean_dec(x_254);
lean_dec_ref(x_253);
lean_dec(x_252);
lean_dec_ref(x_251);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
x_272 = !lean_is_exclusive(x_264);
if (x_272 == 0)
{
return x_264;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_264, 0);
x_274 = lean_ctor_get(x_264, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_264);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
else
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_257, 1);
lean_inc(x_276);
lean_dec(x_257);
x_277 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_243, x_246, x_247, x_248, x_249, x_250, x_251, x_252, x_253, x_254, x_276);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec_ref(x_277);
x_280 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_281 = l_Lean_MessageData_ofExpr(x_278);
x_282 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_280);
x_284 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_256, x_283, x_251, x_252, x_253, x_254, x_279);
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
lean_dec_ref(x_284);
x_59 = x_243;
x_60 = x_244;
x_61 = x_245;
x_62 = x_246;
x_63 = x_247;
x_64 = x_248;
x_65 = x_249;
x_66 = x_250;
x_67 = x_251;
x_68 = x_252;
x_69 = x_253;
x_70 = x_254;
x_71 = x_285;
goto block_242;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_254);
lean_dec_ref(x_253);
lean_dec(x_252);
lean_dec_ref(x_251);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
x_286 = lean_ctor_get(x_277, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_277, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_288 = x_277;
} else {
 lean_dec_ref(x_277);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
}
}
block_496:
{
lean_object* x_301; 
lean_inc_ref(x_298);
x_301 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(x_1, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_300);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec_ref(x_301);
x_304 = lean_ctor_get(x_302, 0);
x_305 = lean_box(0);
x_306 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith_2431311409____hygCtx___hyg_34_(x_304, x_305);
if (x_306 == 0)
{
lean_object* x_307; 
lean_inc(x_299);
lean_inc_ref(x_298);
lean_inc(x_297);
lean_inc_ref(x_296);
lean_inc(x_295);
lean_inc_ref(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
x_307 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(x_302, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_303);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
x_310 = lean_ctor_get(x_307, 1);
lean_inc(x_310);
lean_dec_ref(x_307);
x_311 = !lean_is_exclusive(x_308);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_312 = lean_ctor_get(x_308, 0);
x_313 = lean_ctor_get(x_308, 1);
lean_dec(x_313);
x_314 = !lean_is_exclusive(x_309);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_315 = lean_ctor_get(x_309, 0);
x_316 = lean_ctor_get(x_309, 1);
x_317 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_318 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_317, x_298, x_310);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_unbox(x_319);
lean_dec(x_319);
if (x_320 == 0)
{
lean_object* x_321; 
lean_free_object(x_309);
lean_free_object(x_308);
x_321 = lean_ctor_get(x_318, 1);
lean_inc(x_321);
lean_dec_ref(x_318);
x_243 = x_316;
x_244 = x_312;
x_245 = x_315;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_295;
x_251 = x_296;
x_252 = x_297;
x_253 = x_298;
x_254 = x_299;
x_255 = x_321;
goto block_290;
}
else
{
uint8_t x_322; 
x_322 = !lean_is_exclusive(x_318);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_318, 1);
x_324 = lean_ctor_get(x_318, 0);
lean_dec(x_324);
x_325 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_315, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_323);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec_ref(x_325);
x_328 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_316, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_327);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec_ref(x_328);
x_331 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
x_332 = l_Lean_MessageData_ofExpr(x_326);
lean_ctor_set_tag(x_318, 7);
lean_ctor_set(x_318, 1, x_332);
lean_ctor_set(x_318, 0, x_331);
x_333 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_309, 7);
lean_ctor_set(x_309, 1, x_333);
lean_ctor_set(x_309, 0, x_318);
x_334 = l_Lean_MessageData_ofExpr(x_329);
lean_ctor_set_tag(x_308, 7);
lean_ctor_set(x_308, 1, x_334);
lean_ctor_set(x_308, 0, x_309);
x_335 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_336 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_336, 0, x_308);
lean_ctor_set(x_336, 1, x_335);
x_337 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_317, x_336, x_296, x_297, x_298, x_299, x_330);
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
lean_dec_ref(x_337);
x_243 = x_316;
x_244 = x_312;
x_245 = x_315;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_295;
x_251 = x_296;
x_252 = x_297;
x_253 = x_298;
x_254 = x_299;
x_255 = x_338;
goto block_290;
}
else
{
uint8_t x_339; 
lean_dec(x_326);
lean_free_object(x_318);
lean_free_object(x_309);
lean_dec(x_316);
lean_dec(x_315);
lean_free_object(x_308);
lean_dec(x_312);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
x_339 = !lean_is_exclusive(x_328);
if (x_339 == 0)
{
return x_328;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_328, 0);
x_341 = lean_ctor_get(x_328, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_328);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
else
{
uint8_t x_343; 
lean_free_object(x_318);
lean_free_object(x_309);
lean_dec(x_316);
lean_dec(x_315);
lean_free_object(x_308);
lean_dec(x_312);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
x_343 = !lean_is_exclusive(x_325);
if (x_343 == 0)
{
return x_325;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_325, 0);
x_345 = lean_ctor_get(x_325, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_325);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
return x_346;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_318, 1);
lean_inc(x_347);
lean_dec(x_318);
x_348 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_315, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_347);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec_ref(x_348);
x_351 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_316, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_350);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec_ref(x_351);
x_354 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
x_355 = l_Lean_MessageData_ofExpr(x_349);
x_356 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
x_357 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_309, 7);
lean_ctor_set(x_309, 1, x_357);
lean_ctor_set(x_309, 0, x_356);
x_358 = l_Lean_MessageData_ofExpr(x_352);
lean_ctor_set_tag(x_308, 7);
lean_ctor_set(x_308, 1, x_358);
lean_ctor_set(x_308, 0, x_309);
x_359 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_360 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_360, 0, x_308);
lean_ctor_set(x_360, 1, x_359);
x_361 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_317, x_360, x_296, x_297, x_298, x_299, x_353);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec_ref(x_361);
x_243 = x_316;
x_244 = x_312;
x_245 = x_315;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_295;
x_251 = x_296;
x_252 = x_297;
x_253 = x_298;
x_254 = x_299;
x_255 = x_362;
goto block_290;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_349);
lean_free_object(x_309);
lean_dec(x_316);
lean_dec(x_315);
lean_free_object(x_308);
lean_dec(x_312);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
x_363 = lean_ctor_get(x_351, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_351, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_365 = x_351;
} else {
 lean_dec_ref(x_351);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_free_object(x_309);
lean_dec(x_316);
lean_dec(x_315);
lean_free_object(x_308);
lean_dec(x_312);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
x_367 = lean_ctor_get(x_348, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_348, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_369 = x_348;
} else {
 lean_dec_ref(x_348);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(1, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_371 = lean_ctor_get(x_309, 0);
x_372 = lean_ctor_get(x_309, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_309);
x_373 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_374 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_373, x_298, x_310);
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_unbox(x_375);
lean_dec(x_375);
if (x_376 == 0)
{
lean_object* x_377; 
lean_free_object(x_308);
x_377 = lean_ctor_get(x_374, 1);
lean_inc(x_377);
lean_dec_ref(x_374);
x_243 = x_372;
x_244 = x_312;
x_245 = x_371;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_295;
x_251 = x_296;
x_252 = x_297;
x_253 = x_298;
x_254 = x_299;
x_255 = x_377;
goto block_290;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_374, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_379 = x_374;
} else {
 lean_dec_ref(x_374);
 x_379 = lean_box(0);
}
x_380 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_371, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_378);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec_ref(x_380);
x_383 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_372, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_382);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec_ref(x_383);
x_386 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
x_387 = l_Lean_MessageData_ofExpr(x_381);
if (lean_is_scalar(x_379)) {
 x_388 = lean_alloc_ctor(7, 2, 0);
} else {
 x_388 = x_379;
 lean_ctor_set_tag(x_388, 7);
}
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
x_389 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_390 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
x_391 = l_Lean_MessageData_ofExpr(x_384);
lean_ctor_set_tag(x_308, 7);
lean_ctor_set(x_308, 1, x_391);
lean_ctor_set(x_308, 0, x_390);
x_392 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_393 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_393, 0, x_308);
lean_ctor_set(x_393, 1, x_392);
x_394 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_373, x_393, x_296, x_297, x_298, x_299, x_385);
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec_ref(x_394);
x_243 = x_372;
x_244 = x_312;
x_245 = x_371;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_295;
x_251 = x_296;
x_252 = x_297;
x_253 = x_298;
x_254 = x_299;
x_255 = x_395;
goto block_290;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_381);
lean_dec(x_379);
lean_dec(x_372);
lean_dec(x_371);
lean_free_object(x_308);
lean_dec(x_312);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
x_396 = lean_ctor_get(x_383, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_383, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_398 = x_383;
} else {
 lean_dec_ref(x_383);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_379);
lean_dec(x_372);
lean_dec(x_371);
lean_free_object(x_308);
lean_dec(x_312);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
x_400 = lean_ctor_get(x_380, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_380, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_402 = x_380;
} else {
 lean_dec_ref(x_380);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(1, 2, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_401);
return x_403;
}
}
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; 
x_404 = lean_ctor_get(x_308, 0);
lean_inc(x_404);
lean_dec(x_308);
x_405 = lean_ctor_get(x_309, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_309, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_407 = x_309;
} else {
 lean_dec_ref(x_309);
 x_407 = lean_box(0);
}
x_408 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_409 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_408, x_298, x_310);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_unbox(x_410);
lean_dec(x_410);
if (x_411 == 0)
{
lean_object* x_412; 
lean_dec(x_407);
x_412 = lean_ctor_get(x_409, 1);
lean_inc(x_412);
lean_dec_ref(x_409);
x_243 = x_406;
x_244 = x_404;
x_245 = x_405;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_295;
x_251 = x_296;
x_252 = x_297;
x_253 = x_298;
x_254 = x_299;
x_255 = x_412;
goto block_290;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_409, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_414 = x_409;
} else {
 lean_dec_ref(x_409);
 x_414 = lean_box(0);
}
x_415 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_405, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_413);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec_ref(x_415);
x_418 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_406, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_417);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec_ref(x_418);
x_421 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
x_422 = l_Lean_MessageData_ofExpr(x_416);
if (lean_is_scalar(x_414)) {
 x_423 = lean_alloc_ctor(7, 2, 0);
} else {
 x_423 = x_414;
 lean_ctor_set_tag(x_423, 7);
}
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
x_424 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
if (lean_is_scalar(x_407)) {
 x_425 = lean_alloc_ctor(7, 2, 0);
} else {
 x_425 = x_407;
 lean_ctor_set_tag(x_425, 7);
}
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
x_426 = l_Lean_MessageData_ofExpr(x_419);
x_427 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
x_428 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_429 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
x_430 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_408, x_429, x_296, x_297, x_298, x_299, x_420);
x_431 = lean_ctor_get(x_430, 1);
lean_inc(x_431);
lean_dec_ref(x_430);
x_243 = x_406;
x_244 = x_404;
x_245 = x_405;
x_246 = x_291;
x_247 = x_292;
x_248 = x_293;
x_249 = x_294;
x_250 = x_295;
x_251 = x_296;
x_252 = x_297;
x_253 = x_298;
x_254 = x_299;
x_255 = x_431;
goto block_290;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_416);
lean_dec(x_414);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
x_432 = lean_ctor_get(x_418, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_418, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_434 = x_418;
} else {
 lean_dec_ref(x_418);
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
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_414);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
x_436 = lean_ctor_get(x_415, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_415, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_438 = x_415;
} else {
 lean_dec_ref(x_415);
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
}
}
else
{
uint8_t x_440; 
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
x_440 = !lean_is_exclusive(x_307);
if (x_440 == 0)
{
return x_307;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_307, 0);
x_442 = lean_ctor_get(x_307, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_307);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_444 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3;
x_445 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_444, x_298, x_303);
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_unbox(x_446);
lean_dec(x_446);
if (x_447 == 0)
{
lean_object* x_448; 
lean_dec(x_302);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
x_448 = lean_ctor_get(x_445, 1);
lean_inc(x_448);
lean_dec_ref(x_445);
x_12 = x_448;
goto block_15;
}
else
{
uint8_t x_449; 
x_449 = !lean_is_exclusive(x_445);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; 
x_450 = lean_ctor_get(x_445, 1);
x_451 = lean_ctor_get(x_445, 0);
lean_dec(x_451);
x_452 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_302, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_450);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
x_453 = !lean_is_exclusive(x_302);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; 
x_454 = lean_ctor_get(x_302, 1);
lean_dec(x_454);
x_455 = lean_ctor_get(x_302, 0);
lean_dec(x_455);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_456 = lean_ctor_get(x_452, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_452, 1);
lean_inc(x_457);
lean_dec_ref(x_452);
x_458 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_459 = l_Lean_MessageData_ofExpr(x_456);
lean_ctor_set_tag(x_445, 7);
lean_ctor_set(x_445, 1, x_459);
lean_ctor_set(x_445, 0, x_458);
lean_ctor_set_tag(x_302, 7);
lean_ctor_set(x_302, 1, x_458);
lean_ctor_set(x_302, 0, x_445);
x_460 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_444, x_302, x_296, x_297, x_298, x_299, x_457);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
x_461 = lean_ctor_get(x_460, 1);
lean_inc(x_461);
lean_dec_ref(x_460);
x_12 = x_461;
goto block_15;
}
else
{
uint8_t x_462; 
lean_free_object(x_302);
lean_free_object(x_445);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
x_462 = !lean_is_exclusive(x_452);
if (x_462 == 0)
{
return x_452;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_452, 0);
x_464 = lean_ctor_get(x_452, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_452);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set(x_465, 1, x_464);
return x_465;
}
}
}
else
{
lean_dec(x_302);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_452, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_452, 1);
lean_inc(x_467);
lean_dec_ref(x_452);
x_468 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_469 = l_Lean_MessageData_ofExpr(x_466);
lean_ctor_set_tag(x_445, 7);
lean_ctor_set(x_445, 1, x_469);
lean_ctor_set(x_445, 0, x_468);
x_470 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_470, 0, x_445);
lean_ctor_set(x_470, 1, x_468);
x_471 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_444, x_470, x_296, x_297, x_298, x_299, x_467);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
x_472 = lean_ctor_get(x_471, 1);
lean_inc(x_472);
lean_dec_ref(x_471);
x_12 = x_472;
goto block_15;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_free_object(x_445);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
x_473 = lean_ctor_get(x_452, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_452, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_475 = x_452;
} else {
 lean_dec_ref(x_452);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_473);
lean_ctor_set(x_476, 1, x_474);
return x_476;
}
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_445, 1);
lean_inc(x_477);
lean_dec(x_445);
x_478 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__4(x_302, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_477);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_479 = x_302;
} else {
 lean_dec_ref(x_302);
 x_479 = lean_box(0);
}
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_480 = lean_ctor_get(x_478, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_478, 1);
lean_inc(x_481);
lean_dec_ref(x_478);
x_482 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_483 = l_Lean_MessageData_ofExpr(x_480);
x_484 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
if (lean_is_scalar(x_479)) {
 x_485 = lean_alloc_ctor(7, 2, 0);
} else {
 x_485 = x_479;
 lean_ctor_set_tag(x_485, 7);
}
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_482);
x_486 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__6___redArg(x_444, x_485, x_296, x_297, x_298, x_299, x_481);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
lean_dec_ref(x_486);
x_12 = x_487;
goto block_15;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec(x_479);
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
x_488 = lean_ctor_get(x_478, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_478, 1);
lean_inc(x_489);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_490 = x_478;
} else {
 lean_dec_ref(x_478);
 x_490 = lean_box(0);
}
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(1, 2, 0);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_489);
return x_491;
}
}
}
}
}
else
{
uint8_t x_492; 
lean_dec(x_299);
lean_dec_ref(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
x_492 = !lean_is_exclusive(x_301);
if (x_492 == 0)
{
return x_301;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_301, 0);
x_494 = lean_ctor_get(x_301, 1);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_301);
x_495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_495, 0, x_493);
lean_ctor_set(x_495, 1, x_494);
return x_495;
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
x_39 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith_2431311409____hygCtx___hyg_34_(x_37, x_38);
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
x_49 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith_2431311409____hygCtx___hyg_34_(x_47, x_48);
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
